//! The walk over a body's control flow, generic over the [`Domain`] it
//! carries.

use alloc::{
    borrow::Cow,
    collections::{BTreeMap, btree_map::Entry},
    string::String,
    vec::Vec,
};
use core::fmt;

use sqlparser::ast::{
    Expr, Function, FunctionArg, FunctionArgExpr, FunctionArguments, ObjectName, ObjectNamePart,
    Query, Statement, Value,
};
use sqlparser_expr_eval::Outcomes;
use sqlparser_plpgsql::{
    embedded::{
        Assignment, Block, BoundCursor, Branch, Case, Declaration, DeclarationKind, Diagnostics,
        Exit, ExitKind, Handler, Indirection, IntoTargets, Loop, LoopControl, Node, NodeKind, Open,
        RaiseLevel, ReturnQuery, Target,
    },
    namespace::{self, Name, NameKind, Namespace, Signature, Sql, TriggerVariable, WriteSite},
};
use sqlstate::{SqlState, pg};

use crate::{Domain, Found, Output, Part, Rows, Source, Step, Test, Write, raise};

/// What only the catalog tells the walk about a body.
pub trait Catalog {
    /// Whether the parameter, declared variable or cursor parameter `name`
    /// holds a row, which its type decides.
    fn holds_row(&self, name: &Name) -> bool;

    /// Whether `call` writes back to each argument written in it, when it
    /// reaches one procedure, and `None` when it may reach none or several.
    fn written_back(&mut self, call: &Statement) -> Option<Vec<bool>>;
}

/// Whether `COMMIT` and `ROLLBACK` in a body may end the transaction and let
/// the body run on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Transactions {
    /// A function, or a procedure with a `SET` clause or `SECURITY DEFINER`,
    /// where they raise `invalid_transaction_termination`.
    Refused,
    /// A procedure with neither, which `CALL` may run outside a transaction
    /// block, where they run on unless a handler is in force.
    Controlled,
}

/// What control reaching the end of a body's outer block, past its handlers
/// too, does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Ending {
    /// The routine returns, as a procedure, a `DO` block, an event trigger
    /// function and a function with output parameters or returning `void`
    /// or a set do.
    Returns,
    /// The routine raises `2F005`, as any other function does, a trigger
    /// function among them.
    Raises,
}

/// A point where control returns from a body.
#[derive(Clone, Copy, Debug)]
pub enum Return<'body> {
    /// A `RETURN`, once it evaluates its value.
    Statement(&'body Node),
    /// The end of the outer block, past its handlers too, under
    /// [`Ending::Returns`].
    End,
}

/// A point where an error may leave a body, no handler around it surely
/// catching it.
///
/// A handler surely catches an error whose SQLSTATE is known without running
/// the step where one of its conditions names the SQLSTATE or its class, or
/// is `others` and the SQLSTATE is neither `query_canceled` nor
/// `assert_failure`. The handlers of a block catch any error where they name
/// `others`, `query_canceled` and `assert_failure` together.
#[derive(Clone, Copy, Debug)]
pub enum Escape<'body> {
    /// A step that surely raises. That is `RAISE EXCEPTION`, an `ASSERT`
    /// whose condition fails, a `CASE` without `ELSE` matching no `WHEN`,
    /// `COMMIT` or `ROLLBACK` where they may not end the transaction, and an
    /// `EXIT` naming the function's own label, which leaves every block and
    /// raises `2F005` outside them.
    Raises(Step<'body>),
    /// A step that may raise an error whose SQLSTATE only running it tells.
    /// That is a step [`Domain::may_raise`] answers `true` for, a step a
    /// raise may stop between two of the writes it makes, and `COMMIT` or
    /// `ROLLBACK` ending the transaction.
    MayRaise(Step<'body>),
    /// The end of the outer block, past its handlers too, under
    /// [`Ending::Raises`].
    End,
}

/// An error stopping the walk.
#[derive(Debug, thiserror::Error)]
pub enum Error<E> {
    /// The body names a variable PostgreSQL does not compile.
    #[error(transparent)]
    Namespace(#[from] namespace::Error),
    /// A write names a target that reaches no variable where it stands.
    #[error("'{name}' names no variable in reach where the body writes it")]
    UnresolvedTarget {
        /// The target, as written.
        name: String,
    },
    /// The domain stopped the walk.
    #[error("{0}")]
    Domain(E),
}

/// What the walk leaves at the statements, expressions and loops of a body,
/// and where control leaves the body.
#[derive(Clone, Debug)]
pub struct Flow<'body, S> {
    /// The join of the states reaching each statement and expression.
    points: BTreeMap<SiteKey, S>,
    /// The join of the states reaching the end of each `CASE` without `ELSE`
    /// with no `WHEN` matched, by the address of the `CASE`.
    unmatched: BTreeMap<usize, S>,
    /// The join of the states entering each loop, by its address.
    entered: BTreeMap<usize, S>,
    /// The join of the states control leaves each loop with, by its address.
    left: BTreeMap<usize, S>,
    /// The join of the states control returns with at each point.
    returns: Recorded<Return<'body>, S>,
    /// The join of the states an error leaves the body with at each point.
    escapes: Recorded<Escape<'body>, S>,
}

impl<'body, S> Flow<'body, S> {
    /// The join of the states the body reaches `sql` with, before any test
    /// it makes narrows them, `None` when no path reaches it.
    #[must_use]
    pub fn at(&self, sql: Sql<'body>) -> Option<&S> {
        self.points.get(&SiteKey::of(sql))
    }

    /// The join of the states reaching the end of `case`, a `CASE` without
    /// `ELSE`, with no `WHEN` matched, where PostgreSQL raises
    /// `case_not_found`, `None` when no path does.
    #[must_use]
    pub fn unmatched(&self, case: &'body Case) -> Option<&S> {
        self.unmatched.get(&address(case))
    }

    /// The join of the states a path enters `repeated` with, before its
    /// control runs, `None` when no path reaches it.
    #[must_use]
    pub fn entered(&self, repeated: &'body Loop) -> Option<&S> {
        self.entered.get(&address(repeated))
    }

    /// The join of the states control leaves `repeated` with, `None` when
    /// control never leaves it.
    ///
    /// Control leaves a loop when its condition is false or `NULL`, its
    /// range, rows or elements run out, an `EXIT` ends it, an `EXIT` or
    /// `CONTINUE` inside it reaches a block or loop around it, a `RETURN`
    /// inside it runs, or a step inside it surely raises an error no handler
    /// inside it surely catches, as [`Escape`] tells which steps surely raise
    /// and which handlers surely catch. A step that only may raise, as
    /// [`Domain::may_raise`] tells, leaves no loop.
    ///
    /// A path continuing the body after the loop carries the writes the loop
    /// makes as control leaves it, and a `RETURN` or a raise carries none.
    #[must_use]
    pub fn left(&self, repeated: &'body Loop) -> Option<&S> {
        self.left.get(&address(repeated))
    }

    /// Each point where control returns from the body, with the join of the
    /// states it returns with there, in the order the walk first reaches
    /// each.
    pub fn returns(&self) -> impl Iterator<Item = (Return<'body>, &S)> {
        self.returns.iter()
    }

    /// Each point where an error may leave the body, with the join of the
    /// states it leaves with there, in the order the walk first reaches
    /// each.
    pub fn escapes(&self) -> impl Iterator<Item = (Escape<'body>, &S)> {
        self.escapes.iter()
    }
}

/// A point of a body where the walk records the states reaching it.
trait Point: Copy {
    /// What tells the point apart from every other of its kind.
    fn key(self) -> (u8, usize);
}

impl Point for Return<'_> {
    fn key(self) -> (u8, usize) {
        match self {
            Self::Statement(node) => (0, address(node)),
            Self::End => (1, 0),
        }
    }
}

impl Point for Escape<'_> {
    fn key(self) -> (u8, usize) {
        let step = |first: u8, step: Step<'_>| {
            match step {
                Step::Declaration(declaration) => (first, address(declaration)),
                Step::Node(node) => (first + 1, address(node)),
                Step::Iteration(repeated) => (first + 2, address(repeated)),
            }
        };
        match self {
            Self::Raises(raising) => step(0, raising),
            Self::MayRaise(raising) => step(3, raising),
            Self::End => (6, 0),
        }
    }
}

/// The join of the states reaching each point of one kind, in the order the
/// walk first reaches each.
#[derive(Clone, Debug)]
struct Recorded<P, S> {
    points: Vec<(P, S)>,
    /// The position of each point in `points`, by its [`Point::key`].
    positions: BTreeMap<(u8, usize), usize>,
}

impl<P: Point, S> Recorded<P, S> {
    const fn new() -> Self {
        Self { points: Vec::new(), positions: BTreeMap::new() }
    }

    /// Adds `state` to what reaches `point`.
    fn add<'body, D>(&mut self, domain: &D, point: P, state: Cow<'_, S>)
    where
        D: Domain<'body, State = S>,
        S: Clone,
    {
        match self.positions.entry(point.key()) {
            Entry::Occupied(held) => domain.join(&mut self.points[*held.get()].1, &state),
            Entry::Vacant(vacant) => {
                vacant.insert(self.points.len());
                self.points.push((point, state.into_owned()));
            }
        }
    }

    fn iter(&self) -> impl Iterator<Item = (P, &S)> {
        self.points.iter().map(|(point, state)| (*point, state))
    }
}

/// Where a statement or expression sits in the body, by the kind of SQL and
/// its address.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct SiteKey(u8, usize);

impl SiteKey {
    pub(crate) fn of(sql: Sql<'_>) -> Self {
        match sql {
            Sql::Statement(statement) => Self(0, address(statement)),
            Sql::Expression(query) => Self(1, address(query)),
            Sql::Dynamic(dynamic) => Self(2, address(dynamic)),
        }
    }
}

/// The address of `value`, which identifies it in the body.
pub(crate) fn address<T>(value: &T) -> usize {
    core::ptr::from_ref(value).addr()
}

/// The address of the declaration or step a write stands at.
pub(crate) fn write_address(write: namespace::Write<'_>) -> usize {
    match write {
        namespace::Write::Declaration(declaration) => address(declaration),
        namespace::Write::Node(node) => address(node),
    }
}

/// Walks `block`, the body of the routine `signature` describes, carrying
/// `domain`'s states through its control flow, and gives the states reaching
/// each of its statements and expressions, entering and leaving each of its
/// loops, and returning from it or leaving it with an error. `ending` tells
/// what control reaching the end of the body does.
///
/// A block writes its declarations in order, then walks its statements, and
/// its handlers start from every point among its statements where a raise
/// may happen. `IF` and `CASE` try each condition where every earlier one
/// was false or `NULL`. A loop walks its statements until the state at its
/// head stops changing, each round's head passing through
/// [`Domain::widen`].
///
/// # Errors
///
/// Returns the errors [`Block::write_sites`] returns,
/// [`Error::UnresolvedTarget`] for a write whose target reaches no variable,
/// and the domain's errors.
pub fn walk<'body, D: Domain<'body>, C: Catalog>(
    block: &'body Block,
    signature: &Signature,
    transactions: Transactions,
    ending: Ending,
    catalog: &mut C,
    domain: &mut D,
) -> Result<Flow<'body, D::State>, Error<D::Error>> {
    let writes = block.write_sites(signature, |name| catalog.holds_row(name))?;
    // Every namespace answers the same `FOUND`. A body without SQL or
    // writes has no namespace, and no read of `FOUND` either.
    let found = match writes.first() {
        Some(site) => Some(site.namespace.found().clone()),
        None => {
            block
                .sites(signature, |name| catalog.holds_row(name))?
                .first()
                .map(|site| site.namespace.found().clone())
        }
    };
    let mut walk = Walk {
        catalog,
        domain,
        writes: writes.into_iter().map(|site| (write_address(site.write), site)).collect(),
        found,
        frames: Vec::new(),
        points: BTreeMap::new(),
        unmatched: BTreeMap::new(),
        entered: BTreeMap::new(),
        left: BTreeMap::new(),
        returns: Recorded::new(),
        escapes: Recorded::new(),
        transactions,
    };
    let entry = walk.domain.entry().map_err(Error::Domain)?;
    if let Some(end) = walk.block(block, entry)? {
        let domain = &*walk.domain;
        match ending {
            Ending::Returns => walk.returns.add(domain, Return::End, Cow::Owned(end)),
            Ending::Raises => walk.escapes.add(domain, Escape::End, Cow::Owned(end)),
        }
    }
    Ok(Flow {
        points: walk.points,
        unmatched: walk.unmatched,
        entered: walk.entered,
        left: walk.left,
        returns: walk.returns,
        escapes: walk.escapes,
    })
}

/// A variable a target reaches, and the part of it written.
struct Resolved<'body> {
    variable: Name,
    part: Vec<Part<'body>>,
    /// Whether the target is a whole variable holding a row, which a lone
    /// target of a query takes a whole row into.
    row: bool,
}

/// A block or loop enclosing the point the walk stands at.
struct Frame<'body, S> {
    label: Option<&'body str>,
    repeats: bool,
    /// The block's handlers, none for a loop.
    handlers: &'body [Handler],
    /// Whether the block's handlers catch what its statements raise, as they
    /// do while the walk is among those statements.
    catching: bool,
    /// What a raise the block's handlers may catch leaves.
    raised: Option<S>,
    /// What an `EXIT` leaving the block or loop leaves.
    exited: Option<S>,
    /// What a `CONTINUE` of the loop leaves.
    continued: Option<S>,
    /// What a loop writes as control leaves it, by `EXIT` and `CONTINUE`
    /// passing through it too.
    leaving: Vec<Write<'body>>,
    /// What control leaves the loop with, however it leaves.
    left: Option<S>,
}

impl<'body, S> Frame<'body, S> {
    const fn new(
        label: Option<&'body str>,
        repeats: bool,
        handlers: &'body [Handler],
        leaving: Vec<Write<'body>>,
    ) -> Self {
        Self {
            label,
            repeats,
            handlers,
            catching: false,
            raised: None,
            exited: None,
            continued: None,
            leaving,
            left: None,
        }
    }
}

/// The walk over one body.
struct Walk<'body, 'run, D: Domain<'body>, C> {
    catalog: &'run mut C,
    domain: &'run mut D,
    /// Every write, by the address of its declaration or step.
    writes: BTreeMap<usize, WriteSite<'body>>,
    /// The function's `FOUND`, unless the body holds no namespace.
    found: Option<Name>,
    frames: Vec<Frame<'body, D::State>>,
    points: BTreeMap<SiteKey, D::State>,
    unmatched: BTreeMap<usize, D::State>,
    entered: BTreeMap<usize, D::State>,
    left: BTreeMap<usize, D::State>,
    returns: Recorded<Return<'body>, D::State>,
    escapes: Recorded<Escape<'body>, D::State>,
    transactions: Transactions,
}

/// The result of one step of the walk, `None` where no path leaves it.
type Leaves<S, E> = Result<Option<S>, Error<E>>;

/// A pair of outcomes, as the paths a test holds on and the ones it fails on.
type Split<T> = (Option<T>, Option<T>);

/// The writes each round of a loop makes, and the ones a loop over no row
/// makes instead.
type Rounds<'body> = (Vec<Write<'body>>, Vec<Write<'body>>);

impl<'body, D: Domain<'body>, C: Catalog> Walk<'body, '_, D, C> {
    /// Adds `from` to `into`, either of which no path may reach.
    fn join(&self, into: &mut Option<D::State>, from: Option<&D::State>) {
        if let Some(from) = from {
            add(&*self.domain, into, from);
        }
    }

    /// Records `state` as reaching `sql`.
    fn evaluated(&mut self, sql: Sql<'body>, state: &D::State) {
        record(&*self.domain, &mut self.points, SiteKey::of(sql), Cow::Borrowed(state));
    }

    /// Records `state` as reaching each expression of `queries`.
    fn evaluated_all<'q: 'body>(
        &mut self,
        queries: impl IntoIterator<Item = &'q Query>,
        state: &D::State,
    ) {
        for query in queries {
            self.evaluated(Sql::Expression(query), state);
        }
    }

    /// Hands `state` to every enclosing block whose handlers may catch a
    /// raise there.
    fn handled(&mut self, state: &D::State) {
        let domain = &*self.domain;
        for frame in self.frames.iter_mut().filter(|frame| frame.catching) {
            add(domain, &mut frame.raised, state);
        }
    }

    /// Hands `state` to the enclosing handlers where `step` may raise an
    /// error whose SQLSTATE only running it tells, and records it as leaving
    /// the body unless a block around surely catches it.
    fn raised(&mut self, step: Step<'body>, state: &D::State) {
        self.handled(state);
        if !self.frames.iter().any(|frame| frame.catching && raise::caught(frame.handlers, None)) {
            self.escapes.add(&*self.domain, Escape::MayRaise(step), Cow::Borrowed(state));
        }
    }

    /// Hands `state` to the enclosing handlers where `step` surely raises,
    /// reporting `code`, `None` when only running it tells, and to every
    /// loop it leaves, out to the innermost block whose handlers surely
    /// catch it, or out of the body.
    fn raises(&mut self, step: Step<'body>, code: Option<SqlState>, state: &D::State) {
        self.handled(state);
        let caught = self
            .frames
            .iter()
            .rposition(|frame| frame.catching && raise::caught(frame.handlers, code));
        if caught.is_none() {
            self.escapes.add(&*self.domain, Escape::Raises(step), Cow::Borrowed(state));
        }
        self.escape(caught.map_or(0, |index| index + 1), state);
    }

    /// Hands `state` to every loop among the frames from `outer` on, which
    /// control leaves with it.
    fn escape(&mut self, outer: usize, state: &D::State) {
        let domain = &*self.domain;
        for frame in self.frames[outer..].iter_mut().filter(|frame| frame.repeats) {
            add(domain, &mut frame.left, state);
        }
    }

    /// Hands `state` to the enclosing handlers when the domain says `step`
    /// may raise there.
    fn may_raise(&mut self, step: Step<'body>, state: &D::State) -> Result<(), Error<D::Error>> {
        if self.domain.may_raise(step, state).map_err(Error::Domain)? {
            self.raised(step, state);
        }
        Ok(())
    }

    /// What remains of `state` where `test` takes one of `outcomes`.
    fn assume(
        &mut self,
        test: Test<'body>,
        outcomes: Outcomes,
        state: D::State,
    ) -> Leaves<D::State, D::Error> {
        self.domain.assume(test, outcomes, state).map_err(Error::Domain)
    }

    /// Applies every write `step` makes, `writes`, to `state`, each value
    /// read where `inputs` holds. A raise may stop the step between two
    /// writes, as assigning a value to the next target or `STRICT` finding
    /// no row may, so what each write but the last leaves goes to the
    /// enclosing handlers.
    fn write_all(
        &mut self,
        step: Step<'body>,
        writes: &[Write<'body>],
        inputs: &D::State,
        state: &mut D::State,
    ) -> Result<(), Error<D::Error>> {
        for (index, write) in writes.iter().enumerate() {
            if index > 0 {
                self.raised(step, state);
            }
            self.domain.write(write, inputs, state).map_err(Error::Domain)?;
        }
        Ok(())
    }

    /// Applies every write `step` makes, `writes`, to `state`, each value
    /// read where `state` holds before the first.
    fn write_from(
        &mut self,
        step: Step<'body>,
        writes: &[Write<'body>],
        state: &mut D::State,
    ) -> Result<(), Error<D::Error>> {
        let inputs = state.clone();
        self.write_all(step, writes, &inputs, state)
    }

    /// The names the targets of the write at `at` reach.
    fn write_site(
        &self,
        at: usize,
        name: &dyn fmt::Display,
    ) -> Result<&WriteSite<'body>, Error<D::Error>> {
        self.writes.get(&at).ok_or_else(|| unresolved(name))
    }

    /// The variable the name `parts` writes reaches in `namespace`, with the
    /// parts after it as fields.
    fn lookup(&self, namespace: &Namespace, parts: Vec<String>) -> Option<Resolved<'body>> {
        let catalog = &*self.catalog;
        let (name, consumed) = namespace.lookup(&parts, |name| catalog.holds_row(name))?;
        let part: Vec<_> = parts.into_iter().skip(consumed).map(Part::Field).collect();
        let row = part.is_empty() && holds_row(catalog, name);
        Some(Resolved { variable: name.clone(), part, row })
    }

    /// The variable `target` writes in `namespace`, and the part of it.
    fn target(
        &self,
        namespace: &Namespace,
        target: &'body Target,
    ) -> Result<Resolved<'body>, Error<D::Error>> {
        let mut resolved = self
            .lookup(namespace, stored_parts(&target.name))
            .ok_or_else(|| unresolved(&target.name))?;
        if !target.indirection.is_empty() {
            resolved.row = false;
        }
        resolved.part.extend(target.indirection.iter().map(|step| {
            match step {
                Indirection::Field(field) => {
                    Part::Field(folded(&field.value, field.quote_style.is_some()))
                }
                Indirection::Index(index) => Part::Index(index),
                Indirection::Slice { lower, upper } => {
                    Part::Slice { lower: lower.as_deref(), upper: upper.as_deref() }
                }
            }
        }));
        Ok(resolved)
    }

    /// The writes of `targets` by the step `node`, each taking the output
    /// `source` builds. A lone target holding a row takes the whole row, and
    /// with `whole` a lone target takes the whole value, as `FOREACH` assigns
    /// an element. Any other target takes the column at its position.
    fn targets(
        &self,
        node: &'body Node,
        targets: &'body [Target],
        whole: bool,
        site: Option<Sql<'body>>,
        source: impl Fn(Output) -> Source<'body>,
    ) -> Result<Vec<Write<'body>>, Error<D::Error>> {
        let namespace = &self.write_site(address(node), &"the targets")?.namespace;
        let resolved: Vec<_> = targets
            .iter()
            .map(|target| self.target(namespace, target))
            .collect::<Result<_, _>>()?;
        let lone = matches!(resolved.as_slice(), [target] if whole || target.row);
        Ok(resolved
            .into_iter()
            .enumerate()
            .map(|(position, Resolved { variable, part, .. })| {
                let output = if lone { Output::Row } else { Output::Ordinal(position) };
                Write {
                    at: namespace::Write::Node(node),
                    position,
                    variable,
                    part,
                    surely: true,
                    source: source(output),
                    site,
                }
            })
            .collect())
    }

    /// The cursor variable `cursor` names at the write of `node`.
    fn cursor(&self, node: &'body Node, cursor: &ObjectName) -> Result<Name, Error<D::Error>> {
        let namespace = &self.write_site(address(node), cursor)?.namespace;
        match self.lookup(namespace, stored_parts(cursor)) {
            Some(Resolved { variable, part, .. }) if part.is_empty() => Ok(variable),
            _ => Err(unresolved(cursor)),
        }
    }

    /// The write of `FOUND` by `node` at `position`, unless the body holds no
    /// namespace.
    fn found(
        &self,
        node: &'body Node,
        position: usize,
        found: Found,
        site: Option<Sql<'body>>,
    ) -> Option<Write<'body>> {
        Some(Write {
            at: namespace::Write::Node(node),
            position,
            variable: self.found.clone()?,
            part: Vec::new(),
            surely: true,
            source: Source::Found(found),
            site,
        })
    }

    /// Applies what each loop among `frames` writes as control leaves it to
    /// `state`, innermost first, and hands each loop what control leaves it
    /// with. These writes raise nothing.
    fn leave(
        &mut self,
        frames: core::ops::Range<usize>,
        state: &mut D::State,
    ) -> Result<(), Error<D::Error>> {
        for index in frames.rev() {
            let inputs = state.clone();
            for write in &self.frames[index].leaving {
                self.domain.write(write, &inputs, state).map_err(Error::Domain)?;
            }
            if self.frames[index].repeats {
                add(&*self.domain, &mut self.frames[index].left, state);
            }
        }
        Ok(())
    }

    /// Walks `nodes` from `state`.
    fn nodes(
        &mut self,
        nodes: &'body [Node],
        mut state: Option<D::State>,
    ) -> Leaves<D::State, D::Error> {
        for node in nodes {
            let Some(reached) = state else { return Ok(None) };
            state = self.node(node, reached)?;
        }
        Ok(state)
    }

    /// Walks `node` from `state`, giving what it leaves.
    fn node(&mut self, node: &'body Node, mut state: D::State) -> Leaves<D::State, D::Error> {
        let step = Step::Node(node);
        self.may_raise(step, &state)?;
        match &node.kind {
            NodeKind::Statement { statement, into } => {
                self.statement(node, statement, into.as_ref(), &mut state)?;
            }
            NodeKind::Perform { query } | NodeKind::ReturnQuery(ReturnQuery::Query(query)) => {
                let sql = Sql::Statement(query);
                self.evaluated(sql, &state);
                let found = self.found(node, 0, Found::Rows, Some(sql));
                self.write_from(step, found.as_slice(), &mut state)?;
            }
            NodeKind::Assignment(assignment) => self.assignment(node, assignment, &mut state)?,
            NodeKind::Dynamic { dynamic, into } => {
                let sql = Sql::Dynamic(dynamic);
                self.evaluated(sql, &state);
                if let Some(into) = into {
                    let rows = Rows::First { strict: into.strict };
                    let writes = self.targets(node, &into.targets, false, Some(sql), |output| {
                        Source::Dynamic { dynamic, output, rows }
                    })?;
                    self.write_from(step, &writes, &mut state)?;
                }
            }
            NodeKind::ReturnQuery(ReturnQuery::Dynamic(dynamic)) => {
                let sql = Sql::Dynamic(dynamic);
                self.evaluated(sql, &state);
                let found = self.found(node, 0, Found::Rows, Some(sql));
                self.write_from(step, found.as_slice(), &mut state)?;
            }
            NodeKind::Fetch(fetch) => {
                self.evaluated_all(fetch.direction.expression(), &state);
                let cursor = self.cursor(node, &fetch.cursor)?;
                let mut writes = self.targets(node, &fetch.targets, false, None, |output| {
                    Source::Cursor { cursor: cursor.clone(), output }
                })?;
                writes.extend(self.found(node, fetch.targets.len(), Found::Rows, None));
                self.write_from(step, &writes, &mut state)?;
            }
            NodeKind::Diagnostics(diagnostics) => {
                self.diagnostics(node, diagnostics, &mut state)?;
            }
            NodeKind::Move { direction, .. } => {
                self.evaluated_all(direction.expression(), &state);
                let found = self.found(node, 0, Found::Rows, None);
                self.write_from(step, found.as_slice(), &mut state)?;
            }
            NodeKind::Close { .. } => {}
            NodeKind::Commit { .. } | NodeKind::Rollback { .. } => {
                // A handler in force opens a subtransaction, which may not
                // commit.
                let catching = self.frames.iter().any(|frame| frame.catching);
                if self.transactions == Transactions::Refused || catching {
                    self.raises(step, Some(pg::INVALID_TRANSACTION_TERMINATION), &state);
                    return Ok(None);
                }
                self.raised(step, &state);
            }
            NodeKind::Open(open) => self.open(node, open, &mut state)?,
            NodeKind::Block(block) => return self.block(block, state),
            NodeKind::If(choice) => {
                let tests = choice
                    .branches
                    .iter()
                    .map(|branch| (branch, Test::Condition(&branch.condition)));
                let (end, unmatched) = self.branches(tests, state)?;
                let otherwise = self.nodes(&choice.otherwise, unmatched)?;
                return Ok(self.joined(end, otherwise.as_ref()));
            }
            NodeKind::Case(case) => return self.case(node, case, state),
            NodeKind::Loop(repeated) => return self.repeated(node, repeated, &state),
            NodeKind::Exit(exit) => return self.exit(node, exit, state),
            NodeKind::Return { value } => {
                self.evaluated_all(value.as_deref(), &state);
                self.escape(0, &state);
                self.returns.add(&*self.domain, Return::Statement(node), Cow::Owned(state));
                return Ok(None);
            }
            NodeKind::ReturnNext { value } => self.evaluated_all(value.as_deref(), &state),
            NodeKind::Raise(raise) => {
                let options = raise.options.iter().map(|option| &option.value);
                self.evaluated_all(raise.arguments.iter().chain(options), &state);
                if raise.level == RaiseLevel::Exception {
                    self.raises(step, raise::reported(raise), &state);
                    return Ok(None);
                }
            }
            NodeKind::Assert(assert) => {
                let condition = Test::Condition(&assert.condition);
                self.evaluated(Sql::Expression(&assert.condition), &state);
                let failed = self.assume(condition, Outcomes::NOT_TRUE, state.clone())?;
                if let Some(failed) = failed {
                    self.evaluated_all(assert.message.as_deref(), &failed);
                    self.raises(step, Some(pg::ASSERT_FAILURE), &failed);
                }
                return self.assume(condition, Outcomes::TRUE, state);
            }
        }
        Ok(Some(state))
    }

    /// Writes what `statement` by `node` gives `FOUND`, its `INTO` targets
    /// and the variables a `CALL` passes.
    fn statement(
        &mut self,
        node: &'body Node,
        statement: &'body Statement,
        into: Option<&'body IntoTargets>,
        state: &mut D::State,
    ) -> Result<(), Error<D::Error>> {
        let sql = Sql::Statement(statement);
        self.evaluated(sql, state);
        // Utility statements and `CALL` leave `FOUND` as it was.
        let counts = matches!(
            statement,
            Statement::Query(_)
                | Statement::Insert(_)
                | Statement::Update(_)
                | Statement::Delete(_)
                | Statement::Merge(_)
        );
        let mut writes = Vec::new();
        if counts {
            let targets = into.map_or(0, |into| into.targets.len());
            writes.extend(self.found(node, targets, Found::Rows, Some(sql)));
        }
        match into {
            Some(into) => {
                let rows = Rows::First { strict: into.strict };
                writes.extend(self.targets(node, &into.targets, false, Some(sql), |output| {
                    Source::Query { statement, output, rows }
                })?);
            }
            None if matches!(statement, Statement::Call(_)) => {
                writes.extend(self.call(node, statement)?);
            }
            None => {}
        }
        self.write_from(Step::Node(node), &writes, state)
    }

    /// `end` with `other` added.
    fn joined(&self, mut end: Option<D::State>, other: Option<&D::State>) -> Option<D::State> {
        self.join(&mut end, other);
        end
    }

    /// Writes the value `assignment` by `node` gives its target.
    fn assignment(
        &mut self,
        node: &'body Node,
        assignment: &'body Assignment,
        state: &mut D::State,
    ) -> Result<(), Error<D::Error>> {
        let subscripts = assignment.target.indirection.iter().flat_map(|step| {
            match step {
                Indirection::Field(_) => [None, None],
                Indirection::Index(index) => [Some(&**index), None],
                Indirection::Slice { lower, upper } => [lower.as_deref(), upper.as_deref()],
            }
            .into_iter()
            .flatten()
        });
        self.evaluated_all(subscripts, state);
        let value = &*assignment.value;
        self.evaluated(Sql::Expression(value), state);
        let namespace = &self.write_site(address(node), &assignment.target.name)?.namespace;
        let Resolved { variable, part, .. } = self.target(namespace, &assignment.target)?;
        let write = Write {
            at: namespace::Write::Node(node),
            position: 0,
            variable,
            part,
            surely: true,
            source: Source::Value(value),
            site: Some(Sql::Expression(value)),
        };
        self.write_from(Step::Node(node), core::slice::from_ref(&write), state)
    }

    /// Writes what `diagnostics` by `node` reads into its targets.
    fn diagnostics(
        &mut self,
        node: &'body Node,
        diagnostics: &'body Diagnostics,
        state: &mut D::State,
    ) -> Result<(), Error<D::Error>> {
        let namespace = &self.write_site(address(node), &"GET DIAGNOSTICS")?.namespace;
        let mut writes = Vec::with_capacity(diagnostics.items.len());
        for (position, item) in diagnostics.items.iter().enumerate() {
            let Resolved { variable, part, .. } = self.target(namespace, &item.target)?;
            writes.push(Write {
                at: namespace::Write::Node(node),
                position,
                variable,
                part,
                surely: true,
                source: Source::Diagnostics(item.kind),
                site: None,
            });
        }
        self.write_from(Step::Node(node), &writes, state)
    }

    /// Records `state` as reaching the SQL `open` by `node` runs, and writes
    /// the portal name it may give its cursor variable.
    fn open(
        &mut self,
        node: &'body Node,
        open: &'body Open,
        state: &mut D::State,
    ) -> Result<(), Error<D::Error>> {
        let variable = self.cursor(node, open.cursor())?;
        match open {
            Open::Bound(cursor) => self.opened(cursor, state),
            Open::Query { query, .. } => self.evaluated(Sql::Statement(query), state),
            Open::Dynamic { dynamic, .. } => self.evaluated(Sql::Dynamic(dynamic), state),
        }
        // A cursor variable already naming a portal keeps its name.
        let write = Write {
            at: namespace::Write::Node(node),
            position: 0,
            variable,
            part: Vec::new(),
            surely: false,
            source: Source::PortalName,
            site: None,
        };
        self.write_from(Step::Node(node), core::slice::from_ref(&write), state)
    }

    /// Records `state` as reaching the arguments and the query of `cursor` as
    /// it opens.
    fn opened(&mut self, cursor: &'body BoundCursor, state: &D::State) {
        self.evaluated_all(&cursor.arguments, state);
        self.evaluated(Sql::Statement(&cursor.query), state);
    }

    /// What the procedure `call` by `node` returns to each variable it passes.
    /// A call reaching one procedure surely writes the variables at its
    /// `INOUT` and `OUT` parameters, and any other call may write every
    /// variable it passes.
    fn call(
        &mut self,
        node: &'body Node,
        call: &'body Statement,
    ) -> Result<Vec<Write<'body>>, Error<D::Error>> {
        let written_back = self.catalog.written_back(call);
        let namespace = &self.write_site(address(node), call)?.namespace;
        let mut writes = Vec::new();
        for (argument, mut passed) in call_arguments(call) {
            let surely = match written_back.as_ref().and_then(|written| written.get(argument)) {
                Some(false) => continue,
                Some(true) => true,
                None => false,
            };
            // Parentheses and a cast to the variable's own type leave the
            // argument writable, and a cast to another type fails the call.
            while let Expr::Nested(inner) | Expr::Cast { expr: inner, .. } = passed {
                passed = inner;
            }
            let parts = match passed {
                Expr::Identifier(ident) => {
                    Vec::from([folded(&ident.value, ident.quote_style.is_some())])
                }
                Expr::CompoundIdentifier(idents) => {
                    idents
                        .iter()
                        .map(|ident| folded(&ident.value, ident.quote_style.is_some()))
                        .collect()
                }
                Expr::Value(value) => {
                    match &value.value {
                        Value::Placeholder(placeholder) => Vec::from([placeholder.clone()]),
                        _ => continue,
                    }
                }
                _ => continue,
            };
            let Some(Resolved { variable, part, .. }) = self.lookup(namespace, parts) else {
                continue;
            };
            writes.push(Write {
                at: namespace::Write::Node(node),
                position: argument,
                variable,
                part,
                surely,
                source: Source::Call { call, argument },
                site: Some(Sql::Statement(call)),
            });
        }
        Ok(writes)
    }

    /// Walks a block. Its declarations run before its handlers take effect,
    /// and each handler starts from what every raise among its statements
    /// leaves.
    fn block(&mut self, block: &'body Block, mut state: D::State) -> Leaves<D::State, D::Error> {
        self.frames.push(Frame::new(block.label.as_deref(), false, &block.handlers, Vec::new()));
        for declaration in &block.declarations {
            self.may_raise(Step::Declaration(declaration), &state)?;
            self.declaration(declaration, &mut state)?;
        }
        let index = self.frames.len() - 1;
        self.frames[index].catching = !block.handlers.is_empty();
        let mut end = self.nodes(&block.statements, Some(state))?;
        self.frames[index].catching = false;
        let raised = self.frames[index].raised.take();
        for handler in &block.handlers {
            let handled = self.nodes(&handler.statements, raised.clone())?;
            self.join(&mut end, handled.as_ref());
        }
        let exited = self.frames.pop().and_then(|frame| frame.exited);
        Ok(self.joined(end, exited.as_ref()))
    }

    /// Writes the value `declaration` gives its variable on entering its
    /// block.
    fn declaration(
        &mut self,
        declaration: &'body Declaration,
        state: &mut D::State,
    ) -> Result<(), Error<D::Error>> {
        let (source, site) = match &declaration.kind {
            DeclarationKind::Variable(declared) => {
                match declared.default.as_deref() {
                    Some(default) => {
                        self.evaluated(Sql::Expression(default), state);
                        (Source::Value(default), Some(Sql::Expression(default)))
                    }
                    None => (Source::Null, None),
                }
            }
            DeclarationKind::Cursor(_) => (Source::CursorName, None),
            // An alias declares no variable of its own, nor a write.
            DeclarationKind::Alias(_) => return Ok(()),
        };
        let at = address(declaration);
        let Some(variable) = self.write_site(at, &declaration.name)?.declared.clone() else {
            return Err(unresolved(&declaration.name));
        };
        let write = Write {
            at: namespace::Write::Declaration(declaration),
            position: 0,
            variable,
            part: Vec::new(),
            surely: true,
            source,
            site,
        };
        self.write_from(Step::Declaration(declaration), core::slice::from_ref(&write), state)
    }

    /// Walks each branch of `tests` where every earlier test failed, giving
    /// the join of what the branches leave and what reaches past the last
    /// test with none holding.
    fn branches(
        &mut self,
        tests: impl Iterator<Item = (&'body Branch, Test<'body>)>,
        state: D::State,
    ) -> Result<Split<D::State>, Error<D::Error>> {
        let mut end = None;
        let mut remaining = Some(state);
        for (branch, test) in tests {
            let Some(state) = remaining else { break };
            self.evaluated(Sql::Expression(&branch.condition), &state);
            let taken = self.assume(test, Outcomes::TRUE, state.clone())?;
            let taken = self.nodes(&branch.statements, taken)?;
            self.join(&mut end, taken.as_ref());
            remaining = self.assume(test, Outcomes::NOT_TRUE, state)?;
        }
        Ok((end, remaining))
    }

    /// Walks a `CASE`. A `CASE` with a subject tests the subject against
    /// each `WHEN`, and one without `ELSE` raises `case_not_found` where no
    /// `WHEN` holds.
    fn case(
        &mut self,
        node: &'body Node,
        case: &'body Case,
        state: D::State,
    ) -> Leaves<D::State, D::Error> {
        let subject = case.subject.as_deref();
        self.evaluated_all(subject, &state);
        let tests = case.branches.iter().map(|branch| {
            let test = match subject {
                Some(subject) => Test::Match { subject, values: &branch.condition },
                None => Test::Condition(&branch.condition),
            };
            (branch, test)
        });
        let (end, unmatched) = self.branches(tests, state)?;
        let fallen = if let Some(nodes) = &case.otherwise {
            self.nodes(nodes, unmatched)?
        } else {
            if let Some(unmatched) = unmatched {
                self.raises(Step::Node(node), Some(pg::CASE_NOT_FOUND), &unmatched);
                record(&*self.domain, &mut self.unmatched, address(case), Cow::Owned(unmatched));
            }
            None
        };
        Ok(self.joined(end, fallen.as_ref()))
    }

    /// Walks `EXIT` or `CONTINUE` at `node`, handing what transfers to the
    /// block or loop it reaches, which is the innermost carrying its label
    /// or the innermost loop without one. A label nothing carries is the
    /// function's, which leaves every block and loop and raises `2F005`.
    fn exit(
        &mut self,
        node: &'body Node,
        exit: &'body Exit,
        state: D::State,
    ) -> Leaves<D::State, D::Error> {
        let (transfers, falls) = match exit.condition.as_deref() {
            Some(condition) => {
                self.evaluated(Sql::Expression(condition), &state);
                let test = Test::Condition(condition);
                let falls = self.assume(test, Outcomes::NOT_TRUE, state.clone())?;
                (self.assume(test, Outcomes::TRUE, state)?, falls)
            }
            None => (Some(state), None),
        };
        let frame = match &exit.label {
            Some(label) => {
                self.frames.iter().rposition(|frame| frame.label == Some(label.as_str()))
            }
            None => self.frames.iter().rposition(|frame| frame.repeats),
        };
        let Some(mut transfers) = transfers else { return Ok(falls) };
        // A label nothing carries is the function's, so control leaves
        // every block and loop.
        let outer = frame.map_or(0, |index| index + 1);
        self.leave(outer..self.frames.len(), &mut transfers)?;
        let domain = &*self.domain;
        let Some(index) = frame else {
            self.escapes.add(domain, Escape::Raises(Step::Node(node)), Cow::Owned(transfers));
            return Ok(falls);
        };
        let frame = &mut self.frames[index];
        let into = match exit.kind {
            ExitKind::Exit => &mut frame.exited,
            ExitKind::Continue => &mut frame.continued,
        };
        match into {
            Some(into) => domain.join(into, &transfers),
            None => *into = Some(transfers),
        }
        Ok(falls)
    }

    /// Walks the loop `repeated` at `node` until the state at its head stops
    /// changing.
    fn repeated(
        &mut self,
        node: &'body Node,
        repeated: &'body Loop,
        entry: &D::State,
    ) -> Leaves<D::State, D::Error> {
        record(&*self.domain, &mut self.entered, address(repeated), Cow::Borrowed(entry));
        match &repeated.control {
            LoopControl::Unconditional | LoopControl::While(_) => {}
            LoopControl::Range { lower, upper, step, .. } => {
                let bounds = [&**lower, &**upper].into_iter().chain(step.as_deref());
                self.evaluated_all(bounds, entry);
            }
            LoopControl::Query { query, .. } => self.evaluated(Sql::Statement(query), entry),
            LoopControl::Cursor { cursor, .. } => self.opened(cursor, entry),
            LoopControl::Dynamic { dynamic, .. } => self.evaluated(Sql::Dynamic(dynamic), entry),
            LoopControl::Array { array, .. } => self.evaluated(Sql::Expression(array), entry),
        }
        let (each, nulls) = self.iterations(node, &repeated.control)?;
        // A loop over no row assigns its targets a null, from the state it
        // starts in, before any of its statements write.
        let empty = match &repeated.control {
            LoopControl::Query { .. } | LoopControl::Dynamic { .. } => {
                let mut empty = entry.clone();
                self.write_all(Step::Iteration(repeated), &nulls, entry, &mut empty)?;
                Some(empty)
            }
            _ => None,
        };
        // A `FOR` or `FOREACH` loop sets `FOUND` however control leaves it,
        // and a cursor `FOR` loop gives the cursor variable it named its
        // portal its null back.
        let mut leaving = Vec::new();
        if !matches!(repeated.control, LoopControl::Unconditional | LoopControl::While(_)) {
            leaving.extend(self.found(node, each.len(), Found::Iterated, None));
        }
        if let (LoopControl::Cursor { .. }, [_, portal]) = (&repeated.control, each.as_slice()) {
            leaving.push(Write { source: Source::PortalReleased, ..portal.clone() });
        }
        self.frames.push(Frame::new(repeated.label.as_deref(), true, &[], leaving));
        let mut head = entry.clone();
        let mut round = 0;
        let back = loop {
            let state = if let LoopControl::While(condition) = &repeated.control {
                self.evaluated(Sql::Expression(condition), &head);
                self.may_raise(Step::Iteration(repeated), &head)?;
                self.assume(Test::Condition(condition), Outcomes::TRUE, head.clone())?
            } else {
                self.may_raise(Step::Iteration(repeated), &head)?;
                let mut state = head.clone();
                self.write_all(Step::Iteration(repeated), &each, entry, &mut state)?;
                Some(state)
            };
            let mut back = self.nodes(&repeated.statements, state)?;
            // Each round hands its own `CONTINUE`s back to the head.
            let continued = self.frames.last_mut().and_then(|frame| frame.continued.take());
            self.join(&mut back, continued.as_ref());
            let mut next = entry.clone();
            if let Some(back) = &back {
                self.domain.join(&mut next, back);
            }
            let next = self.domain.widen(&head, next, round);
            if next == head {
                break back;
            }
            head = next;
            round += 1;
        };
        let exited = self.frames.last_mut().and_then(|frame| frame.exited.take());
        let exit = match &repeated.control {
            LoopControl::Unconditional => None,
            LoopControl::While(condition) => {
                self.assume(Test::Condition(condition), Outcomes::NOT_TRUE, head)?
            }
            LoopControl::Query { .. } | LoopControl::Dynamic { .. } => {
                self.joined(empty, back.as_ref())
            }
            LoopControl::Range { .. } | LoopControl::Cursor { .. } | LoopControl::Array { .. } => {
                Some(head)
            }
        };
        let mut exit = self.joined(exit, exited.as_ref());
        if let Some(state) = &mut exit {
            let index = self.frames.len() - 1;
            self.leave(index..index + 1, state)?;
        }
        if let Some(left) = self.frames.pop().and_then(|frame| frame.left) {
            record(&*self.domain, &mut self.left, address(repeated), Cow::Owned(left));
        }
        Ok(exit)
    }

    /// The writes each round of the loop at `node` makes, and the ones a loop
    /// over no row makes instead.
    fn iterations(
        &self,
        node: &'body Node,
        control: &'body LoopControl,
    ) -> Result<Rounds<'body>, Error<D::Error>> {
        let at = address(node);
        let declared = |variable: &str| -> Result<Name, Error<D::Error>> {
            self.write_site(at, &variable)?.declared.clone().ok_or_else(|| unresolved(&variable))
        };
        let write = |position, variable, source, site| {
            Write {
                at: namespace::Write::Node(node),
                position,
                variable,
                part: Vec::new(),
                surely: true,
                source,
                site,
            }
        };
        Ok(match control {
            LoopControl::Unconditional | LoopControl::While(_) => (Vec::new(), Vec::new()),
            LoopControl::Range { variable, reverse, lower, upper, step } => {
                let source =
                    Source::LoopIndex { reverse: *reverse, lower, upper, step: step.as_deref() };
                let index = write(0, declared(variable)?, source, Some(Sql::Expression(lower)));
                (Vec::from([index]), Vec::new())
            }
            LoopControl::Query { targets, query } => {
                let site = Some(Sql::Statement(query));
                let source = |rows| move |output| Source::Query { statement: query, output, rows };
                (
                    self.targets(node, targets, false, site, source(Rows::Each))?,
                    self.targets(node, targets, false, site, source(Rows::Empty))?,
                )
            }
            LoopControl::Cursor { variable, cursor } => {
                let query = &*cursor.query;
                let source =
                    Source::Query { statement: query, output: Output::Row, rows: Rows::Each };
                let row = write(0, declared(variable)?, source, Some(Sql::Statement(query)));
                // A cursor variable holding null names the portal the loop
                // opens until the loop ends, and keeps any other name.
                let portal = Write {
                    surely: false,
                    ..write(1, self.cursor(node, &cursor.name)?, Source::PortalName, None)
                };
                (Vec::from([row, portal]), Vec::new())
            }
            LoopControl::Dynamic { targets, dynamic } => {
                let site = Some(Sql::Dynamic(dynamic));
                let source = |rows| move |output| Source::Dynamic { dynamic, output, rows };
                (
                    self.targets(node, targets, false, site, source(Rows::Each))?,
                    self.targets(node, targets, false, site, source(Rows::Empty))?,
                )
            }
            LoopControl::Array { targets, slice, array } => {
                let site = Some(Sql::Expression(array));
                let source = |output| Source::ArrayElement { array, slice: *slice, output };
                (self.targets(node, targets, true, site, source)?, Vec::new())
            }
        })
    }
}

/// Adds `from` to `into`, which no path may reach.
fn add<'body, D: Domain<'body>>(domain: &D, into: &mut Option<D::State>, from: &D::State) {
    match into {
        Some(state) => domain.join(state, from),
        None => *into = Some(from.clone()),
    }
}

/// Adds `state` to what `map` holds at `key`.
fn record<'body, D: Domain<'body>, K: Ord>(
    domain: &D,
    map: &mut BTreeMap<K, D::State>,
    key: K,
    state: Cow<'_, D::State>,
) {
    match map.entry(key) {
        Entry::Occupied(mut held) => domain.join(held.get_mut(), &state),
        Entry::Vacant(vacant) => {
            vacant.insert(state.into_owned());
        }
    }
}

/// The error for a write naming `name`, which reaches no variable.
fn unresolved<E>(name: &dyn fmt::Display) -> Error<E> {
    Error::UnresolvedTarget { name: alloc::format!("{name}") }
}

/// The name an identifier written as `value` denotes, as PostgreSQL folds
/// it, keeping a quoted one as written and folding any other to ASCII lower
/// case.
pub(crate) fn folded(value: &str, quoted: bool) -> String {
    if quoted { value.into() } else { value.to_ascii_lowercase() }
}

/// The parts of `name` as PostgreSQL stores them. A part that is no
/// identifier stays empty, which no declaration matches.
pub(crate) fn stored_parts(name: &ObjectName) -> Vec<String> {
    name.0
        .iter()
        .map(|part| {
            ObjectNamePart::as_ident(part)
                .map(|ident| folded(&ident.value, ident.quote_style.is_some()))
                .unwrap_or_default()
        })
        .collect()
}

/// Whether the variable `name` holds a row, asking `catalog` for the
/// variables whose declared type decides.
fn holds_row(catalog: &impl Catalog, name: &Name) -> bool {
    match name.kind() {
        NameKind::LoopRecord { .. }
        | NameKind::Trigger(TriggerVariable::New | TriggerVariable::Old) => true,
        NameKind::Parameter { .. } | NameKind::CursorParameter { .. } => catalog.holds_row(name),
        NameKind::Declared { declaration, .. } => {
            matches!(declaration.kind, DeclarationKind::Variable(_)) && catalog.holds_row(name)
        }
        NameKind::ReturnValue
        | NameKind::Trigger(_)
        | NameKind::Found
        | NameKind::LoopIndex { .. }
        | NameKind::SqlState
        | NameKind::SqlErrm => false,
    }
}

/// The expressions `CALL` passes its procedure, each with its position
/// among the arguments written, from 0.
fn call_arguments(call: &Statement) -> impl Iterator<Item = (usize, &Expr)> {
    let arguments = match call {
        Statement::Call(Function { args: FunctionArguments::List(list), .. }) => {
            list.args.as_slice()
        }
        _ => &[],
    };
    arguments.iter().enumerate().filter_map(|(position, argument)| {
        match argument {
            FunctionArg::Unnamed(FunctionArgExpr::Expr(expression))
            | FunctionArg::Named { arg: FunctionArgExpr::Expr(expression), .. }
            | FunctionArg::ExprNamed { arg: FunctionArgExpr::Expr(expression), .. } => {
                Some((position, expression))
            }
            FunctionArg::Unnamed(_) | FunctionArg::Named { .. } | FunctionArg::ExprNamed { .. } => {
                None
            }
        }
    })
}
