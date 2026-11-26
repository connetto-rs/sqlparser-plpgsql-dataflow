//! What each variable may hold at each point of a body, as the guarantees
//! `sqlparser-expr-eval` carries through one expression.
//!
//! [`analyze`] walks a body with the [`Values`] domain. A write gives its
//! target the forward evaluation of its source, a test narrows the state to
//! what the backward evaluation of its condition implies, and a loop's head
//! forgets every variable whose guarantee keeps changing after a few rounds.
//! [`Analysis::truth_under`] then evaluates an expression under the
//! guarantees reaching a statement or expression.

use alloc::{borrow::Cow, boxed::Box, collections::BTreeMap, string::String, vec, vec::Vec};
use core::ops::ControlFlow;

use sqlparser::{
    ast::{
        BinaryOperator, DataType, ExactNumberInfo, Expr, Function, GroupByExpr, ObjectName, Query,
        Select, SelectItem, SetExpr, Statement, Value, ValueWithSpan, visit_expressions,
    },
    dialect::PostgreSqlDialect,
};
use sqlparser_expr_eval::{
    self as eval, Callee, CalleeKind, Evaluation, Guarantees, Interval, Outcomes,
    PostgreSqlOptions, QueryEvaluation, Resolved, ScalarType, Subject, TextRules, Unlisted,
    evaluate, implied, sql_values::postgres as pg,
};
use sqlparser_plpgsql::{
    embedded::{
        self, Block, Case, Declaration, DeclarationKind, DeclaredType, Loop, LoopControl, NodeKind,
    },
    namespace::{self, Name, NameKind, Signature, Sql},
};

use crate::{
    Catalog, Domain, Error, Flow, Found, Output, Part, Rows, Source, Step, Test, Transactions,
    Write,
    walk::{SiteKey, address, folded, stored_parts, walk, write_address},
};

/// How many rounds a loop's head joins what returns to it before it forgets
/// every variable whose guarantee still changes.
const JOINED_ROUNDS: usize = 3;

/// What a guarantee is about.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Reference<R> {
    /// A variable of the body, by its [`Name::id`], or the field of it at
    /// `fields`, each as PostgreSQL stores its name.
    Variable {
        /// The variable's [`Name::id`].
        id: usize,
        /// The field path, empty for the whole variable.
        fields: Vec<String>,
    },
    /// Something else a name resolves to, as the [`Context`] resolves it.
    Outer(R),
}

/// What the walk carries, the guarantees each variable satisfies.
pub type State<R> = Guarantees<Reference<R>>;

/// A state narrowed to where a `SELECT` returns its row, and whether it may
/// return none.
type Filtered<'state, R> = (Cow<'state, State<R>>, bool);

/// What only the catalog tells the [`Values`] domain, besides what
/// [`sqlparser_expr_eval::Context`] answers for calls, subqueries, types and
/// collations.
///
/// A name the body reaches as a variable resolves to
/// [`Reference::Variable`], which a custom plan binds as a constant. The
/// domain asks [`sqlparser_expr_eval::Context::reference`] and
/// [`sqlparser_expr_eval::Context::may_plan_as_constant`] only for the names
/// no variable answers, and keeps no guarantee about what it answers past the
/// expression reading it. The domain reads a `SELECT` reading no relation
/// itself, and the rows any other query returns into its targets come from
/// [`sqlparser_expr_eval::Context::query`], under the guarantees about those
/// outer references alone, since a context knows no variable.
pub trait Context: eval::Context {
    /// What `variable`, or its field at `fields`, may hold by its type
    /// alone, whatever the body assigned it.
    ///
    /// The domain answers itself for `FOUND`, `SQLSTATE`, `SQLERRM`, an
    /// integer loop's index, and the whole of a variable declared with a type
    /// named directly. An evaluation that may raise says reading may raise.
    /// The default answers any value of an unknown type, whose read raises
    /// only for a field, which a record not yet assigned refuses.
    ///
    /// # Errors
    ///
    /// Returns the context's error when it cannot tell.
    fn variable(&mut self, variable: &Name, fields: &[String]) -> Result<Evaluation, Self::Error> {
        let _ = variable;
        Ok(Evaluation::unknown(ScalarType::Unknown).with_error(!fields.is_empty()))
    }

    /// What a parameter, `$0` or trigger variable, or its field at `fields`,
    /// holds as the body starts, `None` when only its type tells.
    ///
    /// # Errors
    ///
    /// Returns the context's error when it cannot tell.
    fn entry(
        &mut self,
        variable: &Name,
        fields: &[String],
    ) -> Result<Option<Evaluation>, Self::Error> {
        let _ = (variable, fields);
        Ok(None)
    }
}

/// The variable a name reaches where the body reads it, and the field path
/// the parts after it name.
#[derive(Clone, Debug)]
struct Resolution {
    name: Name,
    fields: Vec<String>,
}

/// The variables the names written at one statement or expression reach, by
/// their parts as PostgreSQL stores them.
type Names = BTreeMap<Vec<String>, Resolution>;

/// The guarantees domain over `sqlparser-expr-eval`.
///
/// A state holds guarantees about variables alone. A guarantee about an
/// expression, or about what the context resolves, holds only while the
/// expression reading it runs, since the same text may name another variable
/// or column at another point.
pub struct Values<C: Context> {
    context: C,
    /// The names each statement and expression of the body reaches.
    names: BTreeMap<SiteKey, Names>,
    /// The variable each declaration declares, by its address.
    declared: BTreeMap<usize, Name>,
    /// The target each assignment writes, by its address, when it writes a
    /// variable or a field of one, no subscript.
    assigned: BTreeMap<usize, Resolution>,
    /// The parameters, trigger variables and `FOUND` the body reads, with
    /// their field paths.
    entries: BTreeMap<(usize, Vec<String>), Name>,
    /// What each variable and field may hold by its type alone.
    bases: BTreeMap<(usize, Vec<String>), Evaluation>,
    options: PostgreSqlOptions,
}

/// The walk over one body with the [`Values`] domain, and what it left.
pub struct Analysis<'body, C: Context> {
    flow: Flow<'body, State<C::Reference>>,
    values: Values<C>,
}

impl<'body, C: Context> Analysis<'body, C> {
    /// Whether a path reaches `sql`.
    #[must_use]
    pub fn reached(&self, sql: Sql<'body>) -> bool {
        self.flow.at(sql).is_some_and(|state| !state.is_impossible())
    }

    /// Whether a path reaches the end of `case`, a `CASE` without `ELSE`,
    /// with no `WHEN` matched, where PostgreSQL raises `case_not_found`.
    #[must_use]
    pub fn unmatched(&self, case: &'body Case) -> bool {
        self.flow.unmatched(case).is_some_and(|state| !state.is_impossible())
    }

    /// Whether control may leave `repeated` once a path enters it, `None`
    /// when no path reaches it, as [`Flow::left`] tells where control
    /// leaves a loop.
    #[must_use]
    pub fn ends(&self, repeated: &'body Loop) -> Option<bool> {
        self.flow.entered(repeated).filter(|state| !state.is_impossible())?;
        Some(self.flow.left(repeated).is_some_and(|state| !state.is_impossible()))
    }

    /// What `expression` evaluates to under the guarantees reaching `sql`,
    /// `None` when no path reaches it.
    ///
    /// The names `expression` writes resolve as they do in `sql`, which
    /// holds for every expression `sql` writes.
    ///
    /// # Errors
    ///
    /// Returns the context's error when a reference, a call or a subquery
    /// fails to resolve.
    pub fn truth_under(
        &mut self,
        sql: Sql<'body>,
        expression: &Expr,
    ) -> Result<Option<Evaluation>, C::Error> {
        let Some(state) = self.flow.at(sql).filter(|state| !state.is_impossible()) else {
            return Ok(None);
        };
        self.values.evaluate_at([Some(sql), None], expression, state).map(Some)
    }

    /// What `condition`, the condition of an `IF`, `ELSIF`, searched `CASE`,
    /// `WHILE`, `EXIT WHEN`, `CONTINUE WHEN` or `ASSERT`, evaluates to where
    /// the body reaches it, converted to `boolean` as PL/pgSQL converts it,
    /// `None` when no path reaches it.
    ///
    /// That answers whether it is always true, never true or always raising
    /// there.
    ///
    /// # Errors
    ///
    /// Returns the context's error when a reference, a call or a subquery
    /// fails to resolve.
    pub fn condition(&mut self, condition: &'body Query) -> Result<Option<Evaluation>, C::Error> {
        let Some(state) =
            self.flow.at(Sql::Expression(condition)).filter(|state| !state.is_impossible())
        else {
            return Ok(None);
        };
        self.values.condition(condition, state).map(|(evaluation, _)| Some(evaluation))
    }

    /// The context the analysis reads through, for binding what an
    /// expression passed to [`Analysis::truth_under`] names before reading
    /// it.
    ///
    /// What the context answered during the walk stays in the analysis, so
    /// a change to what it answers for the body's own names goes unseen.
    pub fn context_mut(&mut self) -> &mut C {
        &mut self.values.context
    }
}

/// Walks `block`, the body of the routine `signature` describes, with the
/// [`Values`] domain over `context`.
///
/// # Errors
///
/// Returns the errors [`walk`](crate::walk) returns, and the context's.
pub fn analyze<'body, C: Context, K: Catalog>(
    block: &'body Block,
    signature: &Signature,
    transactions: Transactions,
    catalog: &mut K,
    context: C,
) -> Result<Analysis<'body, C>, Error<C::Error>> {
    let mut values = Values::new(block, signature, &*catalog, context)?;
    let flow = walk(block, signature, transactions, catalog, &mut values)?;
    Ok(Analysis { flow, values })
}

impl<C: Context> Values<C> {
    /// The domain for `block`, the body of the routine `signature`
    /// describes, resolving its names with `catalog` and asking `context`
    /// what they hold.
    ///
    /// # Errors
    ///
    /// Returns the errors [`Block::sites`] returns.
    pub fn new<K: Catalog>(
        block: &Block,
        signature: &Signature,
        catalog: &K,
        context: C,
    ) -> Result<Self, Error<C::Error>> {
        let holds_row = |name: &Name| catalog.holds_row(name);
        let mut names = BTreeMap::new();
        let mut entries = BTreeMap::new();
        for site in block.sites(signature, holds_row)? {
            let mut table = Names::new();
            let mut resolve = |expression: &Expr| {
                if let Some(parts) = parts(expression)
                    && !table.contains_key(&parts)
                    && let Some((name, consumed)) = site.namespace.lookup(&parts, holds_row)
                {
                    let fields = parts[consumed..].to_vec();
                    if matches!(
                        name.kind(),
                        NameKind::Parameter { .. }
                            | NameKind::ReturnValue
                            | NameKind::Trigger(_)
                            | NameKind::Found
                    ) {
                        entries.insert((name.id(), fields.clone()), name.clone());
                    }
                    table.insert(parts, Resolution { name: name.clone(), fields });
                }
                ControlFlow::<()>::Continue(())
            };
            let _ = match site.sql {
                Sql::Statement(statement) => visit_expressions(statement, &mut resolve),
                Sql::Expression(query) => visit_expressions(query, &mut resolve),
                Sql::Dynamic(dynamic) => {
                    let _ = visit_expressions(&dynamic.command, &mut resolve);
                    visit_expressions(&dynamic.arguments, &mut resolve)
                }
            };
            names.insert(SiteKey::of(site.sql), table);
        }
        let mut declared = BTreeMap::new();
        let mut assigned = BTreeMap::new();
        for site in block.write_sites(signature, holds_row)? {
            match site.write {
                namespace::Write::Declaration(_) => {
                    declared.extend(site.declared.map(|name| (write_address(site.write), name)));
                }
                namespace::Write::Node(node) => {
                    // A target's indirection starts at its first subscript.
                    let NodeKind::Assignment(assignment) = &node.kind else { continue };
                    let parts = stored_parts(&assignment.target.name);
                    let resolution = site
                        .namespace
                        .lookup(&parts, holds_row)
                        .filter(|_| assignment.target.indirection.is_empty())
                        .map(|(name, consumed)| {
                            Resolution { name: name.clone(), fields: parts[consumed..].to_vec() }
                        });
                    if let Some(resolution) = resolution {
                        assigned.insert(address(node), resolution);
                    }
                }
            }
        }
        Ok(Self {
            context,
            names,
            declared,
            assigned,
            entries,
            bases: BTreeMap::new(),
            options: PostgreSqlOptions::default(),
        })
    }

    /// What `expression` evaluates to under `state`, its names resolved as
    /// at each of `sites`, the first answering first.
    fn evaluate_at(
        &mut self,
        sites: [Option<Sql<'_>>; 2],
        expression: &Expr,
        state: &State<C::Reference>,
    ) -> Result<Evaluation, C::Error> {
        let (mut scope, options) = self.scope(sites);
        evaluate(expression, &PostgreSqlDialect {}, options, &mut scope, state)
    }

    /// The forward evaluation of the expression `query` selects, read at
    /// its own site.
    fn evaluate_query(
        &mut self,
        query: &Query,
        state: &State<C::Reference>,
    ) -> Result<Evaluation, C::Error> {
        self.evaluate_at([Some(Sql::Expression(query)), None], &embedded::expression(query), state)
    }

    /// Whether evaluating the expression `query` selects may raise under
    /// `state`.
    fn may_raise_query(
        &mut self,
        query: &Query,
        state: &State<C::Reference>,
    ) -> Result<bool, C::Error> {
        Ok(self.evaluate_query(query, state)?.may_raise())
    }

    /// What the condition `query` selects evaluates to under `state`,
    /// converted to `boolean` as PL/pgSQL converts a condition, and whether
    /// it was `boolean` already.
    ///
    /// PL/pgSQL casts any other value through its text, so `'yes'` holds and
    /// `'maybe'` raises.
    fn condition(
        &mut self,
        query: &Query,
        state: &State<C::Reference>,
    ) -> Result<(Evaluation, bool), C::Error> {
        let value = self.evaluate_query(query, state)?;
        if *value.ty() == ScalarType::Boolean {
            return Ok((value, true));
        }
        let values = if value.values().is_empty() {
            eval::Values::none()
        } else {
            eval::Values::Unlisted(Unlisted::any())
        };
        let error = value.may_raise() || !value.values().is_empty();
        Ok((Evaluation::new(ScalarType::Boolean, value.may_be_null(), error, values), false))
    }

    /// Whether evaluating the condition `query` selects may raise under
    /// `state`.
    fn may_raise_condition(
        &mut self,
        query: &Query,
        state: &State<C::Reference>,
    ) -> Result<bool, C::Error> {
        Ok(self.condition(query, state)?.0.may_raise())
    }

    /// The scope resolving names as at each of `sites`, and the dialect's
    /// settings.
    fn scope(&mut self, sites: [Option<Sql<'_>>; 2]) -> (Scope<'_, C>, &PostgreSqlOptions) {
        let Self { context, names, bases, options, .. } = self;
        let names = sites.map(|site| site.and_then(|sql| names.get(&SiteKey::of(sql))));
        (Scope { context, names, bases }, options)
    }

    /// What `name`, or its field at `fields`, may hold by its type alone.
    fn base(&mut self, name: &Name, fields: &[String]) -> Result<Evaluation, C::Error> {
        base(&mut self.context, &mut self.bases, name, fields)
    }

    /// What the variable `name`, or its field at `fields`, holds once
    /// assigned `value`, and whether the assignment may raise.
    fn assign(
        &mut self,
        value: &Evaluation,
        name: &Name,
        fields: &[String],
    ) -> Result<(Evaluation, bool), C::Error> {
        let base = self.base(name, fields)?;
        let declared = if fields.is_empty() { declared_variable(name) } else { None };
        // PostgreSQL drops the length and precision written for a
        // parameter's type.
        let unmodified = match (name.kind(), declared) {
            (NameKind::Parameter { .. }, _) => fields.is_empty(),
            (_, Some(variable)) => {
                matches!(
                    &variable.data_type,
                    DeclaredType::Data(
                        DataType::Text
                            | DataType::Varchar(None)
                            | DataType::CharacterVarying(None)
                            | DataType::Numeric(ExactNumberInfo::None)
                            | DataType::Decimal(ExactNumberInfo::None)
                    )
                )
            }
            (_, None) => false,
        };
        let not_null = declared.is_some_and(|variable| variable.not_null);
        Ok(assigned(value, &base, unmodified, not_null))
    }

    /// What the write `write` gives its target, its value read where
    /// `inputs` holds, `None` when only the target's type tells.
    fn source(
        &mut self,
        write: &Write<'_>,
        fields: &[String],
        inputs: &State<C::Reference>,
    ) -> Result<Option<Evaluation>, C::Error> {
        let ty = self.base(&write.variable, fields)?.ty().clone();
        let value = match &write.source {
            Source::Null
            | Source::PortalReleased
            | Source::Query { rows: Rows::Empty, .. }
            | Source::Dynamic { rows: Rows::Empty, .. } => Evaluation::null(ty),
            Source::Value(query) => self.evaluate_query(query, inputs)?,
            Source::Query { statement: Statement::Query(query), output, rows } => {
                if let Some(select) = self.lone_row(query)? {
                    let Some(expression) = selected(select, *output) else {
                        return Ok(None);
                    };
                    let (kept, refused) = self.filtered(write.site, select, inputs)?;
                    let found = if kept.is_impossible() {
                        Evaluation::impossible(ty.clone())
                    } else {
                        self.evaluate_at([write.site, None], expression, &kept)?
                    };
                    // A missing row gives a target `NULL`, and `STRICT`
                    // raises instead.
                    if refused && *rows == (Rows::First { strict: false }) {
                        found.join(&Evaluation::null(ty))
                    } else {
                        found
                    }
                } else {
                    let evaluation = self.context.query(query, &outer(inputs))?;
                    match column(&evaluation, *output, *rows) {
                        Some(column) => column,
                        None => return Ok(None),
                    }
                }
            }
            Source::LoopIndex { lower, upper, .. } => {
                let lower = self.evaluate_query(lower, inputs)?;
                let upper = self.evaluate_query(upper, inputs)?;
                return Ok(Some(loop_index(&lower, &upper)));
            }
            Source::Found(found) => {
                let mut outcomes = Outcomes::TRUE.union(Outcomes::FALSE);
                if *found == Found::Rows
                    && let Some(site @ Sql::Statement(Statement::Query(query))) = write.site
                    && let Some(select) = self.lone_row(query)?
                {
                    let (kept, refused) = self.filtered(Some(site), select, inputs)?;
                    outcomes = Outcomes::NONE;
                    if !kept.is_impossible() {
                        outcomes = outcomes.union(Outcomes::TRUE);
                    }
                    if refused {
                        outcomes = outcomes.union(Outcomes::FALSE);
                    }
                }
                return Ok(Some(Evaluation::condition(outcomes, false)));
            }
            Source::CursorName
            | Source::PortalName
            | Source::Query { .. }
            | Source::Dynamic { .. }
            | Source::Cursor { .. }
            | Source::Call { .. }
            | Source::Diagnostics(_)
            | Source::ArrayElement { .. } => return Ok(None),
        };
        Ok(Some(self.assign(&value, &write.variable, fields)?.0))
    }

    /// The `SELECT` `query` writes, when it reads no relation, so that it
    /// returns one row, or with a `WHERE` one row where the `WHERE` holds
    /// and none elsewhere.
    ///
    /// A call reaching no known function, or one that may be an aggregate,
    /// a window or a set-returning function, may change how many rows come
    /// back.
    fn lone_row<'query>(
        &mut self,
        query: &'query Query,
    ) -> Result<Option<&'query Select>, C::Error> {
        let Query { with: None, body, limit_clause: None, fetch: None, pipe_operators, .. } = query
        else {
            return Ok(None);
        };
        let SetExpr::Select(select) = &**body else { return Ok(None) };
        let ungrouped = matches!(
            &select.group_by,
            GroupByExpr::Expressions(expressions, modifiers)
                if expressions.is_empty() && modifiers.is_empty()
        );
        let plain = pipe_operators.is_empty()
            && ungrouped
            && select.from.is_empty()
            && select.having.is_none()
            && select.qualify.is_none()
            && select.prewhere.is_none()
            && select.top.is_none()
            && select.projection.iter().all(|item| {
                matches!(item, SelectItem::UnnamedExpr(_) | SelectItem::ExprWithAlias { .. })
            });
        if !plain {
            return Ok(None);
        }
        let read = visit_expressions(&select.projection, |expression| {
            let Expr::Function(call) = expression else { return ControlFlow::Continue(()) };
            match self.context.callees(call) {
                Ok(callees)
                    if call.over.is_none()
                        && !callees.is_empty()
                        && callees.iter().all(|callee| {
                            callee.kind == CalleeKind::Normal && !callee.returns_set
                        }) =>
                {
                    ControlFlow::Continue(())
                }
                answer => ControlFlow::Break(answer.map(|_| ())),
            }
        });
        match read {
            ControlFlow::Continue(()) => Ok(Some(&**select)),
            ControlFlow::Break(answer) => answer.map(|()| None),
        }
    }

    /// `inputs` narrowed to where `select`, a [`Self::lone_row`], returns its
    /// row, and whether it may return none, its names resolved as at `site`.
    fn filtered<'state>(
        &mut self,
        site: Option<Sql<'_>>,
        select: &Select,
        inputs: &'state State<C::Reference>,
    ) -> Result<Filtered<'state, C::Reference>, C::Error> {
        let Some(filter) = &select.selection else { return Ok((Cow::Borrowed(inputs), false)) };
        let (mut scope, options) = self.scope([site, None]);
        let dialect = PostgreSqlDialect {};
        let outcomes = evaluate(filter, &dialect, options, &mut scope, inputs)?.outcomes();
        let kept = implied(filter, Outcomes::TRUE, &dialect, options, &mut scope, inputs)?;
        Ok((Cow::Owned(inputs.meet(&kept)), outcomes.falsity || outcomes.null))
    }

    /// Whether the test `case` makes of `subject` and of each `WHEN` may
    /// raise under `state`.
    fn may_raise_case(
        &mut self,
        case: &Case,
        state: &State<C::Reference>,
    ) -> Result<bool, C::Error> {
        for branch in &case.branches {
            let raises = match &case.subject {
                Some(subject) => {
                    match matched(subject, &branch.condition) {
                        Some(test) => {
                            let sites = [
                                Some(Sql::Expression(subject)),
                                Some(Sql::Expression(&branch.condition)),
                            ];
                            self.evaluate_at(sites, &test, state)?.may_raise()
                        }
                        None => true,
                    }
                }
                None => self.may_raise_condition(&branch.condition, state)?,
            };
            if raises {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Whether `declaration` may raise as its block starts under `state`.
    fn may_raise_declaration(
        &mut self,
        declaration: &Declaration,
        state: &State<C::Reference>,
    ) -> Result<bool, C::Error> {
        let DeclarationKind::Variable(variable) = &declaration.kind else {
            return Ok(false);
        };
        let Some(default) = &variable.default else {
            return Ok(variable.not_null);
        };
        let Some(name) = self.declared.get(&address(declaration)).cloned() else {
            return Ok(true);
        };
        let value = self.evaluate_query(default, state)?;
        Ok(self.assign(&value, &name, &[])?.1)
    }
}

impl<'body, C: Context> Domain<'body> for Values<C> {
    type State = State<C::Reference>;
    type Error = C::Error;

    fn entry(&mut self) -> Result<Self::State, C::Error> {
        let mut state = State::new();
        for ((id, fields), name) in &self.entries {
            let evaluation = match name.kind() {
                // PostgreSQL sets `FOUND` false as each call starts.
                NameKind::Found => {
                    fields.is_empty().then(|| Evaluation::condition(Outcomes::FALSE, false))
                }
                _ => self.context.entry(name, fields)?,
            };
            if let Some(evaluation) = evaluation {
                let reference = Reference::Variable { id: *id, fields: fields.clone() };
                state.restrict(Subject::Reference(reference), evaluation);
            }
        }
        Ok(state)
    }

    fn join(&self, into: &mut Self::State, from: &Self::State) {
        *into = into.join(from);
    }

    fn widen(&self, head: &Self::State, next: Self::State, round: usize) -> Self::State {
        let joined = head.join(&next);
        if round < JOINED_ROUNDS {
            return joined;
        }
        if round < 2 * JOINED_ROUNDS {
            let mut kept = joined.clone();
            kept.retain(|subject| head.get(subject) == joined.get(subject));
            return kept;
        }
        // Relations may narrow and widen by turns, so only unchanged single
        // guarantees stay.
        let mut kept = State::new();
        for (reference, evaluation) in joined.references() {
            if head.reference(reference) == Some(evaluation) {
                kept.restrict(Subject::Reference(reference.clone()), evaluation.clone());
            }
        }
        kept
    }

    fn write(
        &mut self,
        write: &Write<'body>,
        inputs: &Self::State,
        state: &mut Self::State,
    ) -> Result<(), C::Error> {
        let id = write.variable.id();
        let mut fields = Vec::new();
        let mut subscripted = false;
        for part in &write.part {
            match part {
                Part::Field(field) if !subscripted => fields.push(field.clone()),
                Part::Field(_) | Part::Index(_) | Part::Slice { .. } => subscripted = true,
            }
        }
        let mut written = state.clone();
        written.retain(|subject| {
            !matches!(
                subject,
                Subject::Reference(Reference::Variable { id: other, fields: path })
                    if *other == id && (path.starts_with(&fields) || fields.starts_with(path))
            )
        });
        if !subscripted && let Some(value) = self.source(write, &fields, inputs)? {
            written.restrict(Subject::Reference(Reference::Variable { id, fields }), value);
        }
        *state = if write.surely { written } else { state.join(&written) };
        Ok(())
    }

    fn assume(
        &mut self,
        test: Test<'body>,
        outcomes: Outcomes,
        state: Self::State,
    ) -> Result<Option<Self::State>, C::Error> {
        let (sites, expression) = match test {
            Test::Condition(condition) => {
                let (value, boolean) = self.condition(condition, &state)?;
                if value.outcomes().intersection(outcomes).is_empty() {
                    return Ok(None);
                }
                // A condition PL/pgSQL casts from another type implies nothing
                // of its operands.
                if !boolean {
                    return Ok(Some(state));
                }
                ([Some(Sql::Expression(condition)), None], embedded::expression(condition))
            }
            Test::Match { subject, values } => {
                match matched(subject, values) {
                    Some(test) => {
                        (
                            [Some(Sql::Expression(subject)), Some(Sql::Expression(values))],
                            Cow::Owned(test),
                        )
                    }
                    None => return Ok(Some(state)),
                }
            }
        };
        let (mut scope, options) = self.scope(sites);
        let implied =
            implied(&expression, outcomes, &PostgreSqlDialect {}, options, &mut scope, &state)?;
        let mut narrowed = state.meet(&implied);
        narrowed
            .retain(|subject| matches!(subject, Subject::Reference(Reference::Variable { .. })));
        Ok((!narrowed.is_impossible()).then_some(narrowed))
    }

    fn may_raise(&mut self, step: Step<'body>, state: &Self::State) -> Result<bool, C::Error> {
        match step {
            Step::Declaration(declaration) => self.may_raise_declaration(declaration, state),
            Step::Node(node) => {
                match &node.kind {
                    NodeKind::Assignment(assignment) => {
                        let Some(Resolution { name, fields }) =
                            self.assigned.get(&address(node)).cloned()
                        else {
                            return Ok(true);
                        };
                        let value = self.evaluate_query(&assignment.value, state)?;
                        Ok(self.assign(&value, &name, &fields)?.1)
                    }
                    NodeKind::If(choice) => {
                        for branch in &choice.branches {
                            if self.may_raise_condition(&branch.condition, state)? {
                                return Ok(true);
                            }
                        }
                        Ok(false)
                    }
                    NodeKind::Case(case) => {
                        if let Some(subject) = &case.subject
                            && self.may_raise_query(subject, state)?
                        {
                            return Ok(true);
                        }
                        self.may_raise_case(case, state)
                    }
                    NodeKind::Exit(exit) => {
                        match &exit.condition {
                            Some(condition) => self.may_raise_condition(condition, state),
                            None => Ok(false),
                        }
                    }
                    NodeKind::Assert(assert) => {
                        if self.may_raise_condition(&assert.condition, state)? {
                            return Ok(true);
                        }
                        match &assert.message {
                            Some(message) => self.may_raise_query(message, state),
                            None => Ok(false),
                        }
                    }
                    NodeKind::Block(_) | NodeKind::Return { value: None } => Ok(false),
                    NodeKind::Loop(repeated) => {
                        Ok(!matches!(
                            repeated.control,
                            LoopControl::Unconditional | LoopControl::While(_)
                        ))
                    }
                    _ => Ok(true),
                }
            }
            Step::Iteration(repeated) => {
                match &repeated.control {
                    LoopControl::Unconditional => Ok(false),
                    LoopControl::While(condition) => self.may_raise_condition(condition, state),
                    _ => Ok(true),
                }
            }
        }
    }
}

/// The context `sqlparser-expr-eval` reads one expression through, resolving
/// the body's names to its variables and asking the user's context for the
/// rest.
struct Scope<'run, C: Context> {
    context: &'run mut C,
    names: [Option<&'run Names>; 2],
    bases: &'run mut BTreeMap<(usize, Vec<String>), Evaluation>,
}

impl<C: Context> eval::Context for Scope<'_, C> {
    type Reference = Reference<C::Reference>;
    type Error = C::Error;

    fn reference(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<Resolved<Self::Reference>>, C::Error> {
        if let Some(parts) = parts(expression)
            && let Some(Resolution { name, fields }) =
                self.names.iter().flatten().find_map(|names| names.get(&parts))
        {
            let evaluation = base(self.context, self.bases, name, fields)?;
            let reference = Reference::Variable { id: name.id(), fields: fields.clone() };
            return Ok(Some(Resolved { reference, evaluation }));
        }
        Ok(self.context.reference(expression)?.map(|resolved| {
            Resolved {
                reference: Reference::Outer(resolved.reference),
                evaluation: resolved.evaluation,
            }
        }))
    }

    fn callees(&mut self, call: &Function) -> Result<Vec<Callee>, C::Error> {
        self.context.callees(call)
    }

    fn evaluate_body(
        &mut self,
        callee: &Callee,
        arguments: &[Evaluation],
    ) -> Result<Option<Evaluation>, C::Error> {
        self.context.evaluate_body(callee, arguments)
    }

    /// The user's context answers only an expression reading no name a
    /// variable of the body answers, since it knows no variable.
    fn expression(&mut self, expression: &Expr) -> Result<Option<Evaluation>, C::Error> {
        let names = self.names;
        let reads_variable = visit_expressions(expression, |inner| {
            match parts(inner) {
                Some(parts) if names.iter().flatten().any(|names| names.contains_key(&parts)) => {
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            }
        });
        if reads_variable.is_break() {
            return Ok(None);
        }
        self.context.expression(expression)
    }

    fn query(
        &mut self,
        query: &Query,
        guarantees: &Guarantees<Self::Reference>,
    ) -> Result<QueryEvaluation, C::Error> {
        self.context.query(query, &outer(guarantees))
    }

    fn data_type(&self, data_type: &DataType) -> ScalarType {
        self.context.data_type(data_type)
    }

    fn collation(&mut self, name: &ObjectName) -> Result<TextRules, C::Error> {
        self.context.collation(name)
    }

    /// PL/pgSQL binds every variable an embedded statement reads as a
    /// parameter, which a custom plan folds as a constant.
    fn may_plan_as_constant(&self, reference: &Self::Reference) -> bool {
        match reference {
            Reference::Variable { .. } => true,
            Reference::Outer(reference) => self.context.may_plan_as_constant(reference),
        }
    }
}

/// The guarantees of `state` about what the context resolves, the only
/// subjects the context knows.
fn outer<R: Clone + Ord>(state: &Guarantees<Reference<R>>) -> Guarantees<R> {
    let mut guarantees = Guarantees::new();
    for (reference, evaluation) in state.references() {
        if let Reference::Outer(reference) = reference {
            guarantees.restrict(Subject::Reference(reference.clone()), evaluation.clone());
        }
    }
    guarantees
}

/// The parts of `expression` as PostgreSQL stores them, when it is a name.
fn parts(expression: &Expr) -> Option<Vec<String>> {
    match expression {
        Expr::Identifier(ident) => Some(vec![folded(&ident.value, ident.quote_style.is_some())]),
        Expr::CompoundIdentifier(idents) => {
            Some(
                idents
                    .iter()
                    .map(|ident| folded(&ident.value, ident.quote_style.is_some()))
                    .collect(),
            )
        }
        Expr::Value(ValueWithSpan { value: Value::Placeholder(placeholder), .. }) => {
            Some(vec![placeholder.clone()])
        }
        _ => None,
    }
}

/// The variable declaration `name` reaches, when a `DECLARE` section binds
/// it as a variable.
fn declared_variable(name: &Name) -> Option<&embedded::Variable> {
    match name.kind() {
        NameKind::Declared { declaration, .. } => {
            match &declaration.kind {
                DeclarationKind::Variable(variable) => Some(variable),
                DeclarationKind::Alias(_) | DeclarationKind::Cursor(_) => None,
            }
        }
        _ => None,
    }
}

/// What `name`, or its field at `fields`, may hold by its type alone, asked
/// of `context` once.
fn base<C: Context>(
    context: &mut C,
    bases: &mut BTreeMap<(usize, Vec<String>), Evaluation>,
    name: &Name,
    fields: &[String],
) -> Result<Evaluation, C::Error> {
    let key = (name.id(), fields.to_vec());
    if let Some(known) = bases.get(&key) {
        return Ok(known.clone());
    }
    let own = |ty: ScalarType| Some(Evaluation::unknown(ty).with_error(false));
    let evaluation = match (name.kind(), fields) {
        (NameKind::Found, []) => own(ScalarType::Boolean),
        (NameKind::LoopIndex { .. }, []) => own(ScalarType::Integer(pg::IntegerType::Integer)),
        (NameKind::SqlState | NameKind::SqlErrm, []) => own(ScalarType::Text(TextRules::DEFAULT)),
        (NameKind::Declared { declaration, .. }, []) => {
            match &declaration.kind {
                DeclarationKind::Variable(variable) => {
                    match &variable.data_type {
                        DeclaredType::Data(data_type) => {
                            let mut ty = context.data_type(data_type);
                            if let (ScalarType::Text(_), Some(collation)) =
                                (&ty, &variable.collation)
                            {
                                ty = ScalarType::Text(context.collation(collation)?);
                            }
                            own(ty).map(|evaluation| evaluation.with_null(!variable.not_null))
                        }
                        DeclaredType::ColumnType { .. } | DeclaredType::RowType { .. } => None,
                    }
                }
                DeclarationKind::Cursor(_) => own(ScalarType::Other),
                DeclarationKind::Alias(_) => None,
            }
        }
        _ => None,
    };
    let evaluation = match evaluation {
        Some(evaluation) => evaluation,
        None => context.variable(name, fields)?,
    };
    let evaluation = within_type(evaluation);
    bases.insert(key, evaluation.clone());
    Ok(evaluation)
}

/// `evaluation` narrowed to the range its integer type admits.
fn within_type(evaluation: Evaluation) -> Evaluation {
    let Some((low, high)) = evaluation.ty().integer_bounds() else {
        return evaluation;
    };
    let mut range = Unlisted::any();
    range.numbers =
        Interval::point(pg::PgNumeric::from(low)).hull(&Interval::point(pg::PgNumeric::from(high)));
    let bounds =
        Evaluation::new(evaluation.ty().clone(), true, false, eval::Values::Unlisted(range));
    evaluation.meet(&bounds)
}

/// What a target whose type alone allows `base` holds once assigned
/// `value`, and whether the assignment may raise. `unmodified` tells
/// whether the target's type carries no length or precision, and
/// `not_null` whether its declaration forbids a null.
fn assigned(
    value: &Evaluation,
    base: &Evaluation,
    unmodified: bool,
    not_null: bool,
) -> (Evaluation, bool) {
    let target = base.ty();
    let (converted, mut raises) = if value.values().is_empty() {
        // A null, or no value at all, reads the same in any type.
        (value.clone().with_type(target.clone()), false)
    } else if keeps(value.ty(), target, unmodified) {
        let range = value.number_range();
        let narrowed = within_type(value.clone().with_type(target.clone()));
        let overflows = target.integer_bounds().is_some() && narrowed.number_range() != range;
        (narrowed, overflows)
    } else {
        (Evaluation::unknown(target.clone()).with_null(value.may_be_null()), true)
    };
    raises |= value.may_raise() || (not_null && value.may_be_null());
    (converted.with_error(false).meet(base), raises)
}

/// Whether assigning a value of type `source` to a target of type `target`
/// keeps every value the target's range admits. `unmodified` tells whether
/// the target's type carries no length, precision or scale, any of which
/// may round, pad or refuse a value, as `numeric(3, -1)` rounds 15 to 20.
fn keeps(source: &ScalarType, target: &ScalarType, unmodified: bool) -> bool {
    match (source, target) {
        (ScalarType::Integer(_), ScalarType::Integer(_))
        | (ScalarType::Boolean, ScalarType::Boolean)
        | (ScalarType::Date, ScalarType::Date) => true,
        (ScalarType::Integer(_) | ScalarType::Numeric, ScalarType::Numeric)
        | (ScalarType::Text(_) | ScalarType::UnknownLiteral, ScalarType::Text(_)) => unmodified,
        (ScalarType::Enum(left), ScalarType::Enum(right)) => left == right,
        _ => false,
    }
}

/// The part `output` of the rows `rows` of what `evaluation` returns, `None`
/// when it is a whole row or the columns are not enumerated.
fn column(evaluation: &QueryEvaluation, output: Output, rows: Rows) -> Option<Evaluation> {
    let Output::Ordinal(position) = output else { return None };
    let mut column = evaluation.columns.as_ref()?.get(position)?.clone();
    let returned = evaluation.rows.one || evaluation.rows.many;
    match rows {
        Rows::First { strict: false } if evaluation.rows.none => {
            column = if returned {
                column.with_null(true)
            } else {
                Evaluation::null(column.ty().clone())
            };
        }
        Rows::First { .. } | Rows::Each | Rows::Empty => {}
    }
    Some(column)
}

/// The integers a `FOR` loop's index takes between bounds evaluating to
/// `lower` and `upper`, which PostgreSQL refuses to be null.
fn loop_index(lower: &Evaluation, upper: &Evaluation) -> Evaluation {
    let ty = ScalarType::Integer(pg::IntegerType::Integer);
    let mut range = Unlisted::any();
    // A bound of another type is rounded, which may take the index past it.
    if matches!(lower.ty(), ScalarType::Integer(_)) && matches!(upper.ty(), ScalarType::Integer(_))
    {
        range.numbers = lower.number_range().hull(&upper.number_range());
    }
    within_type(Evaluation::new(ty, false, false, eval::Values::Unlisted(range)))
}

/// The expression `select` gives the column `output` names, `None` for a
/// whole row.
fn selected(select: &Select, output: Output) -> Option<&Expr> {
    let Output::Ordinal(position) = output else { return None };
    match select.projection.get(position)? {
        SelectItem::UnnamedExpr(expression)
        | SelectItem::ExprWithAlias { expr: expression, .. } => Some(expression),
        _ => None,
    }
}

/// The condition one `WHEN` of a `CASE` with a subject tests, that the
/// subject equals one of the values it lists, `None` when the `WHEN` is no
/// list of expressions.
fn matched(subject: &Query, values: &Query) -> Option<Expr> {
    let SetExpr::Select(select) = &*values.body else { return None };
    if !select.from.is_empty() || select.selection.is_some() {
        return None;
    }
    let subject = embedded::expression(subject).into_owned();
    select
        .projection
        .iter()
        .map(|item| {
            match item {
                SelectItem::UnnamedExpr(value) => {
                    Some(Expr::BinaryOp {
                        left: Box::new(subject.clone()),
                        op: BinaryOperator::Eq,
                        right: Box::new(value.clone()),
                    })
                }
                _ => None,
            }
        })
        .reduce(|left, right| {
            Some(Expr::BinaryOp {
                left: Box::new(left?),
                op: BinaryOperator::Or,
                right: Box::new(right?),
            })
        })
        .flatten()
}
