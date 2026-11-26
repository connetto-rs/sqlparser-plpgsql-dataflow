//! The paths the walk follows through tests, raises and loops, read through
//! a domain whose state is the outcomes of the tests each path took.
extern crate alloc;

use alloc::collections::BTreeSet;
use core::{cell::Cell, convert::Infallible};

use sqlparser::ast::{Query, Statement};
use sqlparser_expr_eval::Outcomes;
use sqlparser_plpgsql::{
    embedded::{Block, Node, NodeKind, embedded_sql},
    namespace::{FunctionKind, Name, Signature, Sql},
};
use sqlparser_plpgsql_dataflow::{
    Catalog, Domain, Ending, Escape, Flow, Return, Step, Test, Transactions, Write, walk,
};

/// A schema where no variable holds a row and no `CALL` reaches a procedure.
struct Scalars;

impl Catalog for Scalars {
    fn holds_row(&self, _name: &Name) -> bool {
        false
    }

    fn written_back(&mut self, _call: &Statement) -> Option<Vec<bool>> {
        None
    }
}

/// One path, as the outcome of every test it took.
type Path = BTreeSet<String>;

/// The paths reaching a point, each with the tests it took. A path taking
/// a test both ways is reached by none, and only a statement holding
/// `1 / 0` may raise.
struct Paths;

/// The expression a `SELECT` evaluating one expression evaluates.
fn expression(query: &Query) -> String {
    query.to_string().strip_prefix("SELECT ").unwrap().to_owned()
}

impl<'body> Domain<'body> for Paths {
    type State = BTreeSet<Path>;
    type Error = Infallible;

    fn entry(&mut self) -> Result<Self::State, Infallible> {
        Ok(BTreeSet::from([Path::new()]))
    }

    fn join(&self, into: &mut Self::State, from: &Self::State) {
        into.extend(from.iter().cloned());
    }

    fn widen(&self, head: &Self::State, mut next: Self::State, _round: usize) -> Self::State {
        next.extend(head.iter().cloned());
        next
    }

    fn write(
        &mut self,
        _: &Write<'body>,
        _: &Self::State,
        _: &mut Self::State,
    ) -> Result<(), Infallible> {
        Ok(())
    }

    fn assume(
        &mut self,
        test: Test<'body>,
        outcomes: Outcomes,
        state: Self::State,
    ) -> Result<Option<Self::State>, Infallible> {
        let test = match test {
            Test::Condition(condition) => expression(condition),
            Test::Match { subject, values } => {
                format!("{} IN ({})", expression(subject), expression(values))
            }
        };
        let (taken, refused) = match outcomes {
            Outcomes::TRUE => (format!("{test} true"), format!("{test} not true")),
            Outcomes::NOT_TRUE => (format!("{test} not true"), format!("{test} true")),
            other => panic!("the walk tests only for true or not true, not {other:?}"),
        };
        let paths: BTreeSet<Path> = state
            .into_iter()
            .filter(|path| !path.contains(&refused))
            .map(|mut path| {
                path.insert(taken.clone());
                path
            })
            .collect();
        Ok((!paths.is_empty()).then_some(paths))
    }

    fn may_raise(&mut self, step: Step<'body>, _: &Self::State) -> Result<bool, Infallible> {
        Ok(matches!(step, Step::Node(node)
            if matches!(&node.kind, NodeKind::Statement { statement, .. }
                | NodeKind::Perform { query: statement }
                if statement.to_string().contains("1 / 0"))))
    }
}

/// The function `run(p text, q integer)`.
fn run() -> Signature {
    Signature {
        name: "run".to_owned(),
        parameters: vec![Some("p".to_owned()), Some("q".to_owned())],
        kind: FunctionKind::Plain,
    }
}

/// Each path in `state`, its tests joined in order, or `unreachable`.
fn spelled(state: Option<&BTreeSet<Path>>) -> Vec<String> {
    state.map_or_else(
        || vec!["unreachable".to_owned()],
        |paths| {
            paths.iter().map(|path| path.iter().cloned().collect::<Vec<_>>().join(", ")).collect()
        },
    )
}

/// The paths reaching each `EXECUTE` of `block`, in the order written.
fn at_executes<'body>(block: &'body Block, flow: &Flow<'body, BTreeSet<Path>>) -> Vec<Vec<String>> {
    block
        .sites(&run(), |_| false)
        .unwrap()
        .iter()
        .filter(|site| matches!(site.sql, Sql::Dynamic(_)))
        .map(|site| spelled(flow.at(site.sql)))
        .collect()
}

/// The paths reaching each `EXECUTE` of `body`, run as a function.
fn paths(body: &str) -> Vec<Vec<String>> {
    let block = embedded_sql(body).unwrap();
    let flow =
        walk(&block, &run(), Transactions::Refused, Ending::Raises, &mut Scalars, &mut Paths)
            .unwrap();
    at_executes(&block, &flow)
}

/// An `IF` tries each condition on the paths where every earlier one was
/// false or null, and an `ELSE` runs where all were. Each condition is read
/// where the walk reaches it, before it narrows anything.
#[test]
fn an_if_tries_each_condition_where_the_earlier_ones_failed() {
    let block = embedded_sql(
        "BEGIN
          IF q > 1 THEN EXECUTE 'a';
          ELSIF q > 0 THEN EXECUTE 'b';
          ELSE EXECUTE 'c';
          END IF;
          EXECUTE 'd';
         END",
    )
    .unwrap();
    let flow =
        walk(&block, &run(), Transactions::Refused, Ending::Raises, &mut Scalars, &mut Paths)
            .unwrap();
    assert_eq!(
        at_executes(&block, &flow),
        [
            vec!["q > 1 true"],
            vec!["q > 0 true, q > 1 not true"],
            vec!["q > 0 not true, q > 1 not true"],
            vec!["q > 0 not true, q > 1 not true", "q > 0 true, q > 1 not true", "q > 1 true"],
        ]
    );
    let NodeKind::If(branches) = &block.statements[0].kind else { panic!("an IF") };
    let elsif = &branches.branches[1].condition;
    assert_eq!(spelled(flow.at(Sql::Expression(elsif))), ["q > 1 not true"]);
}

/// A branch no path takes is unreached, as is one where an earlier test of
/// the same condition settled it.
#[test]
fn a_branch_no_path_takes_is_unreached() {
    assert_eq!(
        paths(
            "BEGIN
              IF q > 0 THEN
               IF q > 0 THEN EXECUTE 'a'; ELSE EXECUTE 'b'; END IF;
              END IF;
             END"
        ),
        [vec!["q > 0 true"], vec!["unreachable"]]
    );
}

/// A `CASE` with a subject tests it against each `WHEN` list in turn, and
/// one without `ELSE` ends the paths no `WHEN` matched, which the walk
/// records for the `CASE`.
#[test]
fn a_case_without_else_records_the_paths_no_when_matched() {
    let block = embedded_sql(
        "BEGIN
          CASE p WHEN 'a' THEN EXECUTE 'a'; WHEN 'b', 'c' THEN EXECUTE 'b'; END CASE;
          EXECUTE 'after';
         END",
    )
    .unwrap();
    let flow =
        walk(&block, &run(), Transactions::Refused, Ending::Raises, &mut Scalars, &mut Paths)
            .unwrap();
    assert_eq!(
        at_executes(&block, &flow),
        [
            vec!["p IN ('a') true"],
            vec!["p IN ('a') not true, p IN ('b', 'c') true"],
            vec!["p IN ('a') not true, p IN ('b', 'c') true", "p IN ('a') true"],
        ]
    );
    let NodeKind::Case(case) = &block.statements[0].kind else { panic!("a CASE") };
    assert_eq!(spelled(flow.unmatched(case)), ["p IN ('a') not true, p IN ('b', 'c') not true"]);
}

/// A `WHILE` runs its body where its condition holds and leaves where it
/// does not, `EXIT WHEN` leaves where its condition holds, and `CONTINUE
/// WHEN` goes back to the head where its condition holds, so a later round
/// starts from the paths an earlier round took back.
#[test]
fn loops_split_their_paths_on_their_conditions() {
    assert_eq!(
        paths(
            "BEGIN
              WHILE q > 0 LOOP
               EXECUTE 'body';
               CONTINUE WHEN q > 1;
               EXIT WHEN q > 2;
               EXECUTE 'rest';
              END LOOP;
              EXECUTE 'after';
             END"
        ),
        [
            vec![
                "q > 0 true",
                "q > 0 true, q > 1 not true, q > 2 not true",
                "q > 0 true, q > 1 true",
            ],
            vec!["q > 0 true, q > 1 not true, q > 2 not true"],
            vec!["q > 0 not true", "q > 0 true, q > 1 not true, q > 2 true"],
        ]
    );
}

/// `ASSERT` continues where its condition holds and raises elsewhere, into
/// the handlers of its block.
#[test]
fn an_assert_continues_where_it_holds_and_raises_elsewhere() {
    assert_eq!(
        paths(
            "BEGIN
              BEGIN
               ASSERT q > 0;
               EXECUTE 'after';
              EXCEPTION WHEN assert_failure THEN
               EXECUTE 'handler';
              END;
             END"
        ),
        [vec!["q > 0 true"], vec!["q > 0 not true"]]
    );
}

/// A handler is reached from every point where its block may raise, and
/// from no other.
#[test]
fn a_handler_is_reached_only_from_where_a_raise_may_happen() {
    assert_eq!(
        paths(
            "BEGIN
              BEGIN
               PERFORM 1;
              EXCEPTION WHEN OTHERS THEN EXECUTE 'quiet';
              END;
              BEGIN
               IF q > 0 THEN PERFORM 1 / 0; END IF;
              EXCEPTION WHEN OTHERS THEN EXECUTE 'divided';
              END;
              BEGIN
               IF q > 1 THEN RAISE EXCEPTION 'stop'; END IF;
              EXCEPTION WHEN OTHERS THEN EXECUTE 'raised';
              END;
             END"
        ),
        [
            vec!["unreachable"],
            vec!["q > 0 true"],
            vec!["q > 0 not true, q > 1 true", "q > 0 true, q > 1 true"],
        ]
    );
}

/// The text of `node`, which `body` writes on one line.
fn written(body: &str, node: &Node) -> String {
    let (start, end) = (node.span.start, node.span.end);
    assert_eq!(start.line, end.line, "the step spans one line");
    let line = body.lines().nth(usize::try_from(start.line).unwrap() - 1).unwrap();
    let skipped = usize::try_from(start.column).unwrap() - 1;
    let taken = usize::try_from(end.column - start.column).unwrap();
    line.chars().skip(skipped).take(taken).collect()
}

/// How a test spells `step`, by its text in `body`.
fn step_text(body: &str, step: Step<'_>) -> String {
    match step {
        Step::Node(node) => written(body, node),
        Step::Declaration(declaration) => format!("DECLARE {}", declaration.name),
        Step::Iteration(_) => "a round".to_owned(),
    }
}

/// The points where `body`, run as `run` with the [`Transactions`] and
/// [`Ending`] given, returns, then those where an error leaves it, each
/// with the paths reaching it.
fn exits(body: &str, transactions: Transactions, ending: Ending) -> (Vec<String>, Vec<String>) {
    let block = embedded_sql(body).unwrap();
    let flow = walk(&block, &run(), transactions, ending, &mut Scalars, &mut Paths).unwrap();
    let from = |point: String, paths: &BTreeSet<Path>| {
        format!("{point} from {}", spelled(Some(paths)).join(" | "))
    };
    let returns = flow
        .returns()
        .map(|(at, paths)| {
            let point = match at {
                Return::Statement(node) => written(body, node),
                Return::End => "the end".to_owned(),
            };
            from(point, paths)
        })
        .collect();
    let escapes = flow
        .escapes()
        .map(|(at, paths)| {
            let point = match at {
                Escape::Raises(step) => format!("raises at {}", step_text(body, step)),
                Escape::MayRaise(step) => format!("may raise at {}", step_text(body, step)),
                Escape::End => "raises at the end".to_owned(),
            };
            from(point, paths)
        })
        .collect();
    (returns, escapes)
}

/// A body returns at each `RETURN`, and where control reaches the end of
/// its outer block, its handlers' ends included, the routine returns or
/// raises as its [`Ending`] tells.
#[test]
fn the_end_of_the_body_returns_or_raises_as_the_routine_ends() {
    let body = "BEGIN
          IF q > 0 THEN RETURN; END IF;
          IF q > 1 THEN RAISE EXCEPTION 'handled'; END IF;
         EXCEPTION WHEN OTHERS THEN EXECUTE 'handler';
         END";
    let returned = "RETURN; from q > 0 true";
    let end = "from q > 0 not true, q > 1 not true | q > 0 not true, q > 1 true";
    assert_eq!(
        exits(body, Transactions::Refused, Ending::Returns),
        (vec![returned.to_owned(), format!("the end {end}")], Vec::new())
    );
    assert_eq!(
        exits(body, Transactions::Refused, Ending::Raises),
        (vec![returned.to_owned()], vec![format!("raises at the end {end}")])
    );
}

/// A raise leaves the body where no enclosing handler surely catches what it
/// raises, and one only the domain says may happen leaves it too, since its
/// SQLSTATE is unknown.
#[test]
fn a_raise_no_handler_surely_catches_leaves_the_body() {
    let body = "BEGIN
          BEGIN
           RAISE EXCEPTION 'caught';
          EXCEPTION WHEN OTHERS THEN NULL;
          END;
          BEGIN
           IF q > 1 THEN RAISE division_by_zero; END IF;
           PERFORM 1 / 0;
          EXCEPTION WHEN division_by_zero THEN RAISE;
          END;
          ASSERT q > 2;
          CASE q WHEN 3 THEN RETURN; END CASE;
         END";
    assert_eq!(
        exits(body, Transactions::Refused, Ending::Returns),
        (
            vec!["RETURN; from q > 1 not true, q > 2 true, q IN (3) true".to_owned()],
            vec![
                "may raise at PERFORM 1 / 0; from q > 1 not true".to_owned(),
                "raises at RAISE; from q > 1 not true | q > 1 true".to_owned(),
                "raises at ASSERT q > 2; from q > 1 not true, q > 2 not true".to_owned(),
                "raises at CASE q WHEN 3 THEN RETURN; END CASE; from q > 1 not true, q > 2 true, \
                 q IN (3) not true"
                    .to_owned(),
            ]
        )
    );
}

/// Handlers catching `others`, `query_canceled` and `assert_failure` catch
/// every error, and `others` alone lets `assert_failure` and an error whose
/// SQLSTATE is unknown through.
#[test]
fn only_a_handler_catching_every_sqlstate_surely_catches_an_unknown_one() {
    let body = |conditions: &str| {
        format!(
            "BEGIN
              PERFORM 1 / 0;
              ASSERT q > 0;
             EXCEPTION WHEN {conditions} THEN NULL;
             END"
        )
    };
    let every = body("OTHERS OR query_canceled OR assert_failure");
    assert_eq!(exits(&every, Transactions::Refused, Ending::Returns).1, Vec::<String>::new());
    let others = body("OTHERS");
    assert_eq!(
        exits(&others, Transactions::Refused, Ending::Returns).1,
        ["may raise at PERFORM 1 / 0; from ", "raises at ASSERT q > 0; from q > 0 not true"]
    );
}

/// `EXIT` naming the function's own label leaves every block, its handlers
/// included, and raises `2F005` outside them, whatever the routine.
#[test]
fn an_exit_to_the_function_label_raises_outside_every_handler() {
    let body = "BEGIN
          LOOP
           EXIT run WHEN q > 0;
           COMMIT;
          END LOOP;
         EXCEPTION WHEN OTHERS THEN NULL;
         END";
    assert_eq!(
        exits(body, Transactions::Refused, Ending::Returns),
        (
            vec!["the end from q > 0 not true".to_owned()],
            vec!["raises at EXIT run WHEN q > 0; from q > 0 true".to_owned()]
        )
    );
}

/// A domain whose state counts the rounds a loop body ran, and whose
/// widening jumps to the top after three rounds.
struct Rounds {
    widened: Cell<usize>,
}

impl<'body> Domain<'body> for Rounds {
    type State = u32;
    type Error = Infallible;

    fn entry(&mut self) -> Result<u32, Infallible> {
        Ok(0)
    }

    fn join(&self, into: &mut u32, from: &u32) {
        *into = (*into).max(*from);
    }

    fn widen(&self, head: &u32, next: u32, round: usize) -> u32 {
        self.widened.set(self.widened.get() + 1);
        if round < 3 { next.max(*head) } else { u32::MAX }
    }

    fn write(&mut self, _: &Write<'body>, _: &u32, state: &mut u32) -> Result<(), Infallible> {
        *state = state.saturating_add(1);
        Ok(())
    }

    fn assume(
        &mut self,
        _: Test<'body>,
        _: Outcomes,
        state: u32,
    ) -> Result<Option<u32>, Infallible> {
        Ok(Some(state))
    }

    fn may_raise(&mut self, _: Step<'body>, _: &u32) -> Result<bool, Infallible> {
        Ok(false)
    }
}

/// A loop whose head grows every round stops once the widening settles it.
#[test]
fn widening_ends_a_loop_whose_head_keeps_growing() {
    let block = embedded_sql(
        "DECLARE i int := 0;
         BEGIN WHILE i < 10 LOOP i := i + 1; END LOOP; EXECUTE 'after'; END",
    )
    .unwrap();
    let mut domain = Rounds { widened: Cell::new(0) };
    let flow =
        walk(&block, &run(), Transactions::Refused, Ending::Raises, &mut Scalars, &mut domain)
            .unwrap();
    let sites = block.sites(&run(), |_| false).unwrap();
    let after = sites.iter().find(|site| matches!(site.sql, Sql::Dynamic(_))).unwrap();
    assert_eq!(flow.at(after.sql), Some(&u32::MAX));
    assert_eq!(domain.widened.get(), 5);
}
