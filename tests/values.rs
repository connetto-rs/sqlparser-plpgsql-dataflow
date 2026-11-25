//! What the value guarantees domain reads of conditions, each body run on
//! PostgreSQL 18 for the answer it expects.
use core::convert::Infallible;

use sqlparser::{
    ast::{Expr, Function, Query, Statement},
    dialect::PostgreSqlDialect,
    parser::Parser,
};
use sqlparser_expr_eval::{
    Callee, CalleeKind, Evaluation, NullInput, NullResult, Outcomes, Resolved, ScalarType,
    TextRules, Volatility, sql_values::postgres::IntegerType,
};
use sqlparser_plpgsql::{
    embedded::{Block, Node, NodeKind, embedded_sql},
    namespace::{FunctionKind, Name, NameKind, Signature, Sql},
};
use sqlparser_plpgsql_dataflow::{
    Catalog, Transactions,
    values::{self, Analysis, analyze},
};

/// A schema where only a variable declared `r` holds a row and no `CALL`
/// reaches a procedure.
struct Scalars;

impl Catalog for Scalars {
    fn holds_row(&self, name: &Name) -> bool {
        matches!(name.kind(), NameKind::Declared { declaration, .. } if declaration.name == "r")
    }

    fn written_back(&mut self, _call: &Statement) -> Option<Vec<bool>> {
        None
    }
}

/// The types of a routine's parameters, and `generate_series` as the one
/// function, returning a set of integers.
struct Parameters(Vec<ScalarType>);

impl sqlparser_expr_eval::Context for Parameters {
    type Reference = ();
    type Error = Infallible;

    fn reference(&mut self, _expression: &Expr) -> Result<Option<Resolved<()>>, Infallible> {
        Ok(None)
    }

    fn callees(&mut self, call: &Function) -> Result<Vec<Callee>, Infallible> {
        if call.name.to_string() != "generate_series" {
            return Ok(Vec::new());
        }
        let series = Callee::new(
            None,
            NullInput::Strict,
            NullResult::OnlyOnNullInput,
            Volatility::Immutable,
            CalleeKind::Normal,
            INTEGER,
            true,
            0,
        );
        Ok(vec![series])
    }
}

impl values::Context for Parameters {
    fn variable(&mut self, variable: &Name, fields: &[String]) -> Result<Evaluation, Infallible> {
        Ok(match variable.kind() {
            NameKind::Parameter { position } => {
                Evaluation::unknown(self.0[position - 1].clone()).with_error(false)
            }
            _ => Evaluation::unknown(ScalarType::Unknown).with_error(!fields.is_empty()),
        })
    }
}

const INTEGER: ScalarType = ScalarType::Integer(IntegerType::Integer);

/// A function with one parameter for each of `parameters`.
fn signature(parameters: &[&str]) -> Signature {
    Signature {
        name: "f".into(),
        parameters: parameters.iter().map(|name| Some((*name).into())).collect(),
        kind: FunctionKind::Plain,
    }
}

/// The walk over `block` with parameters `names` of types `types`.
fn analysis<'body, 'context>(
    block: &'body Block,
    names: &[&str],
    context: &'context mut Parameters,
) -> Analysis<'body, 'context, Parameters> {
    analyze(block, &signature(names), Transactions::Refused, &mut Scalars, context).unwrap()
}

/// The outcomes `condition` may take where the body reaches it.
fn outcomes<'body>(
    analysis: &mut Analysis<'body, '_, Parameters>,
    condition: &'body Query,
) -> Outcomes {
    let evaluation = analysis.condition(condition).unwrap();
    evaluation.expect("a path reaches the condition").outcomes()
}

/// The condition of the first branch of the `IF` `node` is.
fn if_condition(node: &Node) -> &Query {
    let NodeKind::If(choice) = &node.kind else { panic!("not an IF: {node:?}") };
    &choice.branches[0].condition
}

/// The value `node`, a `RETURN`, returns.
fn returned(node: &Node) -> &Query {
    let NodeKind::Return { value: Some(value) } = &node.kind else {
        panic!("not a RETURN with a value: {node:?}")
    };
    value
}

#[test]
fn a_default_decides_a_later_condition() {
    // PostgreSQL answers `then`.
    let block = embedded_sql(
        "DECLARE x int := 5; BEGIN IF x > 0 THEN RETURN 'then'; ELSE RETURN 'else'; END IF; END",
    )
    .unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    let condition = if_condition(&block.statements[0]);
    assert_eq!(outcomes(&mut analysis, condition), Outcomes::TRUE);
    let NodeKind::If(choice) = &block.statements[0].kind else { panic!("an IF") };
    assert!(!analysis.reached(Sql::Expression(returned(&choice.otherwise[0]))));
}

#[test]
fn a_branch_narrows_the_conditions_inside_it() {
    // PostgreSQL answers `null` for `NULL` and `other` for 5.
    let block = embedded_sql(
        "BEGIN IF n IS NULL THEN IF n > 3 THEN RETURN 'inner'; END IF; RETURN 'null'; END IF; \
         RETURN 'other'; END",
    )
    .unwrap();
    let mut context = Parameters(vec![INTEGER]);
    let mut analysis = analysis(&block, &["n"], &mut context);
    let NodeKind::If(outer) = &block.statements[0].kind else { panic!("an IF") };
    let inner = if_condition(&outer.branches[0].statements[0]);
    assert_eq!(outcomes(&mut analysis, inner), Outcomes::NULL);
    let NodeKind::If(nested) = &outer.branches[0].statements[0].kind else { panic!("an IF") };
    assert!(!analysis.reached(Sql::Expression(returned(&nested.branches[0].statements[0]))));
}

#[test]
fn a_case_without_else_reaches_its_end_unless_a_when_holds() {
    // PostgreSQL raises `case not found` for `'c'` and `NULL`, and answers
    // `second` for any argument once `p := 'b'` runs.
    let open =
        "BEGIN CASE p WHEN 'a' THEN RETURN 'first'; WHEN 'b' THEN RETURN 'second'; END CASE; END";
    let set = "BEGIN p := 'b'; \
               CASE p WHEN 'a' THEN RETURN 'first'; WHEN 'b' THEN RETURN 'second'; END CASE; END";
    for (body, index, unmatched) in [(open, 0, true), (set, 1, false)] {
        let block = embedded_sql(body).unwrap();
        let mut context = Parameters(vec![ScalarType::Text(TextRules::DEFAULT)]);
        let analysis = analysis(&block, &["p"], &mut context);
        let NodeKind::Case(case) = &block.statements[index].kind else { panic!("a CASE") };
        assert_eq!(analysis.unmatched(case), unmatched, "{body}");
        let first = Sql::Expression(returned(&case.branches[0].statements[0]));
        assert_eq!(analysis.reached(first), unmatched, "{body}");
    }
}

#[test]
fn a_handler_reads_the_values_written_before_the_raise() {
    // PostgreSQL answers 2.
    let block = embedded_sql(
        "DECLARE x int := 1; BEGIN BEGIN x := 2; PERFORM 1/0; \
         EXCEPTION WHEN division_by_zero THEN RETURN x; END; RETURN 0; END",
    )
    .unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    let NodeKind::Block(inner) = &block.statements[0].kind else { panic!("a block") };
    let value = returned(&inner.handlers[0].statements[0]);
    let evaluation = analysis.truth_under(Sql::Expression(value), &parsed("x = 2")).unwrap();
    assert_eq!(evaluation.unwrap().outcomes(), Outcomes::TRUE);
}

#[test]
fn a_loop_whose_head_keeps_changing_still_exits_where_its_condition_fails() {
    // PostgreSQL answers 10.
    let block = embedded_sql(
        "DECLARE i int := 0; BEGIN WHILE i < 10 LOOP i := i + 1; END LOOP; \
         IF i < 0 THEN RETURN 'negative'; END IF; RETURN i::text; END",
    )
    .unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    let negative = if_condition(&block.statements[1]);
    assert!(!outcomes(&mut analysis, negative).truth);
}

#[test]
fn an_assert_contradicting_its_branch_never_holds() {
    // PostgreSQL answers `passed` for -1 and fails the assertion for 1.
    let block =
        embedded_sql("BEGIN IF n > 0 THEN ASSERT n < 0; END IF; RETURN 'passed'; END").unwrap();
    let mut context = Parameters(vec![INTEGER]);
    let mut analysis = analysis(&block, &["n"], &mut context);
    let NodeKind::If(choice) = &block.statements[0].kind else { panic!("an IF") };
    let NodeKind::Assert(assert) = &choice.branches[0].statements[0].kind else {
        panic!("an ASSERT")
    };
    assert_eq!(outcomes(&mut analysis, &assert.condition), Outcomes::FALSE);
}

#[test]
fn found_starts_false() {
    // PostgreSQL answers `unset`.
    let block =
        embedded_sql("BEGIN IF NOT FOUND THEN RETURN 'unset'; END IF; RETURN 'set'; END").unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    assert_eq!(outcomes(&mut analysis, if_condition(&block.statements[0])), Outcomes::TRUE);
    assert!(!analysis.reached(Sql::Expression(returned(&block.statements[1]))));
}

#[test]
fn an_integer_loop_index_stays_within_its_bounds() {
    // PostgreSQL answers `within`.
    let block = embedded_sql(
        "BEGIN FOR i IN 1..3 LOOP IF i > 3 THEN RETURN 'past'; END IF; END LOOP; \
         RETURN 'within'; END",
    )
    .unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    let NodeKind::Loop(repeated) = &block.statements[0].kind else { panic!("a loop") };
    assert_eq!(outcomes(&mut analysis, if_condition(&repeated.statements[0])), Outcomes::FALSE);
}

#[test]
fn an_assignment_reads_the_value_its_target_type_stores() {
    // PostgreSQL answers `three`, rounding 2.5 into an integer.
    let block = embedded_sql(
        "DECLARE x int := 2.5; BEGIN IF x = 3 THEN RETURN 'three'; END IF; RETURN x::text; END",
    )
    .unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    assert!(outcomes(&mut analysis, if_condition(&block.statements[0])).truth);
}

#[test]
fn an_assignment_its_target_type_refuses_raises_into_the_handler() {
    // PostgreSQL answers `ab` and 1, keeping each value the refused
    // assignment would have replaced.
    let bodies = [
        "DECLARE x varchar(2) := 'ab'; \
         BEGIN BEGIN x := 'abc'; EXCEPTION WHEN OTHERS THEN RETURN x; END; RETURN 'none'; END",
        "DECLARE x smallint := 1; BEGIN BEGIN x := 40000; \
         EXCEPTION WHEN numeric_value_out_of_range THEN RETURN x; END; RETURN 'none'; END",
    ];
    for (body, kept) in bodies.into_iter().zip(["x = 'ab'", "x = 1"]) {
        let block = embedded_sql(body).unwrap();
        let mut context = Parameters(Vec::new());
        let mut analysis = analysis(&block, &[], &mut context);
        let NodeKind::Block(inner) = &block.statements[0].kind else { panic!("a block") };
        let value = Sql::Expression(returned(&inner.handlers[0].statements[0]));
        let evaluation = analysis.truth_under(value, &parsed(kept)).unwrap();
        assert!(evaluation.expect(body).outcomes().truth, "{body}");
    }
}

/// The outcomes of each of `expressions` where `body` reaches its last
/// statement, a `RETURN`.
fn at_return(body: &str, parameters: &[&str], expressions: &[&str]) -> Vec<Outcomes> {
    let block = embedded_sql(body).unwrap();
    let mut context = Parameters(vec![INTEGER; parameters.len()]);
    let mut analysis = analysis(&block, parameters, &mut context);
    let last = Sql::Expression(returned(block.statements.last().unwrap()));
    expressions
        .iter()
        .map(|expression| {
            let evaluation = analysis.truth_under(last, &parsed(expression)).unwrap();
            evaluation.expect("a path reaches the RETURN").outcomes()
        })
        .collect()
}

#[test]
fn a_select_reading_no_relation_assigns_its_one_row() {
    // PostgreSQL answers `2 3 4 true`.
    // The names an expression reads resolve as the `RETURN` writes them.
    let body = "DECLARE v int := 1; w int; x int; y int; \
                BEGIN SELECT v + 1 INTO w; SELECT 3, 4 INTO x, y; RETURN w || x || y || found; END";
    let read = at_return(body, &[], &["w = 2", "x = 3", "y = 4", "found"]);
    assert_eq!(read, [Outcomes::TRUE; 4]);
}

#[test]
fn a_select_whose_where_fails_assigns_null_or_raises_under_strict() {
    // PostgreSQL answers `null false` without `STRICT`, and raises
    // `no_data_found` with it, leaving `w` at 7.
    let lax = "DECLARE v int := 1; w int := 7; \
               BEGIN SELECT v INTO w WHERE v > 5; RETURN w || found; END";
    assert_eq!(at_return(lax, &[], &["w IS NULL", "found"]), [Outcomes::TRUE, Outcomes::FALSE]);
    let block = embedded_sql(
        "DECLARE v int := 1; w int := 7; BEGIN BEGIN SELECT v INTO STRICT w WHERE v > 5; \
         RETURN 'found'; EXCEPTION WHEN no_data_found THEN RETURN w; END; END",
    )
    .unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    let NodeKind::Block(inner) = &block.statements[0].kind else { panic!("a block") };
    assert!(!analysis.reached(Sql::Expression(returned(&inner.statements[1]))));
    let handled = Sql::Expression(returned(&inner.handlers[0].statements[0]));
    let kept = analysis.truth_under(handled, &parsed("w = 7")).unwrap();
    assert_eq!(kept.expect("the handler is reached").outcomes(), Outcomes::TRUE);
}

#[test]
fn a_select_assigns_only_where_its_where_holds() {
    // PostgreSQL answers `null` for -1 and 3 for 3, never `nonpositive`.
    let body = "DECLARE w int; BEGIN SELECT n INTO w WHERE n > 0; \
                IF w <= 0 THEN RETURN 'nonpositive'; END IF; RETURN w; END";
    let block = embedded_sql(body).unwrap();
    let mut context = Parameters(vec![INTEGER]);
    let mut analysis = analysis(&block, &["n"], &mut context);
    assert!(!outcomes(&mut analysis, if_condition(&block.statements[1])).truth);
}

#[test]
fn a_set_returning_select_may_assign_no_row() {
    // PostgreSQL answers `not found`.
    let block = embedded_sql(
        "DECLARE x int := 5; BEGIN SELECT generate_series(1, 0) INTO x; \
         IF FOUND THEN RETURN 'found'; END IF; RETURN 'not found'; END",
    )
    .unwrap();
    let mut context = Parameters(Vec::new());
    let analysis = analysis(&block, &[], &mut context);
    assert!(analysis.reached(Sql::Expression(returned(&block.statements[2]))));
}

/// The outcomes of `kept` where the first handler of the block `body` opens
/// with returns.
fn handled(body: &str, kept: &str) -> Outcomes {
    let block = embedded_sql(body).unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    let NodeKind::Block(inner) = &block.statements[0].kind else { panic!("a block") };
    let value = Sql::Expression(returned(&inner.handlers[0].statements[0]));
    let evaluation = analysis.truth_under(value, &parsed(kept)).unwrap();
    evaluation.expect("the handler is reached").outcomes()
}

#[test]
fn a_condition_of_another_type_is_cast_to_boolean() {
    // PostgreSQL answers `then` for `'yes'`, and raises for `'maybe'`
    // before the branch assigns 3, so the handler returns 2.
    let block = embedded_sql(
        "DECLARE x text := 'yes'; BEGIN IF x THEN RETURN 'then'; END IF; RETURN 'else'; END",
    )
    .unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    assert!(outcomes(&mut analysis, if_condition(&block.statements[0])).truth);
    let NodeKind::If(choice) = &block.statements[0].kind else { panic!("an IF") };
    assert!(analysis.reached(Sql::Expression(returned(&choice.branches[0].statements[0]))));
    let raised = "DECLARE x text := 'maybe'; y int := 1; BEGIN BEGIN y := 2; \
                  IF x THEN y := 3; ELSE y := 3; END IF; y := 4; RETURN 0; \
                  EXCEPTION WHEN invalid_text_representation THEN RETURN y; END; END";
    assert!(handled(raised, "y = 2").truth);
}

#[test]
fn a_field_of_a_record_not_yet_assigned_raises() {
    // PostgreSQL raises 55000 reading `r.f`, so the handler returns 2.
    let body = "DECLARE r record; y int := 1; BEGIN BEGIN y := 2; \
                IF r.f IS NULL THEN y := 3; ELSE y := 3; END IF; y := 4; RETURN 0; \
                EXCEPTION WHEN OTHERS THEN RETURN y; END; END";
    assert!(handled(body, "y = 2").truth);
}

#[test]
fn widening_keeps_what_a_loop_never_changes() {
    // PostgreSQL answers `five`.
    let block = embedded_sql(
        "DECLARE c int := 5; i int := 0; a int := 0; b int := 0; \
         BEGIN LOOP IF a = 1 THEN b := 1; END IF; IF i > 1000 THEN a := 1; END IF; \
         i := i + 1; EXIT WHEN i > 5; END LOOP; \
         IF c = 5 THEN RETURN 'five'; END IF; RETURN 'other'; END",
    )
    .unwrap();
    let mut context = Parameters(Vec::new());
    let mut analysis = analysis(&block, &[], &mut context);
    assert_eq!(outcomes(&mut analysis, if_condition(&block.statements[1])), Outcomes::TRUE);
}

/// `text` parsed as one PostgreSQL expression.
fn parsed(text: &str) -> Expr {
    Parser::new(&PostgreSqlDialect {}).try_with_sql(text).unwrap().parse_expr().unwrap()
}
