//! What the value guarantees domain reads of conditions, each body run on
//! PostgreSQL 18 for the answer it expects.
use core::convert::Infallible;

use sqlparser::{
    ast::{Expr, Function, Query, Statement},
    dialect::PostgreSqlDialect,
    parser::Parser,
};
use sqlparser_expr_eval::{
    Callee, CalleeKind, Evaluation, Guarantees, NullInput, NullResult, Outcomes, QueryEvaluation,
    Resolved, Rows, ScalarType, TextRules, Volatility,
    sql_values::postgres::{IntegerType, PgValue},
};
use sqlparser_plpgsql::{
    embedded::{Block, Loop, Node, NodeKind, embedded_sql},
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

/// The types of a routine's parameters, `generate_series` returning a set
/// of integers, `abs` returning one, `limit_value` naming the integer 3
/// outside the body, and the tables `one_row`, holding one row whose `k` is
/// 4, and `no_row`, holding none.
struct Parameters(Vec<ScalarType>);

impl sqlparser_expr_eval::Context for Parameters {
    type Reference = ();
    type Error = Infallible;

    fn reference(&mut self, expression: &Expr) -> Result<Option<Resolved<()>>, Infallible> {
        let Expr::Identifier(ident) = expression else { return Ok(None) };
        Ok((ident.value == "limit_value").then(|| {
            Resolved { reference: (), evaluation: Evaluation::known(PgValue::Integer(3), INTEGER) }
        }))
    }

    fn callees(&mut self, call: &Function) -> Result<Vec<Callee>, Infallible> {
        let returns_set = match call.name.to_string().as_str() {
            "generate_series" => true,
            "abs" => false,
            _ => return Ok(Vec::new()),
        };
        let callee = Callee::new(
            None,
            NullInput::Strict,
            NullResult::OnlyOnNullInput,
            Volatility::Immutable,
            CalleeKind::Normal,
            INTEGER,
            returns_set,
            0,
        );
        Ok(vec![callee])
    }

    fn query(
        &mut self,
        query: &Query,
        _guarantees: &Guarantees<()>,
    ) -> Result<QueryEvaluation, Infallible> {
        let text = query.to_string();
        let k = Evaluation::known(PgValue::Integer(4), INTEGER);
        Ok(if text.contains("FROM one_row") {
            QueryEvaluation::new(Rows::ONE, Some(vec![k]), false)
        } else if text.contains("FROM no_row") {
            QueryEvaluation::new(Rows::NONE, Some(vec![k]), false)
        } else if text.contains("FROM maybe_row") {
            QueryEvaluation::new(Rows::new(true, true, false), Some(vec![k]), false)
        } else {
            QueryEvaluation::unknown()
        })
    }
}

impl values::Context for Parameters {
    fn variable(&mut self, variable: &Name, fields: &[String]) -> Result<Evaluation, Infallible> {
        Ok(match variable.kind() {
            NameKind::Parameter { position } => {
                Evaluation::unknown(self.0[position - 1].clone()).with_error(false)
            }
            // A field `f` holds an integer, and reading it raises until the
            // record is assigned.
            _ if fields == ["f"] => Evaluation::unknown(INTEGER),
            _ => Evaluation::unknown(ScalarType::Unknown).with_error(!fields.is_empty()),
        })
    }
}

/// A context answering nothing, so the domain reads every default.
struct Untyped;

impl sqlparser_expr_eval::Context for Untyped {
    type Reference = ();
    type Error = Infallible;

    fn reference(&mut self, _expression: &Expr) -> Result<Option<Resolved<()>>, Infallible> {
        Ok(None)
    }

    fn callees(&mut self, _call: &Function) -> Result<Vec<Callee>, Infallible> {
        Ok(Vec::new())
    }
}

impl values::Context for Untyped {}

const INTEGER: ScalarType = ScalarType::Integer(IntegerType::Integer);

/// A function with one parameter for each of `parameters`.
fn signature(parameters: &[&str]) -> Signature {
    Signature {
        name: "f".into(),
        parameters: parameters.iter().map(|name| Some((*name).into())).collect(),
        kind: FunctionKind::Plain,
    }
}

/// The walk over `block` with parameters `names`, read through `context`.
fn analysis<'body, C: values::Context<Error = Infallible>>(
    block: &'body Block,
    names: &[&str],
    context: C,
) -> Analysis<'body, C> {
    analyze(block, &signature(names), Transactions::Refused, &mut Scalars, context).unwrap()
}

/// The outcomes `condition` may take where the body reaches it.
fn outcomes<'body, C: values::Context<Error = Infallible>>(
    analysis: &mut Analysis<'body, C>,
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
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
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
    let mut analysis = analysis(&block, &["n"], Parameters(vec![INTEGER]));
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
        let analysis =
            analysis(&block, &["p"], Parameters(vec![ScalarType::Text(TextRules::DEFAULT)]));
        let NodeKind::Case(case) = &block.statements[index].kind else { panic!("a CASE") };
        assert_eq!(analysis.unmatched(case), unmatched, "{body}");
        let first = Sql::Expression(returned(&case.branches[0].statements[0]));
        assert_eq!(analysis.reached(first), unmatched, "{body}");
    }
}

#[test]
fn a_when_listing_several_values_matches_any_of_them() {
    // PostgreSQL answers `listed` for any argument.
    let block = embedded_sql(
        "BEGIN p := 'b'; CASE p WHEN 'a', 'b' THEN RETURN 'listed'; ELSE RETURN 'other'; \
         END CASE; END",
    )
    .unwrap();
    let analysis = analysis(&block, &["p"], Parameters(vec![ScalarType::Text(TextRules::DEFAULT)]));
    let NodeKind::Case(case) = &block.statements[1].kind else { panic!("a CASE") };
    let otherwise = case.otherwise.as_ref().expect("an ELSE");
    assert!(analysis.reached(Sql::Expression(returned(&case.branches[0].statements[0]))));
    assert!(!analysis.reached(Sql::Expression(returned(&otherwise[0]))));
}

#[test]
fn a_handler_reads_the_values_written_before_the_raise() {
    // PostgreSQL answers 2.
    let block = embedded_sql(
        "DECLARE x int := 1; BEGIN BEGIN x := 2; PERFORM 1/0; \
         EXCEPTION WHEN division_by_zero THEN RETURN x; END; RETURN 0; END",
    )
    .unwrap();
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
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
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
    let negative = if_condition(&block.statements[1]);
    assert!(!outcomes(&mut analysis, negative).truth);
}

#[test]
fn an_assert_contradicting_its_branch_never_holds() {
    // PostgreSQL answers `passed` for -1 and fails the assertion for 1.
    let block =
        embedded_sql("BEGIN IF n > 0 THEN ASSERT n < 0; END IF; RETURN 'passed'; END").unwrap();
    let mut analysis = analysis(&block, &["n"], Parameters(vec![INTEGER]));
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
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
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
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
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
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
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
        let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
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
    let mut analysis = analysis(&block, parameters, Parameters(vec![INTEGER; parameters.len()]));
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
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
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
    let mut analysis = analysis(&block, &["n"], Parameters(vec![INTEGER]));
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
    let analysis = analysis(&block, &[], Parameters(Vec::new()));
    assert!(analysis.reached(Sql::Expression(returned(&block.statements[2]))));
}

/// The outcomes of `kept` where the first handler of the block `body` opens
/// with returns, read through `context`.
fn handled<C: values::Context<Error = Infallible>>(body: &str, kept: &str, context: C) -> Outcomes {
    let block = embedded_sql(body).unwrap();
    let mut analysis = analysis(&block, &[], context);
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
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
    assert!(outcomes(&mut analysis, if_condition(&block.statements[0])).truth);
    let NodeKind::If(choice) = &block.statements[0].kind else { panic!("an IF") };
    assert!(analysis.reached(Sql::Expression(returned(&choice.branches[0].statements[0]))));
    let raised = "DECLARE x text := 'maybe'; y int := 1; BEGIN BEGIN y := 2; \
                  IF x THEN y := 3; ELSE y := 3; END IF; y := 4; RETURN 0; \
                  EXCEPTION WHEN invalid_text_representation THEN RETURN y; END; END";
    assert!(handled(raised, "y = 2", Parameters(Vec::new())).truth);
}

#[test]
fn a_null_condition_of_another_type_reads_null() {
    // PostgreSQL answers `else`.
    let block =
        embedded_sql("DECLARE x text; BEGIN IF x THEN RETURN 'then'; END IF; RETURN 'else'; END")
            .unwrap();
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
    assert_eq!(outcomes(&mut analysis, if_condition(&block.statements[0])), Outcomes::NULL);
}

#[test]
fn a_field_of_a_record_not_yet_assigned_raises() {
    // PostgreSQL raises 55000 reading `r.f`, so the handler returns 2.
    let body = "DECLARE r record; y int := 1; BEGIN BEGIN y := 2; \
                IF r.f IS NULL THEN y := 3; ELSE y := 3; END IF; y := 4; RETURN 0; \
                EXCEPTION WHEN OTHERS THEN RETURN y; END; END";
    assert!(handled(body, "y = 2", Untyped).truth);
}

#[test]
fn widening_keeps_what_a_loop_never_changes() {
    // PostgreSQL answers `five`.
    let block = embedded_sql(
        "DECLARE i int := 0; a int := 0; b int := 0; c int := 0; d int := 0; k int := 5; \
         BEGIN LOOP IF c = 1 THEN d := 1; END IF; IF b = 1 THEN c := 1; END IF; \
         IF a = 1 THEN b := 1; END IF; IF i > 1000 THEN a := 1; END IF; \
         i := i + 1; EXIT WHEN i > 5; END LOOP; \
         IF k = 5 THEN RETURN 'five'; END IF; RETURN 'other'; END",
    )
    .unwrap();
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
    assert_eq!(outcomes(&mut analysis, if_condition(&block.statements[1])), Outcomes::TRUE);
}

#[test]
fn nothing_is_read_where_no_path_reaches() {
    // PostgreSQL answers `early`.
    let block =
        embedded_sql("BEGIN RETURN 'early'; IF n > 0 THEN RETURN 'late'; END IF; END").unwrap();
    let mut analysis = analysis(&block, &["n"], Parameters(vec![INTEGER]));
    let condition = if_condition(&block.statements[1]);
    assert!(analysis.condition(condition).unwrap().is_none());
    let read = analysis.truth_under(Sql::Expression(condition), &parsed("n > 0")).unwrap();
    assert!(read.is_none());
}

#[test]
fn a_field_write_sets_the_field_and_a_subscript_write_forgets_the_array() {
    // PostgreSQL answers `3{5}`, the subscript write making `a` non-null.
    let block = embedded_sql(
        "DECLARE r record; a int[]; BEGIN SELECT 1 AS f INTO r; r.f := 3; \
         a[1] := coalesce(a[1], 5); RETURN r.f || a::text; END",
    )
    .unwrap();
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
    let NodeKind::Assignment(subscripted) = &block.statements[2].kind else {
        panic!("an assignment")
    };
    let before = Sql::Expression(&subscripted.value);
    let null = parsed("a IS NULL");
    assert_eq!(analysis.truth_under(before, &null).unwrap().unwrap().outcomes(), Outcomes::TRUE);
    let last = Sql::Expression(returned(&block.statements[3]));
    assert!(analysis.truth_under(last, &null).unwrap().unwrap().outcomes().falsity);
    let field = analysis.truth_under(last, &parsed("r.f = 3")).unwrap().unwrap();
    assert_eq!(field.outcomes(), Outcomes::TRUE);
}

#[test]
fn a_dynamic_command_reads_the_values_its_arguments_name() {
    // PostgreSQL answers 1.
    let block = embedded_sql(
        "DECLARE v int := 1; x int; BEGIN EXECUTE 'SELECT $1' INTO x USING v; RETURN x; END",
    )
    .unwrap();
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
    let NodeKind::Dynamic { dynamic, .. } = &block.statements[0].kind else { panic!("an EXECUTE") };
    let read = analysis.truth_under(Sql::Dynamic(dynamic), &parsed("v = 1")).unwrap();
    assert_eq!(read.unwrap().outcomes(), Outcomes::TRUE);
}

#[test]
fn a_query_reading_a_relation_assigns_what_the_context_returns() {
    // PostgreSQL answers `4 t 0`, and `maybe_row` may hold the one row or
    // none.
    let body = "DECLARE x int; y int := 7; z int := 9; w int; counted int; \
                BEGIN SELECT k INTO x FROM one_row; SELECT k INTO y FROM no_row; \
                SELECT k INTO z FROM maybe_row; SELECT k INTO w FROM elsewhere; \
                GET DIAGNOSTICS counted = ROW_COUNT; RETURN x || (y IS NULL) || z || w || counted; END";
    let read = at_return(body, &[], &["x = 4", "y IS NULL", "z = 4", "w IS NULL"]);
    assert_eq!(read[..2], [Outcomes::TRUE; 2]);
    assert_eq!(read[2], Outcomes::TRUE.union(Outcomes::NULL));
    assert!(read[3].truth && read[3].falsity);
}

#[test]
fn a_select_whose_row_count_the_domain_cannot_tell_may_leave_found_false() {
    // PostgreSQL answers `f`, `f` and `t`.
    let either = Outcomes::TRUE.union(Outcomes::FALSE);
    for (select, found) in [
        ("SELECT 1 INTO x LIMIT 0", either),
        ("SELECT 1 INTO x HAVING false", either),
        ("SELECT abs(-1) INTO x", Outcomes::TRUE),
    ] {
        let body = format!("DECLARE x int; BEGIN {select}; RETURN found; END");
        assert_eq!(at_return(&body, &[], &["found"]), [found], "{select}");
    }
}

#[test]
fn a_test_that_raises_reaches_the_handler_before_its_branch_runs() {
    // PostgreSQL answers 2 for each, raising `division_by_zero`, or
    // `syntax_error` for a `WHEN` that lists no plain values.
    for statement in [
        "CASE WHEN 1 / v > 0 THEN y := 3; ELSE y := 3; END CASE",
        "CASE 1 / v WHEN 1 THEN y := 3; ELSE y := 3; END CASE",
        "ASSERT 1 / v > 0",
        "CASE 1 WHEN 1 FROM one_row THEN y := 3; ELSE y := 3; END CASE",
        "CASE 1 WHEN 1 AS a THEN y := 3; ELSE y := 3; END CASE",
        "CASE 1 WHEN 1 WHERE false THEN y := 3; ELSE y := 3; END CASE",
        "CASE 1 WHEN 1 / v THEN y := 3; ELSE y := 3; END CASE",
    ] {
        let body = format!(
            "DECLARE v int := 0; y int := 1; BEGIN BEGIN y := 2; {statement}; y := 4; RETURN 0; \
             EXCEPTION WHEN OTHERS THEN RETURN y; END; END"
        );
        assert!(handled(&body, "y = 2", Parameters(Vec::new())).truth, "{statement}");
    }
}

#[test]
fn an_assert_that_holds_and_a_bare_exit_raise_nothing() {
    // PostgreSQL answers 0, never entering the handler.
    let body = "DECLARE v int := 1; y int := 1; BEGIN BEGIN y := 2; \
                ASSERT v = 1, 'v is not one'; LOOP EXIT; END LOOP; y := 3; RETURN 0; \
                EXCEPTION WHEN OTHERS THEN RETURN y; END; END";
    assert!(!handled(body, "y = 2", Parameters(Vec::new())).truth);
}

#[test]
fn casts_collations_and_subqueries_read_through_the_context() {
    // PostgreSQL answers `then`, `then` and `else`.
    for (body, read) in [
        ("DECLARE x text := '5'; BEGIN IF x::int > 3 THEN RETURN 'then'; END IF; END", true),
        (
            "DECLARE x text COLLATE \"C\" := 'a'; \
             BEGIN IF x < 'b' COLLATE \"C\" THEN RETURN 'then'; END IF; END",
            true,
        ),
        ("BEGIN IF EXISTS (SELECT 1 FROM no_row) THEN RETURN 'then'; END IF; END", false),
    ] {
        let block = embedded_sql(body).unwrap();
        let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
        let index = block.statements.len() - 1;
        assert_eq!(outcomes(&mut analysis, if_condition(&block.statements[index])).truth, read);
    }
}

#[test]
fn a_name_no_variable_answers_reads_through_the_context() {
    // The context answers 3 for `limit_value`, which a variable shadows.
    for (body, over) in [
        ("BEGIN IF limit_value > 5 THEN RETURN 'over'; END IF; END", Outcomes::FALSE),
        (
            "DECLARE limit_value int := 9; \
             BEGIN IF limit_value > 5 THEN RETURN 'over'; END IF; END",
            Outcomes::TRUE,
        ),
    ] {
        let block = embedded_sql(body).unwrap();
        let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
        assert_eq!(outcomes(&mut analysis, if_condition(&block.statements[0])), over, "{body}");
    }
}

/// A context answering `bound_value` with the integer it holds, as a caller
/// binds the names of an expression just before reading it.
struct Bound(i64);

impl sqlparser_expr_eval::Context for Bound {
    type Reference = ();
    type Error = Infallible;

    fn reference(&mut self, expression: &Expr) -> Result<Option<Resolved<()>>, Infallible> {
        let Expr::Identifier(identifier) = expression else { return Ok(None) };
        Ok((identifier.value == "bound_value").then(|| {
            Resolved {
                reference: (),
                evaluation: Evaluation::known(PgValue::Integer(self.0), INTEGER),
            }
        }))
    }

    fn callees(&mut self, _call: &Function) -> Result<Vec<Callee>, Infallible> {
        Ok(Vec::new())
    }
}

impl values::Context for Bound {}

#[test]
fn an_expression_reads_what_the_context_holds_when_it_is_read() {
    let block = embedded_sql("BEGIN RETURN 1; END").unwrap();
    let mut analysis = analysis(&block, &[], Bound(1));
    let site = Sql::Expression(returned(&block.statements[0]));
    let seven = parsed("bound_value = 7");
    let read = analysis.truth_under(site, &seven).unwrap().unwrap();
    assert_eq!(read.outcomes(), Outcomes::FALSE);
    analysis.context_mut().0 = 7;
    let read = analysis.truth_under(site, &seven).unwrap().unwrap();
    assert_eq!(read.outcomes(), Outcomes::TRUE);
}

#[test]
fn a_positional_parameter_reads_the_parameter_it_numbers() {
    // PostgreSQL answers `other` for 1, -1 and `NULL`.
    let block = embedded_sql(
        "BEGIN IF n > 0 THEN IF $1 <= 0 THEN RETURN 'never'; END IF; END IF; RETURN 'other'; END",
    )
    .unwrap();
    let mut analysis = analysis(&block, &["n"], Parameters(vec![INTEGER]));
    let NodeKind::If(outer) = &block.statements[0].kind else { panic!("an IF") };
    let inner = if_condition(&outer.branches[0].statements[0]);
    assert_eq!(outcomes(&mut analysis, inner), Outcomes::FALSE);
}

#[test]
fn an_alias_and_a_copied_type_hold_what_is_assigned_them() {
    // PostgreSQL answers `five`.
    let block = embedded_sql(
        "DECLARE a ALIAS FOR $1; x n%TYPE := 4; \
         BEGIN a := 5; IF a = 5 AND x = 4 THEN RETURN 'five'; END IF; RETURN 'other'; END",
    )
    .unwrap();
    let mut analysis = analysis(&block, &["n"], Parameters(vec![INTEGER]));
    assert!(outcomes(&mut analysis, if_condition(&block.statements[1])).truth);
}

#[test]
fn a_cursor_is_null_until_opened() {
    // PostgreSQL answers `null`.
    let block = embedded_sql(
        "DECLARE c CURSOR FOR SELECT 1; BEGIN IF c IS NULL THEN RETURN 'null'; END IF; END",
    )
    .unwrap();
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
    assert!(outcomes(&mut analysis, if_condition(&block.statements[0])).truth);
}

#[test]
fn a_handler_reads_the_raised_sqlstate() {
    // PostgreSQL answers `division`.
    let block = embedded_sql(
        "BEGIN PERFORM 1 / 0; RETURN 'none'; EXCEPTION WHEN OTHERS THEN \
         IF SQLSTATE = '22012' THEN RETURN 'division'; END IF; RETURN 'other'; END",
    )
    .unwrap();
    let mut analysis = analysis(&block, &[], Parameters(Vec::new()));
    assert!(outcomes(&mut analysis, if_condition(&block.handlers[0].statements[0])).truth);
}

#[test]
fn a_loop_ends_where_control_leaves_it() {
    // Each answer is one loop's, outer first. PostgreSQL runs every loop
    // answering false until a statement timeout cancels it.
    for (body, answers) in [
        ("BEGIN LOOP PERFORM pg_sleep(1); END LOOP; END", [Some(false)].as_slice()),
        (
            "DECLARE n integer := 0; BEGIN WHILE n < 10 LOOP EXIT WHEN n > 3; END LOOP; END",
            &[Some(false)],
        ),
        (
            "DECLARE i integer := 0; BEGIN WHILE i < 10 LOOP i := i + 1; END LOOP; END",
            &[Some(true)],
        ),
        ("BEGIN LOOP RETURN 1; END LOOP; END", &[Some(true)]),
        ("BEGIN <<around>> LOOP LOOP EXIT around; END LOOP; END LOOP; END", &[Some(true); 2]),
        (
            "DECLARE k int := 0; BEGIN <<o>> LOOP k := k + 1; LOOP CONTINUE o; END LOOP; END LOOP; \
             END",
            &[Some(false), Some(true)],
        ),
        ("BEGIN LOOP <<b>> BEGIN EXIT b; END; END LOOP; END", &[Some(false)]),
        // The function's own label ends the body.
        ("BEGIN LOOP EXIT f; END LOOP; END", &[Some(true)]),
        ("BEGIN RETURN 1; LOOP NULL; END LOOP; END", &[None]),
    ] {
        assert_eq!(ends(body), answers, "{body}");
    }
}

#[test]
fn a_loop_ends_where_a_raise_escapes_it() {
    // Each answer is one loop's. PostgreSQL raises out of every loop
    // answering true and runs every other until a statement timeout cancels
    // it.
    for (body, ends_loop) in [
        ("BEGIN LOOP RAISE EXCEPTION 'stop'; END LOOP; END", true),
        ("DECLARE x int := 0; BEGIN LOOP CASE x WHEN 1 THEN NULL; END CASE; END LOOP; END", true),
        ("BEGIN LOOP ASSERT false; END LOOP; END", true),
        ("BEGIN LOOP COMMIT; END LOOP; END", true),
        (
            "BEGIN LOOP RAISE EXCEPTION 'x'; END LOOP; EXCEPTION WHEN OTHERS THEN RETURN 1; END",
            true,
        ),
        (
            "BEGIN LOOP BEGIN RAISE EXCEPTION 'x'; EXCEPTION WHEN OTHERS THEN NULL; END; END LOOP; END",
            false,
        ),
        (
            "BEGIN LOOP BEGIN RAISE EXCEPTION 'x'; EXCEPTION WHEN division_by_zero THEN NULL; END; \
             END LOOP; END",
            true,
        ),
        (
            "BEGIN LOOP BEGIN RAISE division_by_zero; EXCEPTION WHEN data_exception THEN NULL; END; \
             END LOOP; END",
            false,
        ),
        (
            "BEGIN LOOP BEGIN ASSERT false; EXCEPTION WHEN OTHERS THEN NULL; END; END LOOP; END",
            true,
        ),
        (
            "BEGIN LOOP BEGIN ASSERT false; EXCEPTION WHEN assert_failure THEN NULL; END; END LOOP; \
             END",
            false,
        ),
        (
            "BEGIN LOOP BEGIN RAISE EXCEPTION USING ERRCODE = 'unique_violation'; \
             EXCEPTION WHEN unique_violation THEN NULL; END; END LOOP; END",
            false,
        ),
        (
            "BEGIN LOOP BEGIN RAISE EXCEPTION USING ERRCODE = 'no_such_thing'; \
             EXCEPTION WHEN undefined_object THEN NULL; END; END LOOP; END",
            false,
        ),
        // `MESSAGE` beside a format raises `syntax_error`.
        (
            "BEGIN LOOP BEGIN RAISE EXCEPTION 'x' USING MESSAGE = 'y'; \
             EXCEPTION WHEN raise_exception THEN NULL; END; END LOOP; END",
            true,
        ),
        (
            "BEGIN LOOP BEGIN RAISE EXCEPTION 'x'; EXCEPTION WHEN SQLSTATE '00000' THEN NULL; END; \
             END LOOP; END",
            true,
        ),
    ] {
        assert_eq!(ends(body), [Some(ends_loop)], "{body}");
    }
}

/// Whether control may leave each loop of `body`, the body of a function
/// `f` without parameters, outer first.
fn ends(body: &str) -> Vec<Option<bool>> {
    let block = embedded_sql(body).unwrap();
    let analysis = analysis(&block, &[], Parameters(Vec::new()));
    loops(&block.statements).into_iter().map(|repeated| analysis.ends(repeated)).collect()
}

/// Every loop among `nodes` and the blocks and loops inside them, outer
/// first.
fn loops(nodes: &[Node]) -> Vec<&Loop> {
    let mut found = Vec::new();
    for node in nodes {
        match &node.kind {
            NodeKind::Loop(repeated) => {
                found.push(repeated);
                found.extend(loops(&repeated.statements));
            }
            NodeKind::Block(block) => found.extend(loops(&block.statements)),
            _ => {}
        }
    }
    found
}

/// `text` parsed as one PostgreSQL expression.
fn parsed(text: &str) -> Expr {
    Parser::new(&PostgreSqlDialect {}).try_with_sql(text).unwrap().parse_expr().unwrap()
}
