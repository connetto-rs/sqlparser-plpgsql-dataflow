//! The definitions that may reach each variable an `EXECUTE` of a PL/pgSQL
//! body reads, followed through its branches, loops, blocks, handlers and
//! control transfers.
extern crate alloc;

use alloc::collections::BTreeMap;
use core::ops::ControlFlow;

use sqlparser::ast::{Expr, Query, Statement, Value, visit_expressions};
use sqlparser_plpgsql::{
    embedded::{DeclarationKind, DeclaredType, Dynamic, NodeKind, embedded_sql},
    namespace::{FunctionKind, Name, NameKind, Namespace, Signature, Sql},
};
use sqlparser_plpgsql_dataflow::{
    Catalog, Ending, Escape, Part, Return, Source, Step, Transactions,
    reaching::{ReachingDefinitions, Slot, State},
    walk,
};

/// A schema where a variable of type `record` or `t` holds a row, as does
/// each parameter at the positions `rows` lists, and each `CALL` written as
/// a key of `calls` reaches one procedure writing back to the arguments its
/// value marks.
#[derive(Default)]
struct Schema {
    rows: Vec<usize>,
    calls: BTreeMap<&'static str, Vec<bool>>,
}

impl Catalog for Schema {
    fn holds_row(&self, name: &Name) -> bool {
        match name.kind() {
            NameKind::Parameter { position } => self.rows.contains(position),
            NameKind::Declared { declaration, .. } => {
                matches!(
                    &declaration.kind,
                    DeclarationKind::Variable(variable)
                        if matches!(&variable.data_type, DeclaredType::Data(data_type)
                            if ["record", "t"].contains(&data_type.to_string().to_lowercase().as_str()))
                )
            }
            _ => false,
        }
    }

    fn written_back(&mut self, call: &Statement) -> Option<Vec<bool>> {
        self.calls.get(call.to_string().as_str()).cloned()
    }
}

/// How the test spells a variable, by its name in `signature` or its
/// declaration.
fn variable(name: &Name, signature: &Signature) -> String {
    match name.kind() {
        NameKind::Parameter { position } => signature.parameters[position - 1].clone().unwrap(),
        NameKind::Declared { declaration, .. } => declaration.name.clone(),
        NameKind::Trigger(trigger) => trigger.name().to_lowercase(),
        NameKind::LoopIndex { variable } | NameKind::LoopRecord { variable, .. } => {
            variable.clone()
        }
        NameKind::Found => "found".to_owned(),
        other => format!("{other:?}"),
    }
}

/// The expression a `SELECT` evaluating one expression evaluates.
fn expression(query: &Query) -> String {
    query.to_string().strip_prefix("SELECT ").unwrap().to_owned()
}

/// How a test spells a definition, the part it assigns before its source.
fn rendered(slot: Slot, domain: &ReachingDefinitions<'_>) -> String {
    let Slot::Written(index) = slot else { return "incoming".to_owned() };
    let write = &domain.definitions()[index].write;
    let source = match &write.source {
        Source::Null => "null".to_owned(),
        Source::Value(value) => expression(value),
        Source::CursorName => "cursor name".to_owned(),
        Source::PortalName => "portal name".to_owned(),
        Source::PortalReleased => "portal released".to_owned(),
        Source::Query { statement, output, rows } => format!("{output:?} {rows:?} of {statement}"),
        Source::Dynamic { dynamic, output, rows } => {
            format!("{output:?} {rows:?} of EXECUTE {}", expression(&dynamic.command))
        }
        Source::Cursor { cursor, output } => {
            let NameKind::Declared { declaration, .. } = cursor.kind() else { panic!("a cursor") };
            format!("{output:?} of FETCH {}", declaration.name)
        }
        Source::Call { call, argument } => format!("argument {argument} of {call}"),
        Source::Diagnostics(item) => format!("{item:?}"),
        Source::LoopIndex { reverse, lower, upper, .. } => {
            format!(
                "{}{} .. {}",
                if *reverse { "reverse " } else { "" },
                expression(lower),
                expression(upper)
            )
        }
        Source::ArrayElement { array, slice, output } => {
            format!("{output:?} slice {slice} of {}", expression(array))
        }
        Source::Found(found) => {
            match write.site {
                Some(Sql::Statement(statement)) => format!("{found:?} of {statement}"),
                Some(Sql::Dynamic(dynamic)) => {
                    format!("{found:?} of EXECUTE {}", expression(&dynamic.command))
                }
                _ => format!("{found:?}"),
            }
        }
    };
    let part: String = write
        .part
        .iter()
        .map(|step| {
            match step {
                Part::Field(field) => format!(".{field}"),
                Part::Index(index) => format!("[{}]", expression(index)),
                Part::Slice { .. } => "[:]".to_owned(),
            }
        })
        .collect();
    if part.is_empty() { source } else { format!("{part} {source}") }
}

/// The variables `dynamic` names in its command and arguments, in the order
/// written, each once.
fn named<'namespace>(
    dynamic: &Dynamic,
    namespace: &'namespace Namespace,
    schema: &Schema,
) -> Vec<&'namespace Name> {
    let mut names: Vec<&Name> = Vec::new();
    for query in core::iter::once(&*dynamic.command).chain(&dynamic.arguments) {
        let _ = visit_expressions(query, |expr| {
            let parts: Vec<String> = match expr {
                Expr::Identifier(ident) => vec![ident.value.to_lowercase()],
                Expr::CompoundIdentifier(idents) => {
                    idents.iter().map(|ident| ident.value.to_lowercase()).collect()
                }
                Expr::Value(value) => {
                    match &value.value {
                        Value::Placeholder(placeholder) => vec![placeholder.clone()],
                        _ => return ControlFlow::<()>::Continue(()),
                    }
                }
                _ => return ControlFlow::Continue(()),
            };
            if let Some((name, _)) = namespace.lookup(&parts, |name| schema.holds_row(name))
                && !names.contains(&name)
            {
                names.push(name);
            }
            ControlFlow::Continue(())
        });
    }
    names
}

/// The definitions of each variable each `EXECUTE` and `OPEN ... FOR
/// EXECUTE` of `body`, in the function `signature` describes, reads, in the
/// order written.
fn reaching_with(
    body: &str,
    signature: &Signature,
    transactions: Transactions,
    mut schema: Schema,
) -> Vec<Vec<(String, Vec<String>)>> {
    let block = embedded_sql(body).unwrap();
    let mut domain = ReachingDefinitions::new();
    let flow =
        walk(&block, signature, transactions, Ending::Raises, &mut schema, &mut domain).unwrap();
    let sites = block.sites(signature, |name| schema.holds_row(name)).unwrap();
    sites
        .iter()
        .filter_map(|site| {
            let Sql::Dynamic(dynamic) = site.sql else { return None };
            let reached: Option<&State> = flow.at(site.sql);
            let reads = named(dynamic, &site.namespace, &schema)
                .into_iter()
                .map(|name| {
                    let definitions = match reached {
                        None => vec!["unreachable".to_owned()],
                        Some(state) => {
                            state.get(&name.id()).map_or_else(
                                || vec!["incoming".to_owned()],
                                |slots| slots.iter().map(|slot| rendered(*slot, &domain)).collect(),
                            )
                        }
                    };
                    (variable(name, signature), definitions)
                })
                .collect();
            Some(reads)
        })
        .collect()
}

/// The function `run(p text, q integer)`.
fn run() -> Signature {
    Signature {
        name: "run".to_owned(),
        parameters: vec![Some("p".to_owned()), Some("q".to_owned())],
        kind: FunctionKind::Plain,
    }
}

/// The reads of the function `run(p text, q integer)` running `body`.
fn reaching(body: &str) -> Vec<Vec<(String, Vec<String>)>> {
    reaching_with(body, &run(), Transactions::Refused, Schema::default())
}

/// The reads of the procedure `run(p text, q integer)`, which may control
/// transactions, running `body`.
fn reaching_in_procedure(body: &str) -> Vec<Vec<(String, Vec<String>)>> {
    reaching_with(body, &run(), Transactions::Controlled, Schema::default())
}

/// The reads of `run(p text, q integer)` running `body`, where each `CALL`
/// written as a key of `calls` writes back to the arguments its value marks.
fn reaching_calling(
    body: &str,
    calls: &[(&'static str, &[bool])],
) -> Vec<Vec<(String, Vec<String>)>> {
    let calls = calls.iter().map(|(call, back)| (*call, back.to_vec())).collect();
    reaching_with(body, &run(), Transactions::Refused, Schema { rows: Vec::new(), calls })
}

fn read(variable: &str, definitions: &[&str]) -> (String, Vec<String>) {
    (variable.to_owned(), definitions.iter().map(|&definition| definition.to_owned()).collect())
}

/// An assignment completing on every path replaces the default, and a
/// parameter holds the argument passed.
#[test]
fn an_assignment_replaces_what_the_variable_held() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN s := 'SELECT ' || p; EXECUTE s USING q; END"
        ),
        [vec![read("s", &["'SELECT ' || p"]), read("q", &["incoming"])]]
    );
}

/// A statement without `INTO` that is no `CALL` assigns no variable.
#[test]
fn a_statement_without_into_keeps_what_variables_hold() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN UPDATE t SET name = s WHERE id = q; EXECUTE s; END"
        ),
        [vec![read("s", &["'SELECT 1'"])]]
    );
}

/// A branch that does not assign keeps what the variable held before the
/// branch, beside what every assigning branch leaves.
#[test]
fn branches_join_what_each_path_leaves() {
    assert_eq!(
        reaching(
            "DECLARE s text;
             BEGIN
              IF q > 1 THEN s := 'SELECT 1';
              ELSIF q > 0 THEN PERFORM 1;
              ELSE s := format('SELECT %I', p);
              END IF;
              EXECUTE s;
             END"
        ),
        [vec![read("s", &["null", "'SELECT 1'", "format('SELECT %I', p)"])]]
    );
}

/// A definition written later in a loop reaches an earlier read through the
/// back edge, and a loop that runs no iteration keeps the default.
#[test]
fn a_loop_carries_its_later_writes_back_to_its_head() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              FOR iteration IN 1..2 LOOP
               EXECUTE s;
               s := 'SELECT ' || p;
              END LOOP;
              EXECUTE s;
             END"
        ),
        [
            vec![read("s", &["'SELECT 1'", "'SELECT ' || p"])],
            vec![read("s", &["'SELECT 1'", "'SELECT ' || p"])],
        ]
    );
}

/// An assignment in a nested block reaches the outer variable after the
/// block ends, and a declaration of the same name in a nested block is
/// another variable, whose writes never reach the outer one.
#[test]
fn a_hiding_declaration_is_another_variable() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1'; o text;
             BEGIN
              DECLARE s text := 'SELECT 2';
              BEGIN s := 'SELECT 3'; o := s; END;
              EXECUTE s USING o;
             END"
        ),
        [vec![read("s", &["'SELECT 1'"]), read("o", &["s"])]]
    );
}

/// A handler starts from what the variables held wherever its block's
/// statements raised, so an assignment that raised leaves the earlier
/// value, and a handler keeps what reached the raise, as PostgreSQL rolls
/// back only the database.
#[test]
fn a_handler_sees_the_values_at_every_raise() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              BEGIN
               s := (1 / q)::text;
               PERFORM 1 / q;
              EXCEPTION WHEN OTHERS THEN
               EXECUTE s;
              END;
             END"
        ),
        [vec![read("s", &["'SELECT 1'", "(1 / q)::TEXT"])]]
    );
}

/// A field assignment changes part of the variable, so the definitions of
/// the whole still reach.
#[test]
fn a_field_write_keeps_the_rest_of_the_variable() {
    assert_eq!(
        reaching(
            "DECLARE r record;
             BEGIN
              SELECT name INTO r FROM t;
              r.name := p;
              EXECUTE r.name;
             END"
        ),
        [vec![read("r", &["Row First { strict: false } of SELECT name FROM t", ".name p"])]]
    );
}

/// `EXIT` and `RETURN` leave, so what they skip never reaches, and a read
/// after `RETURN` is unreachable.
#[test]
fn control_transfers_skip_what_they_leave() {
    assert_eq!(
        reaching(
            "DECLARE s text;
             BEGIN
              LOOP s := 'SELECT 1'; EXIT; END LOOP;
              <<inner>> BEGIN
               s := 'SELECT 2';
               EXIT inner WHEN q > 0;
               s := 'SELECT 3';
              END;
              EXECUTE s;
              RETURN;
              EXECUTE p;
             END"
        ),
        [vec![read("s", &["'SELECT 2'", "'SELECT 3'"])], vec![read("p", &["unreachable"])]]
    );
}

/// `SELECT ... INTO` assigns a query output, with its `STRICT` and the
/// output position, and an `EXECUTE ... INTO` the command's result.
#[test]
fn into_assigns_query_and_command_outputs() {
    assert_eq!(
        reaching(
            "DECLARE s text; n integer;
             BEGIN
              SELECT name, id INTO STRICT s, n FROM t WHERE name = p;
              EXECUTE s USING n;
              EXECUTE 'SELECT ' || p INTO s;
              EXECUTE s;
             END"
        ),
        [
            vec![
                read(
                    "s",
                    &["Ordinal(0) First { strict: true } of SELECT name, id FROM t WHERE name = p"]
                ),
                read(
                    "n",
                    &["Ordinal(1) First { strict: true } of SELECT name, id FROM t WHERE name = p"]
                ),
            ],
            vec![read("p", &["incoming"])],
            vec![read("s", &["Ordinal(0) First { strict: false } of EXECUTE 'SELECT ' || p"])],
        ]
    );
}

/// A `STRICT` query that raises assigns nothing, so its handler sees the
/// earlier value beside the query output.
#[test]
fn a_strict_query_that_raises_leaves_the_earlier_value() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              BEGIN
               SELECT name INTO STRICT s FROM t;
               PERFORM 1 / q;
              EXCEPTION WHEN OTHERS THEN
               EXECUTE s;
              END;
             END"
        ),
        [vec![read(
            "s",
            &["'SELECT 1'", "Ordinal(0) First { strict: true } of SELECT name FROM t"]
        )]]
    );
}

/// A loop over a query assigns its target each row, and the empty row, a
/// null, when the query returns none. An empty `FOREACH` keeps what the
/// target held.
#[test]
fn loops_over_rows_and_arrays_assign_their_targets() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1'; e text := 'SELECT 2';
             BEGIN
              FOR s IN SELECT name FROM t LOOP END LOOP;
              FOREACH e IN ARRAY ARRAY[p] LOOP END LOOP;
              EXECUTE s USING e;
             END"
        ),
        [vec![
            read(
                "s",
                &[
                    "Ordinal(0) Empty of SELECT name FROM t",
                    "Ordinal(0) Each of SELECT name FROM t",
                ]
            ),
            read("e", &["'SELECT 2'", "Row slice 0 of ARRAY[p]"]),
        ]]
    );
}

/// A loop over a command's rows assigns each row, and the empty row when
/// the command returns none.
#[test]
fn a_loop_over_a_command_assigns_each_row_or_the_empty_row() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              FOR s IN EXECUTE 'SELECT ' || p LOOP EXECUTE s; END LOOP;
              EXECUTE s;
             END"
        ),
        [
            vec![read("p", &["incoming"])],
            vec![read("s", &["Ordinal(0) Each of EXECUTE 'SELECT ' || p"])],
            vec![read(
                "s",
                &[
                    "Ordinal(0) Empty of EXECUTE 'SELECT ' || p",
                    "Ordinal(0) Each of EXECUTE 'SELECT ' || p",
                ],
            )],
        ]
    );
}

/// A loop over a query whose body always returns leaves the loop only
/// through the query returning no row, so only the empty row follows it.
#[test]
fn a_query_loop_that_always_returns_leaves_only_the_empty_row() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              FOR s IN SELECT name FROM t LOOP RETURN; END LOOP;
              EXECUTE s;
             END"
        ),
        [vec![read("s", &["Ordinal(0) Empty of SELECT name FROM t"])]]
    );
}

/// `FETCH`, `OPEN`, `GET DIAGNOSTICS` and `CALL` assign what they read,
/// and a `CALL` reaching no single procedure adds what it may return beside
/// the earlier value.
#[test]
fn every_other_write_assigns_its_targets() {
    assert_eq!(
        reaching(
            "DECLARE c CURSOR FOR SELECT name FROM t; k refcursor; s text; n integer;
              o text := 'SELECT 1';
             BEGIN
              OPEN c;
              FETCH c INTO s;
              GET DIAGNOSTICS n = ROW_COUNT;
              CALL fill(o, 'x', run.p, missing);
              OPEN k FOR SELECT name FROM t;
              OPEN k FOR EXECUTE 'SELECT 2';
              FOR i IN 1..q LOOP EXECUTE s USING n, c, o, i, k, p; END LOOP;
             END"
        ),
        [
            vec![],
            vec![
                read("s", &["Ordinal(0) of FETCH c"]),
                read("n", &["RowCount"]),
                read("c", &["cursor name", "portal name"]),
                read("o", &["'SELECT 1'", "argument 0 of CALL fill(o, 'x', run.p, missing)"]),
                read("i", &["1 .. q"]),
                read("k", &["null", "portal name", "portal name"]),
                read("p", &["incoming", "argument 2 of CALL fill(o, 'x', run.p, missing)"]),
            ],
        ]
    );
}

/// A parameter starts as the argument, which a branch assigning it joins.
#[test]
fn parameters_start_as_their_arguments() {
    assert_eq!(
        reaching("BEGIN IF p IS NULL THEN p := 'SELECT 1'; END IF; EXECUTE p; END"),
        [vec![read("p", &["incoming", "'SELECT 1'"])]]
    );
}

/// A read through an alias or a position reads the variable it names.
#[test]
fn aliases_and_positions_read_the_variable_they_name() {
    assert_eq!(
        reaching(
            "DECLARE s text; a ALIAS FOR p;
             BEGIN s := 'SELECT ' || a; EXECUTE s USING a, $2; END"
        ),
        [vec![read("s", &["'SELECT ' || a"]), read("p", &["incoming"]), read("q", &["incoming"])]]
    );
}

/// `CONTINUE` carries what it leaves back to the loop head, a `WHILE`
/// loop may run no iteration, and `CASE` joins its branches.
#[test]
fn continue_while_and_case_join_their_paths() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              WHILE q > 0 LOOP
               EXECUTE s;
               IF q > 1 THEN s := 'SELECT 2'; CONTINUE; END IF;
               CASE q WHEN 0 THEN s := 'SELECT 3'; ELSE s := 'SELECT 4'; END CASE;
              END LOOP;
              EXECUTE s;
             END"
        ),
        [
            vec![read("s", &["'SELECT 1'", "'SELECT 2'", "'SELECT 3'", "'SELECT 4'"])],
            vec![read("s", &["'SELECT 1'", "'SELECT 2'", "'SELECT 3'", "'SELECT 4'"])],
        ]
    );
}

/// A `CASE` without an `ELSE` raises `case_not_found` where no `WHEN`
/// holds, so a definition no `WHEN` matched does not fall through it, and
/// the walk records the state reaching that end.
#[test]
fn a_case_without_an_else_raises_where_no_when_holds() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              CASE q WHEN 0 THEN s := 'SELECT 2'; END CASE;
              EXECUTE s;
             END"
        ),
        [vec![read("s", &["'SELECT 2'"])]]
    );
}

/// A handler of the `case_not_found` a `CASE` without an `ELSE` raises sees
/// what reached the `CASE`, and a `WHEN` whose last write completed raises
/// nothing after it.
#[test]
fn a_handler_of_the_missing_else_sees_what_reached_the_case() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              BEGIN
               CASE q WHEN 0 THEN s := 'SELECT 2'; END CASE;
              EXCEPTION WHEN OTHERS THEN
               EXECUTE s;
              END;
             END"
        ),
        [vec![read("s", &["'SELECT 1'"])]]
    );
}

/// `EXIT` naming an outer loop leaves both loops, so the statements after
/// the inner loop never run.
#[test]
fn a_labelled_exit_leaves_every_loop_up_to_its_label() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              <<outer>> LOOP
               LOOP s := 'SELECT 2'; EXIT outer; END LOOP;
               s := 'SELECT 3';
              END LOOP;
              EXECUTE s;
             END"
        ),
        [vec![read("s", &["'SELECT 2'"])]]
    );
}

/// A loop over a cursor holding null gives it the name of the portal it
/// opens, and leaving the loop, by `EXIT` too, gives the null back.
#[test]
fn a_cursor_loop_names_its_portal_while_it_runs() {
    assert_eq!(
        reaching(
            "DECLARE c CURSOR FOR SELECT name FROM t;
             BEGIN
              c := NULL;
              FOR r IN c LOOP
               EXECUTE 'MOVE NEXT IN ' || quote_ident(c);
               EXIT WHEN q > 0;
              END LOOP;
              EXECUTE 'CLOSE ' || quote_ident(c);
             END"
        ),
        [vec![read("c", &["NULL", "portal name"])], vec![read("c", &["NULL"])]]
    );
}

/// A declaration in a loop runs its default on every iteration, so the
/// default reads what the previous iteration left.
#[test]
fn a_declaration_in_a_loop_reads_the_previous_iteration() {
    let block = embedded_sql(
        "DECLARE s text := 'SELECT 1';
         BEGIN
          FOR i IN 1..2 LOOP
           DECLARE d text := s || ' UNION SELECT 2';
           BEGIN s := d; END;
          END LOOP;
         END",
    )
    .unwrap();
    let mut domain = ReachingDefinitions::new();
    walk(
        &block,
        &run(),
        Transactions::Refused,
        Ending::Raises,
        &mut Schema::default(),
        &mut domain,
    )
    .unwrap();
    let default = domain
        .definitions()
        .iter()
        .find(|definition| {
            matches!(definition.write.source, Source::Value(value)
                if expression(value) == "s || ' UNION SELECT 2'")
        })
        .unwrap();
    let inputs = &default.inputs;
    let s = domain.definitions()[0].write.variable.id();
    let reaching: Vec<String> = inputs[&s].iter().map(|slot| rendered(*slot, &domain)).collect();
    assert_eq!(reaching, ["'SELECT 1'", "d"]);
}

/// An element write keeps the rest of the array, and nothing after `RAISE
/// EXCEPTION` runs.
#[test]
fn elements_and_raises() {
    assert_eq!(
        reaching(
            "DECLARE a text[] := ARRAY['SELECT 1'];
             BEGIN
              a[q] := p;
              a[1:q] := ARRAY[p];
              a[1].f := p;
              EXECUTE a[1];
              RAISE EXCEPTION 'stop';
              EXECUTE p;
             END"
        ),
        [
            vec![read("a", &["ARRAY['SELECT 1']", "[q] p", "[:] ARRAY[p]", "[1].f p"])],
            vec![read("p", &["unreachable"])],
        ]
    );
}

/// A function runs in its caller's transaction, so `COMMIT` and `ROLLBACK`
/// in its body raise `invalid_transaction_termination` and nothing after
/// them runs, while a handler of their block takes what reached them.
#[test]
fn commit_and_rollback_raise_in_a_function() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              BEGIN
               IF q > 0 THEN COMMIT; ELSE ROLLBACK AND CHAIN; END IF;
               s := p;
              EXCEPTION WHEN invalid_transaction_termination THEN
               EXECUTE s;
              END;
              EXECUTE s;
             END"
        ),
        [vec![read("s", &["'SELECT 1'"])], vec![read("s", &["'SELECT 1'"])]]
    );
}

/// A procedure a `CALL` outside a transaction block runs goes on after
/// `COMMIT` and `ROLLBACK`, in a query loop and in a handler too.
#[test]
fn commit_and_rollback_run_on_in_a_procedure() {
    assert_eq!(
        reaching_in_procedure(
            "DECLARE s text := 'SELECT 1'; r record;
             BEGIN
              COMMIT;
              s := 'SELECT ' || p;
              EXECUTE s;
              FOR r IN SELECT id FROM t LOOP ROLLBACK AND CHAIN; s := s || r.id; END LOOP;
              EXECUTE s;
              BEGIN
               PERFORM 1 / q;
              EXCEPTION WHEN division_by_zero THEN
               COMMIT;
               s := p;
              END;
              EXECUTE s;
             END"
        ),
        [
            vec![read("s", &["'SELECT ' || p"])],
            vec![read("s", &["'SELECT ' || p", "s || r.id"])],
            vec![read("s", &["'SELECT ' || p", "s || r.id", "p"])],
        ]
    );
}

/// A handler in force makes `COMMIT` and `ROLLBACK` in a procedure raise
/// `invalid_transaction_termination`, whichever enclosing block holds it.
#[test]
fn commit_and_rollback_raise_under_a_handler_in_a_procedure() {
    assert_eq!(
        reaching_in_procedure(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              BEGIN
               COMMIT;
               s := p;
              EXCEPTION WHEN invalid_transaction_termination THEN
               EXECUTE s;
              END;
              BEGIN
               BEGIN ROLLBACK; s := p; END;
              EXCEPTION WHEN invalid_transaction_termination THEN
               EXECUTE s;
              END;
              EXECUTE s;
             END"
        ),
        [
            vec![read("s", &["'SELECT 1'"])],
            vec![read("s", &["'SELECT 1'"])],
            vec![read("s", &["'SELECT 1'"])],
        ]
    );
}

/// `REVERSE` counts down from the first bound written.
#[test]
fn a_reversed_range_starts_at_its_first_bound() {
    assert_eq!(
        reaching(
            "BEGIN
              FOR i IN REVERSE q .. 1 LOOP EXECUTE 'SELECT ' || i; END LOOP;
              FOR i IN q .. 1 LOOP EXECUTE 'SELECT ' || i; END LOOP;
             END"
        ),
        [vec![read("i", &["reverse q .. 1"])], vec![read("i", &["q .. 1"])]]
    );
}

/// A notice raises nothing and a write after `RETURN` reaches no read.
#[test]
fn notices_continue_and_returns_end_the_path() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1';
             BEGIN
              RAISE NOTICE 'running %', p;
              s := p || p;
              EXECUTE s;
              RETURN;
              s := q;
              EXECUTE s;
             END"
        ),
        [vec![read("s", &["p || p"])], vec![read("s", &["unreachable"])]]
    );
}

/// The definitions each variable `state` holds a write's definition of, by
/// its name in `signature`.
fn holding(
    state: &State,
    domain: &ReachingDefinitions<'_>,
    signature: &Signature,
) -> Vec<(String, Vec<String>)> {
    state
        .values()
        .map(|slots| {
            let name = slots
                .iter()
                .find_map(|slot| {
                    let Slot::Written(index) = slot else { return None };
                    Some(&domain.definitions()[*index].write.variable)
                })
                .unwrap();
            let definitions = slots.iter().map(|slot| rendered(*slot, domain)).collect();
            (variable(name, signature), definitions)
        })
        .collect()
}

/// A function with output parameters returns at the end of its body with
/// the definitions its last assignments gave them, and a `RAISE EXCEPTION`
/// beside the end leaves the body with the same definitions.
#[test]
fn the_end_of_a_function_with_output_parameters_returns_what_they_hold() {
    let signature = Signature {
        name: "acting_installation".to_owned(),
        parameters: vec![Some("namespace_id".to_owned()), Some("id".to_owned())],
        kind: FunctionKind::Plain,
    };
    let block = embedded_sql(
        "BEGIN
          namespace_id := NULLIF(current_setting('app.installation_namespace_id', true), '')::UUID;
          id := NULLIF(current_setting('app.installation_id', true), '')::UUID;
          IF (namespace_id IS NULL) <> (id IS NULL) THEN
           RAISE EXCEPTION 'incomplete installation identity' USING ERRCODE = '22023';
          END IF;
         END",
    )
    .unwrap();
    let mut domain = ReachingDefinitions::new();
    let flow = walk(
        &block,
        &signature,
        Transactions::Refused,
        Ending::Returns,
        &mut Schema::default(),
        &mut domain,
    )
    .unwrap();
    let assigned = [
        read(
            "namespace_id",
            &["NULLIF(current_setting('app.installation_namespace_id', true), '')::UUID"],
        ),
        read("id", &["NULLIF(current_setting('app.installation_id', true), '')::UUID"]),
    ];
    let returns: Vec<_> = flow
        .returns()
        .map(|(at, state)| (matches!(at, Return::End), holding(state, &domain, &signature)))
        .collect();
    assert_eq!(returns, [(true, assigned.to_vec())]);
    let raises: Vec<_> = flow
        .escapes()
        .filter_map(|(at, state)| {
            let Escape::Raises(Step::Node(node)) = at else { return None };
            Some((matches!(node.kind, NodeKind::Raise(_)), holding(state, &domain, &signature)))
        })
        .collect();
    assert_eq!(raises, [(true, assigned.to_vec())]);
}

/// A `CALL` reaching no single procedure may write back to a variable passed
/// in parentheses, under a cast or by position, and to no computed argument.
#[test]
fn a_call_of_no_single_procedure_may_write_every_variable_argument() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT 1'; o text := 'SELECT 2';
             BEGIN CALL fill((s), o::text, $1, q || q); EXECUTE s USING o, p, q; END"
        ),
        [vec![
            read("s", &["'SELECT 1'", "argument 0 of CALL fill((s), o::TEXT, $1, q || q)"]),
            read("o", &["'SELECT 2'", "argument 1 of CALL fill((s), o::TEXT, $1, q || q)"]),
            read("p", &["incoming", "argument 2 of CALL fill((s), o::TEXT, $1, q || q)"]),
            read("q", &["incoming"]),
        ]]
    );
}

/// A `CALL` reaching one procedure surely writes the arguments it writes
/// back to, and leaves the rest as they were.
#[test]
fn a_call_of_one_procedure_writes_its_output_arguments() {
    assert_eq!(
        reaching_calling(
            "DECLARE s text := 'SELECT 1'; o text := 'SELECT 2'; r text := 'SELECT 3';
             BEGIN CALL fill(s, o, r); EXECUTE s USING o, r; END",
            &[("CALL fill(s, o, r)", &[false, true, true])],
        ),
        [vec![
            read("s", &["'SELECT 1'"]),
            read("o", &["argument 1 of CALL fill(s, o, r)"]),
            read("r", &["argument 2 of CALL fill(s, o, r)"]),
        ]]
    );
}

/// `GET DIAGNOSTICS` and `GET STACKED DIAGNOSTICS` assign each target the
/// item it names.
#[test]
fn diagnostics_assign_the_items_they_name() {
    assert_eq!(
        reaching(
            "DECLARE a text; b text; c text; d text;
             BEGIN
              GET DIAGNOSTICS a = PG_ROUTINE_OID, b = PG_CONTEXT;
              BEGIN
               PERFORM 1 / q;
              EXCEPTION WHEN OTHERS THEN
               GET STACKED DIAGNOSTICS c = RETURNED_SQLSTATE, d = PG_EXCEPTION_CONTEXT;
               EXECUTE a USING b, c, d;
              END;
             END"
        ),
        [vec![
            read("a", &["RoutineOid"]),
            read("b", &["Context"]),
            read("c", &["ReturnedSqlstate"]),
            read("d", &["ExceptionContext"]),
        ]]
    );
}

/// A lone row target takes the whole row, a row-typed parameter included,
/// while a lone scalar target takes the first output.
#[test]
fn a_lone_row_target_takes_the_whole_row() {
    let signature = Signature {
        name: "rows".to_owned(),
        parameters: vec![Some("r".to_owned()), Some("p".to_owned())],
        kind: FunctionKind::Plain,
    };
    assert_eq!(
        reaching_with(
            "BEGIN
              FOR i IN 1..2 LOOP
               SELECT * INTO r FROM t;
               SELECT id INTO i FROM t;
               EXECUTE p USING r, i;
              END LOOP;
             END",
            &signature,
            Transactions::Refused,
            Schema { rows: vec![1], calls: BTreeMap::new() },
        ),
        [vec![
            read("p", &["incoming"]),
            read("r", &["Row First { strict: false } of SELECT * FROM t"]),
            read("i", &["Ordinal(0) First { strict: false } of SELECT id FROM t"]),
        ]]
    );
}

/// `RETURN NEXT` and `RETURN QUERY` carry on, and `RETURN QUERY EXECUTE` is
/// a site of its own.
#[test]
fn set_returning_statements_carry_on() {
    assert_eq!(
        reaching(
            "DECLARE s text := 'SELECT ' || p;
             BEGIN
              RETURN NEXT s;
              s := 'SELECT ' || q;
              RETURN QUERY SELECT s;
              s := 'SELECT 1';
              RETURN QUERY EXECUTE s USING q;
             END"
        ),
        [vec![read("s", &["'SELECT 1'"]), read("q", &["incoming"])]]
    );
}

/// A write to a name the body declares nowhere stops the walk, naming the
/// target.
#[test]
fn a_write_to_an_undeclared_name_is_unresolvable() {
    for body in [
        "BEGIN missing := 1; END",
        "BEGIN SELECT 1 INTO missing; END",
        "BEGIN GET DIAGNOSTICS missing = ROW_COUNT; END",
    ] {
        let block = embedded_sql(body).unwrap();
        let mut domain = ReachingDefinitions::new();
        let walked = walk(
            &block,
            &run(),
            Transactions::Refused,
            Ending::Raises,
            &mut Schema::default(),
            &mut domain,
        );
        assert!(
            matches!(
                &walked,
                Err(sqlparser_plpgsql_dataflow::Error::UnresolvedTarget { name })
                    if name == "missing"
            ),
            "{body}: {walked:?}"
        );
    }
}

/// The statements processing rows set `FOUND`, a `SELECT ... INTO` before
/// its targets, and a `FOR` loop as control leaves it, while a utility
/// statement, `EXECUTE`, `GET DIAGNOSTICS`, `CALL` and `WHILE` leave it as
/// it was. Inside a `FOR` loop, `FOUND` holds what the statements before it
/// and in it left.
#[test]
fn row_processing_statements_and_for_loops_set_found() {
    assert_eq!(
        reaching(
            "DECLARE c refcursor; s text; n integer;
             BEGIN
              EXECUTE 'SELECT 1' USING FOUND;
              PERFORM 1;
              CREATE TEMP TABLE z (a integer);
              EXECUTE 'SELECT 2';
              GET DIAGNOSTICS n = ROW_COUNT;
              CALL fill(s);
              WHILE q > 0 LOOP q := q - 1; END LOOP;
              EXECUTE 'SELECT 3' USING FOUND;
              FOR i IN 1..q LOOP EXECUTE 'SELECT 4' USING FOUND; DELETE FROM t; END LOOP;
              EXECUTE 'SELECT 5' USING FOUND;
              OPEN c FOR SELECT name FROM t;
              FETCH c INTO s;
              EXECUTE 'SELECT 6' USING FOUND;
              MOVE c;
              EXECUTE 'SELECT 7' USING FOUND;
              RETURN QUERY EXECUTE 'SELECT 8';
              EXECUTE 'SELECT 9' USING FOUND;
             END"
        ),
        [
            vec![read("found", &["incoming"])],
            vec![],
            vec![read("found", &["Rows of SELECT 1"])],
            vec![read("found", &["Rows of SELECT 1", "Rows of DELETE FROM t"])],
            vec![read("found", &["Iterated"])],
            vec![read("found", &["Rows"])],
            vec![read("found", &["Rows"])],
            vec![],
            vec![read("found", &["Rows of EXECUTE 'SELECT 8'"])],
        ]
    );
}

/// A `STRICT` query finding no row sets `FOUND` before it raises, so its
/// handler reads the `FOUND` it set beside the one before it.
#[test]
fn a_strict_query_sets_found_before_it_raises() {
    assert_eq!(
        reaching(
            "DECLARE s text;
             BEGIN
              SELECT name INTO STRICT s FROM t;
             EXCEPTION WHEN no_data_found THEN
              EXECUTE s USING FOUND;
             END"
        ),
        [vec![read("s", &["null"]), read("found", &["incoming", "Rows of SELECT name FROM t"]),]]
    );
}

/// `EXIT` and `CONTINUE` naming an outer loop or block leave every loop they
/// pass through as its end does, setting `FOUND` and giving a cursor
/// variable its null back.
#[test]
fn an_exit_passing_through_a_for_loop_sets_found_and_releases_its_portal() {
    assert_eq!(
        reaching(
            "DECLARE c CURSOR FOR SELECT name FROM t;
             BEGIN
              c := NULL;
              PERFORM 1;
              <<outer>> LOOP
               FOR r IN c LOOP EXIT outer; END LOOP;
              END LOOP;
              EXECUTE 'CLOSE ' || quote_ident(c) USING FOUND;
              <<repeated>> FOR j IN 1..2 LOOP
               PERFORM 1;
               FOR r IN c LOOP CONTINUE repeated; END LOOP;
               EXECUTE 'SELECT 1' USING FOUND;
              END LOOP;
              EXECUTE 'CLOSE ' || quote_ident(c) USING FOUND;
             END"
        ),
        [
            vec![read("c", &["NULL"]), read("found", &["Iterated"])],
            vec![read("found", &["Iterated"])],
            vec![read("c", &["NULL"]), read("found", &["Iterated"])],
        ]
    );
}

/// A later target whose value fails to convert raises with the earlier
/// targets of its step already assigned.
#[test]
fn a_handler_sees_the_targets_assigned_before_one_that_raised() {
    assert_eq!(
        reaching(
            "DECLARE a integer := 0; b integer := 0;
             BEGIN
              BEGIN
               SELECT 1, 'y' INTO a, b;
              EXCEPTION WHEN invalid_text_representation THEN
               EXECUTE 'SELECT 1' USING a, b;
              END;
             END"
        ),
        [vec![
            read("a", &["0", "Ordinal(0) First { strict: false } of SELECT 1, 'y'"]),
            read("b", &["0"]),
        ]]
    );
}
