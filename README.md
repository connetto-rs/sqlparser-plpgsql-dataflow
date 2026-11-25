# sqlparser-plpgsql-dataflow

[![CI](https://github.com/connetto-rs/sqlparser-plpgsql-dataflow/actions/workflows/ci.yml/badge.svg)](https://github.com/connetto-rs/sqlparser-plpgsql-dataflow/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/connetto-rs/sqlparser-plpgsql-dataflow/graph/badge.svg)](https://codecov.io/gh/connetto-rs/sqlparser-plpgsql-dataflow)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/connetto-rs/sqlparser-plpgsql-dataflow/blob/main/LICENSE)
[![crates.io](https://img.shields.io/crates/v/sqlparser-plpgsql-dataflow.svg)](https://crates.io/crates/sqlparser-plpgsql-dataflow)
[![docs.rs](https://docs.rs/sqlparser-plpgsql-dataflow/badge.svg)](https://docs.rs/sqlparser-plpgsql-dataflow)

Forward dataflow analysis over the PL/pgSQL bodies [`sqlparser-plpgsql`](https://github.com/connetto-rs/sqlparser-plpgsql) reads. [`walk`] follows a body through its blocks, branches, loops, exception handlers, `EXIT`, `CONTINUE`, `RETURN`, `RAISE` and transaction control, carrying the state a [`Domain`] defines, and answers the state reaching each statement and expression. The crate is `no_std`, needing only `alloc`.

A domain says what a state is, how paths join, what a write and a test do to a state and where a raise may happen. Loops run until the state at their head stops changing, through the domain's widening. [`reaching::ReachingDefinitions`] is the domain of the writes that may have given each variable its value. [`values::analyze`] walks a body with the guarantees [`sqlparser-expr-eval`](https://github.com/connetto-rs/sqlparser-expr-eval) carries through one expression, so [`values::Analysis::truth_under`] tells what an expression evaluates to given what each variable may hold where the body reaches it. Whatever only a catalog knows, whether a variable holds a row and what a `CALL` writes back, comes through [`Catalog`].

```rust
use sqlparser::ast::Statement;
use sqlparser_plpgsql::{
    embedded::NodeKind,
    embedded_sql,
    namespace::{FunctionKind, Name, Signature, Sql},
};
use sqlparser_plpgsql_dataflow::{
    Catalog, Source, Transactions,
    reaching::{ReachingDefinitions, Slot},
    walk,
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

let block = embedded_sql("DECLARE x int := 1; BEGIN IF p THEN x := 2; END IF; RETURN x; END")?;
let signature = Signature {
    name: "f".into(),
    parameters: vec![Some("p".into())],
    kind: FunctionKind::Plain,
};
let mut domain = ReachingDefinitions::new();
let flow = walk(&block, &signature, Transactions::Refused, &mut Scalars, &mut domain)?;

let NodeKind::Return { value: Some(returned) } = &block.statements[1].kind else {
    unreachable!()
};
let reaching = flow.at(Sql::Expression(returned)).expect("a path reaches the RETURN");
// `x` holds its default where `p` is not true, and 2 where it is.
let values: Vec<String> = reaching
    .values()
    .flatten()
    .map(|slot| {
        let Slot::Written(index) = slot else { unreachable!() };
        let Source::Value(value) = domain.definitions()[*index].write.source else { unreachable!() };
        value.to_string()
    })
    .collect();
assert_eq!(values, ["SELECT 1", "SELECT 2"]);
# Ok::<(), Box<dyn std::error::Error>>(())
```
