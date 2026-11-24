//! What one write of a body assigns, and where the value comes from.

use alloc::{string::String, vec::Vec};

use sqlparser::ast::{Query, Statement};
use sqlparser_plpgsql::{
    embedded::{BoundCursor, DiagnosticsKind, Dynamic, Loop},
    namespace::{self, Name, Sql},
};

/// A value the walk assigns to one variable, or to part of one.
#[derive(Clone, Debug)]
pub struct Write<'body> {
    /// The declaration or step that writes.
    pub at: namespace::Write<'body>,
    /// The target's position among the targets the step writes, from 0.
    ///
    /// A cursor `FOR` loop writes its record at 0 and its cursor variable
    /// at 1. `FOUND`, which a step writes besides its targets, takes the
    /// position after them.
    pub position: usize,
    /// The variable written.
    pub variable: Name,
    /// The part of the variable written, empty for the whole of it.
    pub part: Vec<Part<'body>>,
    /// Whether the write surely assigns, so the target holds nothing it held
    /// before. A `CALL` that may reach no single procedure, and `OPEN` of a
    /// cursor variable that may already name a portal, may leave the
    /// target as it was.
    pub surely: bool,
    /// Where the value comes from.
    pub source: Source<'body>,
    /// The statement or expression the value is read in, whose names
    /// [`Block::sites`](sqlparser_plpgsql::embedded::Block::sites) answers,
    /// for a source that reads any.
    pub site: Option<Sql<'body>>,
}

/// One step into the variable a [`Write`] assigns.
#[derive(Clone, Debug, PartialEq)]
pub enum Part<'body> {
    /// A field, as PostgreSQL stores its name.
    Field(String),
    /// `[index]`, as the `SELECT` evaluating the index.
    Index(&'body Query),
    /// `[lower:upper]`, each bound as the `SELECT` evaluating it.
    Slice {
        /// The first bound, unless omitted.
        lower: Option<&'body Query>,
        /// The second bound, unless omitted.
        upper: Option<&'body Query>,
    },
}

/// Where the value a [`Write`] assigns comes from, as far as the body tells
/// without a catalog.
#[derive(Clone, Debug, PartialEq)]
pub enum Source<'body> {
    /// The null a declaration without a default gives its variable.
    Null,
    /// The value of an expression, which an assignment or a declaration's
    /// default gives, as the `SELECT` evaluating it.
    Value(&'body Query),
    /// The cursor's own name, which a cursor declared with its query holds on
    /// entering its block.
    CursorName,
    /// A portal name PostgreSQL generates, which `OPEN` and a cursor `FOR`
    /// loop give a cursor variable holding null.
    PortalName,
    /// The null a cursor `FOR` loop gives back, as it ends, to the cursor
    /// variable it named its portal.
    PortalReleased,
    /// An output of a query PostgreSQL plans with the body, which `SELECT
    /// ... INTO`, `INSERT ... RETURNING ... INTO`, a `FOR` loop over a query
    /// and a cursor `FOR` loop assign.
    Query {
        /// The query, its `INTO` clause dropped.
        statement: &'body Statement,
        /// The part of each row assigned.
        output: Output,
        /// The rows assigned.
        rows: Rows,
    },
    /// An output of SQL the body builds at run time, which `EXECUTE ... INTO`
    /// and `FOR ... IN EXECUTE` assign.
    Dynamic {
        /// The command and its arguments.
        dynamic: &'body Dynamic,
        /// The part of each row assigned.
        output: Output,
        /// The rows assigned.
        rows: Rows,
    },
    /// The row `FETCH` reads from the portal the cursor variable names, or a
    /// null when none is left.
    Cursor {
        /// The cursor variable.
        cursor: Name,
        /// The part of the row assigned.
        output: Output,
    },
    /// What a procedure's `INOUT` or `OUT` parameter returns to the variable
    /// `CALL` passes there.
    Call {
        /// The `CALL`.
        call: &'body Statement,
        /// The argument's position among those written, from 0.
        argument: usize,
    },
    /// What `GET DIAGNOSTICS` reads.
    Diagnostics(DiagnosticsKind),
    /// Every integer of a `FOR` loop's range in turn, from the first bound
    /// written to the second.
    LoopIndex {
        /// Whether `REVERSE` counts down from `lower` to `upper`.
        reverse: bool,
        /// The first bound written, where the count starts.
        lower: &'body Query,
        /// The second bound written, past which the count stops.
        upper: &'body Query,
        /// The `BY` step.
        step: Option<&'body Query>,
    },
    /// Every element or slice of an array in turn, which `FOREACH` assigns.
    ArrayElement {
        /// The `SELECT` evaluating the array.
        array: &'body Query,
        /// The `SLICE` dimension, 0 for single elements.
        slice: u32,
        /// The part of each element assigned.
        output: Output,
    },
    /// Whether the step found a row, which it gives `FOUND`.
    Found(Found),
}

/// What a step finding a row means, for the [`Source::Found`] it writes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Found {
    /// The statement processed a row. `PERFORM`, `SELECT`, `INSERT`,
    /// `UPDATE`, `DELETE`, `MERGE`, `FETCH`, `MOVE` and `RETURN QUERY` write
    /// it, a statement with `INTO` other than `FETCH` before it assigns its
    /// targets.
    Rows,
    /// The loop ran a round. A `FOR` or `FOREACH` loop writes it as control
    /// leaves the loop, by `EXIT` and `CONTINUE` passing through it too.
    Iterated,
}

/// The part of a row or element a target takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Output {
    /// The column or field at this position, from 0.
    Ordinal(usize),
    /// The whole row or element, which a lone target holding a row takes, as
    /// does the lone target of `FOREACH`.
    Row,
}

/// Which rows of a query a write takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rows {
    /// The first row, or a null when there is none. `STRICT` makes no row
    /// and more than one row an error instead.
    First {
        /// Whether `STRICT` is written.
        strict: bool,
    },
    /// Every row in turn, as a loop takes them.
    Each,
    /// The null a loop over no row assigns.
    Empty,
}

/// The cursor a [`Source::PortalName`] write opens, when it is declared with
/// its query.
pub(crate) fn opened<'body>(write: &Write<'body>) -> Option<&'body BoundCursor> {
    use sqlparser_plpgsql::embedded::{LoopControl, NodeKind, Open};
    let namespace::Write::Node(node) = write.at else {
        return None;
    };
    match &node.kind {
        NodeKind::Open(Open::Bound(cursor))
        | NodeKind::Loop(Loop { control: LoopControl::Cursor { cursor, .. }, .. }) => Some(cursor),
        _ => None,
    }
}
