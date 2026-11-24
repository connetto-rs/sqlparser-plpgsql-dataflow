//! What the walk carries through a body, and how each step changes it.

use sqlparser::ast::Query;
use sqlparser_expr_eval::Outcomes;
use sqlparser_plpgsql::embedded::{Declaration, Loop, Node};

use crate::Write;

/// What the walk carries and how the body's steps change it.
///
/// The walk owns every control-flow rule of PL/pgSQL. A domain only says
/// what a state is, how paths join, what a write and a test do to a state,
/// and where a raise may happen. A point no path reaches has no state, which
/// sits below every state of the domain.
pub trait Domain<'body> {
    /// What the walk holds at one point of the body.
    type State: Clone + PartialEq;
    /// The error a domain may stop the walk with.
    type Error;

    /// The state on entering the body.
    ///
    /// # Errors
    ///
    /// Returns the domain's error when it cannot tell the state.
    fn entry(&mut self) -> Result<Self::State, Self::Error>;

    /// Adds what `from` may hold to `into`, where two paths meet.
    fn join(&self, into: &mut Self::State, from: &Self::State);

    /// The state at the head of a loop for its next round, from the head of
    /// round `round`, counted from 0, and `next`, the join of the loop's
    /// entry and every path back to its head.
    ///
    /// The answer holds what both `head` and `next` may hold, and no loop
    /// takes infinitely many rounds to stop changing it.
    fn widen(&self, head: &Self::State, next: Self::State, round: usize) -> Self::State;

    /// Applies `write` to `state`, its value read where `inputs` holds.
    ///
    /// A step assigning several targets reads every value before it assigns
    /// any, so `inputs` is the state before the step's first write. A loop's
    /// writes read what its control evaluated once on entry, so their
    /// `inputs` is the state the loop is entered with.
    ///
    /// # Errors
    ///
    /// Returns the domain's error when it cannot read the write.
    fn write(
        &mut self,
        write: &Write<'body>,
        inputs: &Self::State,
        state: &mut Self::State,
    ) -> Result<(), Self::Error>;

    /// What remains of `state` on the paths where `test` takes one of
    /// `outcomes`, `None` when no path does.
    ///
    /// # Errors
    ///
    /// Returns the domain's error when it cannot read the test.
    fn assume(
        &mut self,
        test: Test<'body>,
        outcomes: Outcomes,
        state: Self::State,
    ) -> Result<Option<Self::State>, Self::Error>;

    /// Whether running `step` from `state` may raise an error.
    ///
    /// # Errors
    ///
    /// Returns the domain's error when it cannot read the step.
    fn may_raise(&mut self, step: Step<'body>, state: &Self::State) -> Result<bool, Self::Error>;
}

/// A test that splits the paths of a body by its outcome.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Test<'body> {
    /// The condition of an `IF`, `ELSIF`, searched `CASE`, `WHILE`, `EXIT
    /// WHEN`, `CONTINUE WHEN` or `ASSERT`, as the `SELECT` evaluating it.
    Condition(&'body Query),
    /// One `WHEN` of a `CASE` with a subject, which holds when the subject
    /// equals one of the values the `WHEN` lists.
    Match {
        /// The `SELECT` evaluating the subject.
        subject: &'body Query,
        /// The `SELECT` evaluating the values the `WHEN` lists.
        values: &'body Query,
    },
}

/// A point of a body where a raise may happen.
#[derive(Clone, Copy, Debug)]
pub enum Step<'body> {
    /// A declaration, evaluating its default as its block starts.
    Declaration(&'body Declaration),
    /// A step starting, with every condition, bound, query and value it
    /// evaluates before it hands control on.
    Node(&'body Node),
    /// The start of one round of a loop, which evaluates a `WHILE` condition
    /// or reads the next row or element.
    Iteration(&'body Loop),
}
