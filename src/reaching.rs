//! Reaching definitions, the writes that may have given each variable what
//! it holds at each point of a body.

use alloc::{
    collections::{BTreeMap, BTreeSet, btree_map::Entry},
    vec::Vec,
};
use core::convert::Infallible;

use sqlparser_expr_eval::Outcomes;
use sqlparser_plpgsql::embedded::BoundCursor;

use crate::{Domain, Rows, Source, Step, Test, Write, walk::write_address, write::opened};

/// The definitions each variable may hold, by [`Name::id`], where a
/// variable missing holds its entry definition alone.
///
/// [`Name::id`]: sqlparser_plpgsql::namespace::Name::id
pub type State = BTreeMap<usize, BTreeSet<Slot>>;

/// A definition a variable may hold.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Slot {
    /// What the variable holds as the body starts.
    Entry,
    /// The definition at this index of
    /// [`ReachingDefinitions::definitions`].
    Written(usize),
}

/// A definition one write makes each time the walk passes it.
#[derive(Clone, Debug)]
pub struct Definition<'body> {
    /// The write.
    pub write: Write<'body>,
    /// The join of the states its value is read in, which for a loop's
    /// writes is the state the loop is entered with.
    pub inputs: State,
}

/// The reaching definitions [`Domain`], whose state is the [`State`] the
/// walk carries, and which keeps every definition it meets.
///
/// A write surely assigning the whole variable replaces every definition it
/// held, and any other write adds its definition beside them. A cursor `FOR`
/// loop's [`Source::PortalReleased`] instead removes the portal name the
/// loop gave. A test leaves the state as it is, and a raise may happen at
/// every step.
#[derive(Clone, Debug, Default)]
pub struct ReachingDefinitions<'body> {
    definitions: Vec<Definition<'body>>,
    /// The index of each definition, by the address of its write, the
    /// target's position and whether it is the null a loop over no row
    /// assigns.
    keys: BTreeMap<(usize, usize, bool), usize>,
    cursors: BTreeMap<usize, &'body BoundCursor>,
}

impl<'body> ReachingDefinitions<'body> {
    /// A domain that has met no definition yet.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Every definition the walk met, in the order it first passed each
    /// write, which is the body's order.
    #[must_use]
    pub fn definitions(&self) -> &[Definition<'body>] {
        &self.definitions
    }

    /// The cursor declared with its query that each cursor variable opens,
    /// by the variable's [`Name::id`], as the first `OPEN` or `FOR` loop the
    /// walk passes opening it names it.
    ///
    /// [`Name::id`]: sqlparser_plpgsql::namespace::Name::id
    #[must_use]
    pub fn cursors(&self) -> &BTreeMap<usize, &'body BoundCursor> {
        &self.cursors
    }

    /// The index of the definition `write` makes, made on the walk's first
    /// pass over it, with `inputs` added to what reaches it.
    fn define(&mut self, write: &Write<'body>, inputs: &State) -> usize {
        match self.keys.entry(key(write)) {
            Entry::Occupied(entry) => {
                let index = *entry.get();
                merge(&mut self.definitions[index].inputs, inputs);
                index
            }
            Entry::Vacant(entry) => {
                self.definitions.push(Definition { write: write.clone(), inputs: inputs.clone() });
                *entry.insert(self.definitions.len() - 1)
            }
        }
    }
}

/// What tells the definitions of one write apart.
fn key(write: &Write<'_>) -> (usize, usize, bool) {
    let empty = matches!(
        write.source,
        Source::Query { rows: Rows::Empty, .. } | Source::Dynamic { rows: Rows::Empty, .. }
    );
    (write_address(write.at), write.position, empty)
}

impl<'body> Domain<'body> for ReachingDefinitions<'body> {
    type State = State;
    type Error = Infallible;

    fn entry(&mut self) -> Result<State, Infallible> {
        Ok(State::new())
    }

    fn join(&self, into: &mut State, from: &State) {
        merge(into, from);
    }

    fn widen(&self, head: &State, mut next: State, _round: usize) -> State {
        // Each variable holds one of finitely many definitions, so the join
        // stops growing.
        merge(&mut next, head);
        next
    }

    fn write(
        &mut self,
        write: &Write<'body>,
        inputs: &State,
        state: &mut State,
    ) -> Result<(), Infallible> {
        if write.source == Source::PortalReleased {
            // The null given back removes the portal name the loop gave.
            let portal = (write_address(write.at), write.position, false);
            if let Some(&index) = self.keys.get(&portal)
                && let Some(slots) = state.get_mut(&write.variable.id())
            {
                slots.remove(&Slot::Written(index));
            }
            return Ok(());
        }
        if write.source == Source::PortalName
            && let Some(cursor) = opened(write)
        {
            self.cursors.entry(write.variable.id()).or_insert(cursor);
        }
        let index = self.define(write, inputs);
        let slots =
            state.entry(write.variable.id()).or_insert_with(|| BTreeSet::from([Slot::Entry]));
        if write.surely && write.part.is_empty() {
            slots.clear();
        }
        slots.insert(Slot::Written(index));
        Ok(())
    }

    fn assume(
        &mut self,
        _test: Test<'body>,
        _outcomes: Outcomes,
        state: State,
    ) -> Result<Option<State>, Infallible> {
        Ok(Some(state))
    }

    fn may_raise(&mut self, _step: Step<'body>, _state: &State) -> Result<bool, Infallible> {
        Ok(true)
    }
}

/// Adds the definitions `from` holds to `state`.
fn merge(state: &mut State, from: &State) {
    // A variable missing from either side holds its entry definition there.
    for (variable, slots) in state.iter_mut() {
        if !from.contains_key(variable) {
            slots.insert(Slot::Entry);
        }
    }
    for (variable, slots) in from {
        state.entry(*variable).or_insert_with(|| BTreeSet::from([Slot::Entry])).extend(slots);
    }
    state.retain(|_, slots| !(slots.len() == 1 && slots.contains(&Slot::Entry)));
}
