#![doc = include_str!("../README.md")]
// Tests link the standard library whatever the features, as their harness does.
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

extern crate alloc;

mod domain;
pub mod reaching;
pub mod values;
mod walk;
mod write;

pub use domain::{Domain, Step, Test};
pub use walk::{Catalog, Error, Flow, Transactions, walk};
pub use write::{Found, Output, Part, Rows, Source, Write};
