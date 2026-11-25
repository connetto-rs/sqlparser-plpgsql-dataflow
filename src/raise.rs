//! The SQLSTATE a raise reports, and the handlers that catch it.

use alloc::borrow::Cow;

use sqlparser::ast::{Expr, Value};
use sqlparser_plpgsql::{
    condition::errcode,
    embedded::{self, Condition, Handler, Raise, RaiseOptionKind},
};
use sqlstate::{SqlState, pg};

/// The SQLSTATE `raise`, a `RAISE EXCEPTION`, reports, `None` when only
/// running it tells.
///
/// A `RAISE` without a condition, format or option rethrows the error its
/// handler caught. An option whose value is no string literal may be null,
/// and an option written twice, `MESSAGE` beside a format or `ERRCODE`
/// beside a condition each raise `syntax_error` instead. An `ERRCODE` naming
/// no condition raises `undefined_object`.
pub(crate) fn reported(raise: &Raise) -> Option<SqlState> {
    if raise.condition.is_none() && raise.format.is_none() && raise.options.is_empty() {
        return None;
    }
    let mut errcode_text = None;
    for (index, option) in raise.options.iter().enumerate() {
        let Cow::Borrowed(Expr::Value(value)) = embedded::expression(&option.value) else {
            return None;
        };
        let Value::SingleQuotedString(text) = &value.value else { return None };
        let repeated = raise.options[..index].iter().any(|earlier| earlier.kind == option.kind);
        let conflicts = match option.kind {
            RaiseOptionKind::Message => raise.format.is_some(),
            RaiseOptionKind::Errcode => raise.condition.is_some(),
            _ => false,
        };
        if repeated || conflicts {
            return Some(pg::SYNTAX_ERROR);
        }
        if option.kind == RaiseOptionKind::Errcode {
            errcode_text = Some(text.as_str());
        }
    }
    let code = match (errcode_text, raise.condition) {
        (Some(text), _) => errcode(text).unwrap_or(Some(pg::UNDEFINED_OBJECT)),
        (None, Some(condition)) => condition.sqlstate(),
        (None, None) => None,
    };
    Some(code.unwrap_or(pg::RAISE_EXCEPTION))
}

/// Whether one of `handlers` catches an error reporting `code`.
///
/// A condition catches its own SQLSTATE and, when it names a class, every
/// SQLSTATE of the class. `others` catches every error but `query_canceled`
/// and `assert_failure`.
pub(crate) fn caught(handlers: &[Handler], code: SqlState) -> bool {
    let catches = |condition: SqlState| {
        condition == code || (condition.subclass() == "000" && condition.class() == code.class())
    };
    handlers.iter().flat_map(|handler| &handler.conditions).any(|condition| {
        match *condition {
            Condition::Name(name) => name.sqlstates().any(catches),
            Condition::Sqlstate(condition) => catches(condition),
            Condition::Others => code != pg::QUERY_CANCELED && code != pg::ASSERT_FAILURE,
        }
    })
}
