use pear::parsers::*;
use pear::combinators::*;
use pear::macros::{parse, parser, switch};
use pear::input::{Pear, Text};

use crate::value::{Value, Dict};

type Input<'a> = Pear<Text<'a>>;
type Result<'a, T> = pear::input::Result<T, Input<'a>>;

#[inline(always)]
pub fn is_whitespace(&byte: &char) -> bool {
    byte.is_ascii_whitespace()
}

#[inline(always)]
fn is_not_separator(&byte: &char) -> bool {
    match byte {
        ',' | '{' | '}' | '[' | ']' => false,
        _ => true
    }
}

#[inline(always)]
pub fn any<T>(_: &T) -> bool { true }

// TODO: Be more permissive here?
#[inline(always)]
fn is_ident_char(&byte: &char) -> bool {
    byte.is_ascii_alphanumeric() || byte == '_' || byte == '-'
}

#[parser]
fn key<'a>(input: &mut Input<'a>) -> Result<'a, String> {
    Ok(take_some_while(is_ident_char)?.to_string())
}

#[parser]
fn key_value<'a>(input: &mut Input<'a>) -> Result<'a, (String, Value)> {
    let key = (surrounded(key, is_whitespace)?, eat('=')?).0.to_string();
    (key, surrounded(value, is_whitespace)?)
}

#[parser]
fn array<'a>(input: &mut Input<'a>) -> Result<'a, Vec<Value>> {
    Ok(delimited_collect('[', value, ',', ']')?)
}

#[parser]
fn dict<'a>(input: &mut Input<'a>) -> Result<'a, Dict> {
    Ok(delimited_collect('{', key_value, ',', '}')?)
}

#[parser]
fn value<'a>(input: &mut Input<'a>) -> Result<'a, Value> {
    skip_while(is_whitespace)?;
    let val = switch! {
        eat_slice("true") => Value::from(true),
        eat_slice("false") => Value::from(false),
        peek('{') => Value::from(dict()?),
        peek('[') => Value::from(array()?),
        peek('"') => Value::from(delimited('"', any, '"')?.to_string()),
        peek('\'') => Value::from((eat('\'')?, eat_any()?, eat('\'')?).1),
        _ => {
            let value = take_while(is_not_separator)?;
            if value.contains('.') {
                if let Ok(float) = value.parse::<f64>() {
                    return Ok(Value::from(float));
                }
            }

            if let Ok(int) = value.parse::<usize>() {
                Value::from(int)
            } else if let Ok(int) = value.parse::<isize>() {
                Value::from(int)
            } else {
                Value::from(value.to_string())
            }
        }
    };

    skip_while(is_whitespace)?;
    val
}

impl std::str::FromStr for Value {
    type Err = std::convert::Infallible;

    fn from_str(s: &str) -> std::result::Result<Self, std::convert::Infallible> {
        Ok(parse!(value: Text::from(s))
            .unwrap_or_else(|_| Value::from(s.to_string())))
    }
}
