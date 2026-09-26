use std::borrow::Cow;

use crate::value::{Value, Dict, escape::escape};

use super::Empty;

struct Parser<'a> {
    cursor: &'a str,
}

#[derive(Debug)]
#[allow(dead_code)]
pub enum Error {
    Expected(Value),
    Escape(super::escape::Error),
    Eof,
}

type Result<T> = std::result::Result<T, Error>;

impl<'a> Parser<'a> {
    fn new(cursor: &'a str) -> Self {
        Self { cursor }
    }

    fn peek(&self, c: char) -> bool {
        self.peek_next() == Some(c)
    }

    fn eof(&self) -> bool {
        self.cursor.is_empty()
    }

    fn peek_next(&self) -> Option<char> {
        self.cursor.chars().next()
    }

    #[inline]
    fn eat_if<F>(&mut self, f: F) -> Option<char>
        where F: FnOnce(&char) -> bool,
    {
        match self.cursor.chars().next() {
            Some(ch) if f(&ch) => {
                self.cursor = &self.cursor[ch.len_utf8()..];
                Some(ch)
            }
            _ => None,
        }
    }

    fn eat(&mut self, c: char) -> Result<char> {
        self.eat_if(|&ch| ch == c)
            .ok_or_else(|| Error::Expected(Value::from(c)))
    }

    fn eat_any(&mut self) -> Result<char> {
        self.eat_if(|_| true).ok_or(Error::Eof)
    }

    fn skip_whitespace(&mut self) {
        self.cursor = self.cursor.trim_start();
    }

    fn substr<F>(&mut self, f: F) -> Result<&'a str>
        where F: FnMut(&char) -> bool,
    {
        let len = self.cursor.chars()
            .take_while(f)
            .map(|c| c.len_utf8())
            .sum();

        let (substring, rest) = self.cursor.split_at(len);
        self.cursor = rest;
        Ok(substring)
    }

    fn quoted_char(&mut self) -> Result<char> {
        self.eat('\'')?;
        let ch = self.eat_any()?;
        self.eat('\'')?;
        Ok(ch)
    }

    fn quoted_str(&mut self) -> Result<Cow<'a, str>> {
        self.eat('"')?;

        let mut is_escaped = false;
        let inner = self.substr(|&c: &char| -> bool {
            if is_escaped { is_escaped = false; return true; }
            if c == '\\' { is_escaped = true; return true; }
            c != '"'
        })?;

        self.eat('"')?;
        escape(inner).map_err(Error::Escape)
    }

    fn key(&mut self) -> Result<Cow<'a, str>> {
        #[inline(always)]
        fn is_ident_char(&byte: &char) -> bool {
            byte.is_ascii_alphanumeric() || byte == '_' || byte == '-'
        }

        if self.peek('"') {
            self.quoted_str()
        } else {
            self.substr(is_ident_char).map(Cow::Borrowed)
        }
    }

    fn delimited<T, V, F>(&mut self, start: char, end: char, value: F) -> Result<T>
        where T: Extend<V> + Default, F: Fn(&mut Self) -> Result<V>,
    {
        let mut collection = T::default();
        self.eat(start)?;
        self.skip_whitespace();

        while !self.peek(end) {
            collection.extend(Some(value(self)?));

            self.skip_whitespace();
            if self.eat(',').is_err() {
                break;
            }

            self.skip_whitespace();
        }

        self.eat(end)?;
        Ok(collection)
    }

    fn dict(&mut self) -> Result<Dict> {
        self.delimited('{', '}', |parser| {
            let key = parser.key()?;
            (parser.skip_whitespace(), parser.eat('=')?, parser.skip_whitespace());
            let value = parser.value()?;
            Ok((key.to_string(), value))
        })
    }

    fn array(&mut self) -> Result<Vec<Value>> {
        self.delimited('[', ']', |parser| parser.value())
    }

    fn value(&mut self) -> Result<Value> {
        #[inline(always)]
        fn is_not_separator(&byte: &char) -> bool {
            !matches!(byte, ',' | '{' | '}' | '[' | ']')
        }

        self.skip_whitespace();
        let value = match self.peek_next() {
            Some('"') => Value::from(self.quoted_str()?.to_string()),
            Some('\'') => Value::from(self.quoted_char()?),
            Some('[') => Value::from(self.array()?),
            Some('{') => Value::from(self.dict()?),
            Some(_) => match self.substr(is_not_separator)?.trim() {
                "true" => Value::from(true),
                "false" => Value::from(false),
                value => {
                    if value.contains('.') {
                        if let Ok(float) = value.parse::<f64>() {
                            Value::from(float)
                        } else {
                            Value::from(value.to_string())
                        }
                    } else if let Ok(int) = value.parse::<usize>() {
                        Value::from(int)
                    } else if let Ok(int) = value.parse::<isize>() {
                        Value::from(int)
                    } else {
                        Value::from(value.to_string())
                    }
                }
            },
            None => Value::from(Empty::Unit),
        };

        self.skip_whitespace();
        Ok(value)
    }
}

impl std::str::FromStr for Value {
    type Err = std::convert::Infallible;

    fn from_str(string: &str) -> std::result::Result<Self, std::convert::Infallible> {
        let string = string.trim();
        let mut parser = Parser::new(string);
        match parser.value() {
            Ok(value) if parser.eof() => Ok(value),
            _ => Ok(Value::from(string)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::map;

    macro_rules! assert_parse_eq {
        ($string:expr => $expected:expr) => ({
            let expected = Value::from($expected);
            let actual: Value = $string.parse()
                .unwrap_or_else(|e| panic!("failed to parse {:?}: {:?}", $string, e));

            assert_eq!(actual, expected, "got {:?}, expected {:?}", actual, expected);
        });

        ($($string:expr => $expected:expr $(,)?)*) => (
            $(assert_parse_eq!($string => $expected);)*
        )
    }

    #[test]
    #[allow(clippy::approx_constant)] // false positive: using the PI constant would be wrong here
    fn check_simple_values_parse() {
        assert_parse_eq! {
            "true" => true,
            "false" => false,
            "\"false\"" => "false",
            "\"true\"" => "true",
            "  false" => false,
            "  false  " => false,
            "true  " => true,
            "1" => 1u8,
            " 0" => 0u8,
            " -0" => 0i8,
            " -2" => -2,
            " 123 " => 123u8,
            "a,b" => "a,b",
            "   a,b" => "a,b",
            "\"a\"" => "a",
            "a " => "a",
            "   a " => "a",
            "\" a\"" => " a",
            "\"a  \"" => "a  ",
            "\" a  \"" => " a  ",
            "1.2" => 1.2,
            "[" => "[",
            "[a" => "[a",
            "[a b" => "[a b",
            "]" => "]",
            "  1.2" => 1.2,
            "3.14159" => 3.14159,
            "\"\\t\"" => "\t",
            "\"abc\\td\"" => "abc\td",
            "\"abc\\td\\n\"" => "abc\td\n",
            "\"abc\\td\\n\\n\"" => "abc\td\n\n",
            "\"abc\\td\"" => "abc\td",
            "\"\\\"\"" => "\"",
            "\"\\n\\f\\b\\\\\\r\\\"\"" => "\n\u{c}\u{8}\\\r\"",
            "\"\\\"hi\\\"\"" => "\"hi\"",
            "\"hi\\u1234there\"" => "hi\u{1234}there",
            "\"\\\\\"" => "\\",
            // unterminated strings pass through as themselves
            "\"\\\"" => "\"\\\"",
        }
    }

    #[test]
    fn check_compound_values_parse() {
        fn v<T: Into<Value>>(v: T) -> Value { v.into() }

        assert_parse_eq! {
            "[1,2,3]" => vec![1u8, 2u8, 3u8],
            "[ 1 , 2   ,3]" => vec![1u8, 2u8, 3u8],
            " [ 1 , 2   , 3  ] " => vec![1u8, 2u8, 3u8],
            " [ a , b   ,, d  ] " => vec!["a", "b", "", "d"],
            " [ a , b   c,] " => vec!["a", "b   c"],
            " [ a , b   c,,] " => vec!["a", "b   c", ""],
            "{a=b}" => map!["a" => "b"],
            " { a = b } " => map!["a" => "b"],
            "{\"a\"=b}" => map!["a" => "b"],
            "{\"a.b.c\"=b}" => map!["a.b.c" => "b"],
            "{a=1,b=3}" => map!["a" => 1u8, "b" => 3u8],
            "{a=1,b=hi}" => map!["a" => v(1u8), "b" => v("hi")],
            "[1,[2],3]" => vec![v(1u8), v(vec![2u8]), v(3u8)],
            "{a=[[-2]]}" => map!["a" => vec![vec![-2]]],
            "{a=[[-2]],b=\" hi\"}" => map!["a" => v(vec![vec![-2]]), "b" => v(" hi")],
            "[1,true,hi,\"a \"]" => vec![v(1u8), v(true), v("hi"), v("a ")],
            "[1,{a=b},hi]" => vec![v(1u8), v(map!["a" => "b"]), v("hi")],
            "[[ -1], {a=[ b ]},  hi ]" =>
                vec![v(vec![-1]), v(map!["a" => vec!["b"]]), v("hi")],
        }
    }
}
