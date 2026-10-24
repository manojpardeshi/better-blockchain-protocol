//! JSON values, a strict parser, and the canonical encoding of SPEC §2.
//!
//! The canonical form must be byte-identical to Python's
//! `json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)`
//! applied to the value Python's `json.loads` would produce from the same input:
//!
//! * object keys sorted by code point (Rust `String` ordering is UTF-8 byte order, which is the same);
//! * every character outside printable ASCII (0x20..=0x7e) escaped as `\uXXXX` (lowercase hex,
//!   UTF-16 surrogate pairs above U+FFFF), with the short escapes `\" \\ \n \r \t \b \f`;
//! * integers in decimal; a number with a fraction or exponent is a float, printed like Python's
//!   `repr(float)` (shortest round-trip digits, exponent form when the decimal point is at
//!   position <= -4 or > 16, `.0` appended to integral values);
//! * duplicate keys: the last one wins (as in Python).
//!
//! Where Python would accept input that cannot be represented here (lone UTF-16 surrogates,
//! `NaN`/`Infinity`, integers beyond i128, nesting deeper than [`MAX_DEPTH`], non-UTF-8 bytes)
//! the parser refuses it, so the witness rejects the request: being stricter than the reference
//! can only make it abstain, never vote where the reference would not.

use std::collections::BTreeMap;
use std::fmt::Write as _;

/// Deepest nesting the parser accepts (Python's limit is the interpreter recursion limit).
pub const MAX_DEPTH: usize = 256;

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Int(i128),
    Float(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(BTreeMap<String, Json>),
}

pub type Map = BTreeMap<String, Json>;

impl Json {
    pub fn str(s: impl Into<String>) -> Json {
        Json::Str(s.into())
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }

    /// An integer (booleans are not integers, as in SPEC §2).
    pub fn as_int(&self) -> Option<i128> {
        match self {
            Json::Int(i) => Some(*i),
            _ => None,
        }
    }

    pub fn as_obj(&self) -> Option<&Map> {
        match self {
            Json::Obj(m) => Some(m),
            _ => None,
        }
    }

    pub fn as_arr(&self) -> Option<&Vec<Json>> {
        match self {
            Json::Arr(a) => Some(a),
            _ => None,
        }
    }

    /// `obj[key]` for objects; `None` for a missing key or a non-object.
    pub fn get(&self, key: &str) -> Option<&Json> {
        self.as_obj().and_then(|m| m.get(key))
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Json::Null)
    }

    /// Canonical encoding (SPEC §2).
    pub fn canonical(&self) -> Vec<u8> {
        let mut out = String::with_capacity(128);
        write_canonical(self, &mut out);
        out.into_bytes()
    }

    pub fn canonical_string(&self) -> String {
        let mut out = String::with_capacity(128);
        write_canonical(self, &mut out);
        out
    }
}

impl From<&str> for Json {
    fn from(s: &str) -> Json {
        Json::Str(s.to_string())
    }
}
impl From<String> for Json {
    fn from(s: String) -> Json {
        Json::Str(s)
    }
}
impl From<i128> for Json {
    fn from(i: i128) -> Json {
        Json::Int(i)
    }
}
impl From<bool> for Json {
    fn from(b: bool) -> Json {
        Json::Bool(b)
    }
}
impl<T: Into<Json>> From<Option<T>> for Json {
    fn from(o: Option<T>) -> Json {
        o.map(Into::into).unwrap_or(Json::Null)
    }
}

/// Build an object from `(key, value)` pairs.
pub fn obj<const N: usize>(pairs: [(&str, Json); N]) -> Json {
    Json::Obj(pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
}

// ------------------------------------------------------------------ encoding

pub fn write_canonical(v: &Json, out: &mut String) {
    match v {
        Json::Null => out.push_str("null"),
        Json::Bool(true) => out.push_str("true"),
        Json::Bool(false) => out.push_str("false"),
        Json::Int(i) => {
            let _ = write!(out, "{i}");
        }
        Json::Float(f) => out.push_str(&py_float_repr(*f)),
        Json::Str(s) => write_str(s, out),
        Json::Arr(a) => {
            out.push('[');
            for (i, x) in a.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_canonical(x, out);
            }
            out.push(']');
        }
        Json::Obj(m) => {
            out.push('{');
            for (i, (k, x)) in m.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_str(k, out);
                out.push(':');
                write_canonical(x, out);
            }
            out.push('}');
        }
    }
}

/// A string as Python's `ensure_ascii=True` encoder writes it.
pub fn write_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            ' '..='~' => out.push(c),
            _ => {
                let mut buf = [0u16; 2];
                for unit in c.encode_utf16(&mut buf) {
                    let _ = write!(out, "\\u{:04x}", unit);
                }
            }
        }
    }
    out.push('"');
}

/// Python's `repr(float)` for a finite float.
pub fn py_float_repr(x: f64) -> String {
    debug_assert!(x.is_finite());
    if x == 0.0 {
        return if x.is_sign_negative() { "-0.0".into() } else { "0.0".into() };
    }
    // Rust's `{:e}` gives the shortest digits that round-trip, e.g. "1.2345e-7".
    let s = format!("{:e}", x);
    let (mant, exp) = s.split_once('e').expect("LowerExp always has an exponent");
    let (neg, mant) = match mant.strip_prefix('-') {
        Some(m) => (true, m),
        None => (false, mant),
    };
    let digits: String = mant.chars().filter(|c| *c != '.').collect();
    let exp: i32 = exp.parse().expect("integer exponent");
    let decpt = exp + 1; // value = 0.DIGITS * 10^decpt
    let mut out = String::new();
    if neg {
        out.push('-');
    }
    if decpt <= -4 || decpt > 16 {
        out.push_str(&digits[..1]);
        if digits.len() > 1 {
            out.push('.');
            out.push_str(&digits[1..]);
        }
        let e = decpt - 1;
        let _ = write!(out, "e{}{:02}", if e < 0 { '-' } else { '+' }, e.abs());
    } else if decpt <= 0 {
        out.push_str("0.");
        for _ in 0..(-decpt) {
            out.push('0');
        }
        out.push_str(&digits);
    } else if decpt as usize >= digits.len() {
        out.push_str(&digits);
        for _ in 0..(decpt as usize - digits.len()) {
            out.push('0');
        }
        out.push_str(".0");
    } else {
        out.push_str(&digits[..decpt as usize]);
        out.push('.');
        out.push_str(&digits[decpt as usize..]);
    }
    out
}

// ------------------------------------------------------------------- parsing

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError(pub String);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid JSON: {}", self.0)
    }
}

impl std::error::Error for ParseError {}

pub fn parse(input: &[u8]) -> Result<Json, ParseError> {
    let text = std::str::from_utf8(input).map_err(|_| ParseError("not UTF-8".into()))?;
    let mut p = Parser { s: text.as_bytes(), src: text, i: 0 };
    p.ws();
    let v = p.value(0)?;
    p.ws();
    if p.i != p.s.len() {
        return Err(p.err("extra data"));
    }
    Ok(v)
}

pub fn parse_str(input: &str) -> Result<Json, ParseError> {
    parse(input.as_bytes())
}

struct Parser<'a> {
    s: &'a [u8],
    src: &'a str,
    i: usize,
}

impl<'a> Parser<'a> {
    fn err(&self, what: &str) -> ParseError {
        ParseError(format!("{what} at byte {}", self.i))
    }

    fn ws(&mut self) {
        while self.i < self.s.len() && matches!(self.s[self.i], b' ' | b'\t' | b'\n' | b'\r') {
            self.i += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.s.get(self.i).copied()
    }

    fn lit(&mut self, word: &str, v: Json) -> Result<Json, ParseError> {
        if self.s[self.i..].starts_with(word.as_bytes()) {
            self.i += word.len();
            Ok(v)
        } else {
            Err(self.err("unexpected token"))
        }
    }

    fn value(&mut self, depth: usize) -> Result<Json, ParseError> {
        if depth > MAX_DEPTH {
            return Err(self.err("nesting too deep"));
        }
        match self.peek() {
            None => Err(self.err("unexpected end")),
            Some(b'n') => self.lit("null", Json::Null),
            Some(b't') => self.lit("true", Json::Bool(true)),
            Some(b'f') => self.lit("false", Json::Bool(false)),
            Some(b'"') => Ok(Json::Str(self.string()?)),
            Some(b'[') => {
                self.i += 1;
                let mut out = Vec::new();
                self.ws();
                if self.peek() == Some(b']') {
                    self.i += 1;
                    return Ok(Json::Arr(out));
                }
                loop {
                    self.ws();
                    out.push(self.value(depth + 1)?);
                    self.ws();
                    match self.peek() {
                        Some(b',') => self.i += 1,
                        Some(b']') => {
                            self.i += 1;
                            return Ok(Json::Arr(out));
                        }
                        _ => return Err(self.err("expected ',' or ']'")),
                    }
                }
            }
            Some(b'{') => {
                self.i += 1;
                let mut out = Map::new();
                self.ws();
                if self.peek() == Some(b'}') {
                    self.i += 1;
                    return Ok(Json::Obj(out));
                }
                loop {
                    self.ws();
                    if self.peek() != Some(b'"') {
                        return Err(self.err("expected a string key"));
                    }
                    let k = self.string()?;
                    self.ws();
                    if self.peek() != Some(b':') {
                        return Err(self.err("expected ':'"));
                    }
                    self.i += 1;
                    self.ws();
                    let v = self.value(depth + 1)?;
                    out.insert(k, v); // last duplicate wins, as in Python
                    self.ws();
                    match self.peek() {
                        Some(b',') => self.i += 1,
                        Some(b'}') => {
                            self.i += 1;
                            return Ok(Json::Obj(out));
                        }
                        _ => return Err(self.err("expected ',' or '}'")),
                    }
                }
            }
            Some(c) if c == b'-' || c.is_ascii_digit() => self.number(),
            Some(_) => Err(self.err("unexpected character")),
        }
    }

    fn digits(&mut self) -> usize {
        let start = self.i;
        while self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.i += 1;
        }
        self.i - start
    }

    fn number(&mut self) -> Result<Json, ParseError> {
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        match self.peek() {
            Some(b'0') => self.i += 1,
            Some(c) if c.is_ascii_digit() => {
                self.digits();
            }
            _ => return Err(self.err("invalid number")),
        }
        let mut float = false;
        if self.peek() == Some(b'.') {
            let save = self.i;
            self.i += 1;
            if self.digits() == 0 {
                // Python's scanner stops before a bare '.', which then fails as extra data.
                self.i = save;
                return Err(self.err("invalid number"));
            }
            float = true;
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            let save = self.i;
            self.i += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.i += 1;
            }
            if self.digits() == 0 {
                self.i = save;
                return Err(self.err("invalid number"));
            }
            float = true;
        }
        let text = &self.src[start..self.i];
        if float {
            let f: f64 = text.parse().map_err(|_| self.err("invalid float"))?;
            if !f.is_finite() {
                return Err(self.err("float out of range"));
            }
            Ok(Json::Float(f))
        } else {
            text.parse::<i128>().map(Json::Int).map_err(|_| self.err("integer out of range"))
        }
    }

    fn hex4(&mut self) -> Result<u32, ParseError> {
        if self.i + 4 > self.s.len() {
            return Err(self.err("truncated \\u escape"));
        }
        let h = &self.src[self.i..self.i + 4];
        if !h.bytes().all(|c| c.is_ascii_hexdigit()) {
            return Err(self.err("invalid \\u escape"));
        }
        self.i += 4;
        Ok(u32::from_str_radix(h, 16).expect("hex digits"))
    }

    fn string(&mut self) -> Result<String, ParseError> {
        self.i += 1; // opening quote
        let mut out = String::new();
        loop {
            let start = self.i;
            while self.i < self.s.len() && self.s[self.i] != b'"' && self.s[self.i] != b'\\' && self.s[self.i] >= 0x20 {
                self.i += 1;
            }
            out.push_str(&self.src[start..self.i]);
            match self.peek() {
                None => return Err(self.err("unterminated string")),
                Some(b'"') => {
                    self.i += 1;
                    return Ok(out);
                }
                Some(b'\\') => {
                    self.i += 1;
                    let c = self.peek().ok_or_else(|| self.err("unterminated escape"))?;
                    self.i += 1;
                    match c {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let u = self.hex4()?;
                            let cp = if (0xd800..0xdc00).contains(&u) {
                                // A high surrogate must be followed by an escaped low surrogate;
                                // Python would keep a lone surrogate, which no Rust string can hold.
                                if !self.s[self.i..].starts_with(b"\\u") {
                                    return Err(self.err("lone surrogate"));
                                }
                                self.i += 2;
                                let lo = self.hex4()?;
                                if !(0xdc00..0xe000).contains(&lo) {
                                    return Err(self.err("lone surrogate"));
                                }
                                0x10000 + ((u - 0xd800) << 10) + (lo - 0xdc00)
                            } else if (0xdc00..0xe000).contains(&u) {
                                return Err(self.err("lone surrogate"));
                            } else {
                                u
                            };
                            out.push(char::from_u32(cp).ok_or_else(|| self.err("invalid code point"))?);
                        }
                        _ => return Err(self.err("invalid escape")),
                    }
                }
                Some(_) => return Err(self.err("control character in string")),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn canon(s: &str) -> String {
        parse_str(s).unwrap().canonical_string()
    }

    #[test]
    fn basics() {
        assert_eq!(canon(r#"{"b": [1, 2.5, null, true], "a": "x"}"#), r#"{"a":"x","b":[1,2.5,null,true]}"#);
        assert_eq!(canon(r#""é😀\u0001\u007f/""#), r#""\u00e9\ud83d\ude00\u0001\u007f/""#);
        assert_eq!(canon("-0"), "0");
        assert_eq!(canon("1E5"), "100000.0");
        assert_eq!(canon("1e16"), "1e+16");
        assert_eq!(canon("0.00001"), "1e-05");
        assert_eq!(canon("0.0001"), "0.0001");
        assert_eq!(canon(r#"{"a":1,"a":2}"#), r#"{"a":2}"#);
    }

    #[test]
    fn rejects() {
        for bad in ["NaN", "1e400", "\"\\ud800\"", "01", "1.", "[1,]", "{\"a\" 1}", "\"\u{1}\""] {
            assert!(parse_str(bad).is_err(), "{bad}");
        }
    }
}
