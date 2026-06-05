use std::{collections::HashMap, sync::LazyLock};

use num_bigint::BigInt;

use crate::{common::{CompileError, CompileResult, HasLineInfo, LineInfo}, errors};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBrack,
    RBrack,
    LAngle,
    RAngle,

    Comma,
    Colon,
    Semicolon,
    Equal,
    Arrow,
    // Bang,
    Dot,
    Tilde,
    Star,
    Slash,
    Percent,
    Plus,
    Minus,
    Ampersand,
    Caret,
    Pipe,
    ShiftLeft,
    ShiftRight,
    LessEq,
    EqEq,
    NotEq,
    GreaterEq,

    Label,
    Ident,
    StringLit,
    IntLit,
    FloatLit,

    True,
    False,
    As,
    Fun,
    Const,
    Void,
    Noreturn,
    Typedef,
    Underscore,
    Not,
    And,
    Or,
    If,
    While,
    Yield,
    Continue,
    Break,
    Return,
    Else,
    Module,
    Struct,
    Union,
    Using,
    Sizeof,
    Typeof,
    Alignof,
    Compeval,

    // Directives
    DirectiveZero,
    DirectiveUninit,
    DirectiveGhost,
    DirectiveDefault,
    DirectiveTrivial,
}

impl TokenKind {
    pub fn get_repr(&self) -> &str {
        match self {
            TokenKind::LParen => "'('",
            TokenKind::RParen => "')'",
            TokenKind::LBrace => "'{'",
            TokenKind::RBrace => "'}'",
            TokenKind::LBrack => "'['",
            TokenKind::RBrack => "']'",
            TokenKind::LAngle => "'<'",
            TokenKind::RAngle => "'>'",
            TokenKind::Comma => "','",
            TokenKind::Colon => "':'",
            TokenKind::Semicolon => "';'",
            TokenKind::Equal => "'='",
            TokenKind::Arrow => "'->'",
            TokenKind::Dot => "'.'",
            TokenKind::Tilde => "'~'",
            TokenKind::Star => "'*'",
            TokenKind::Slash => "'/'",
            TokenKind::Percent => "'%'",
            TokenKind::Plus => "'+'",
            TokenKind::Minus => "'-'",
            TokenKind::Ampersand => "'&'",
            TokenKind::Caret => "'^'",
            TokenKind::Pipe => "'|'",
            TokenKind::ShiftLeft => "'<<'",
            TokenKind::ShiftRight => "'>>'",
            TokenKind::LessEq => "'<='",
            TokenKind::EqEq => "'=='",
            TokenKind::NotEq => "'!='",
            TokenKind::GreaterEq => "'>='",
            TokenKind::Label => "<$label>",
            TokenKind::Ident => "<identifier>",
            TokenKind::StringLit => "<string>",
            TokenKind::IntLit => "<integer>",
            TokenKind::FloatLit => "<float>",
            TokenKind::True => "'true'",
            TokenKind::False => "'false'",
            TokenKind::As => "'as'",
            TokenKind::Fun => "'fun'",
            TokenKind::Const => "'const'",
            TokenKind::Void => "'void'",
            TokenKind::Noreturn => "'noreturn'",
            TokenKind::Typedef => "'typedef'",
            TokenKind::Underscore => "'_'",
            TokenKind::Not => "'not'",
            TokenKind::And => "'and'",
            TokenKind::Or => "'or'",
            TokenKind::If => "'if'",
            TokenKind::While => "'while'",
            TokenKind::Yield => "'yield'",
            TokenKind::Continue => "'continue'",
            TokenKind::Break => "'break'",
            TokenKind::Return => "'return'",
            TokenKind::Else => "'else'",
            TokenKind::Module => "'module'",
            TokenKind::Struct => "'struct'",
            TokenKind::Union => "'union'",
            TokenKind::Using => "'using'",
            TokenKind::Sizeof => "'sizeof'",
            TokenKind::Typeof => "'typeof'",
            TokenKind::Alignof => "'alignof'",
            TokenKind::Compeval => "'compeval'",
            TokenKind::DirectiveZero => "'#zero'",
            TokenKind::DirectiveUninit => "'#uninit'",
            TokenKind::DirectiveGhost => "'#ghost'",
            TokenKind::DirectiveDefault => "'#default'",
            TokenKind::DirectiveTrivial => "'#trivial'",
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum TokenSuffix {
    I8, I16, I32, I64, I128, ISize,
    U8, U16, U32, U64, U128, USize,
    F32, F64
}

#[derive(Clone, Debug)]
pub enum TokenValue {
    String(String),
    Int {
        integral: BigInt,
        suffix: Option<TokenSuffix>,
    },
    Float {
        integral: BigInt,
        fractional: BigInt,
        mantissa: BigInt,
        suffix: Option<TokenSuffix>,
    },
}

#[derive(Clone, Debug)]
pub struct Token {
    pub line_info: LineInfo,
    pub kind: TokenKind,
    pub text: String,
    pub value: Option<TokenValue>,
}

impl HasLineInfo for Token {
    fn get_line_info(&self) -> LineInfo {
        self.line_info
    }
}

#[derive(Clone, Copy, Debug)]
enum NumberRadix {
    Binary,
    Octal,
    Decimal,
    Hex,
}

pub struct Lexer {
    pub file_path: String,
    text: String,
    start: usize,
    index: usize,
    line_info: LineInfo,
}

static KEYWORDS: LazyLock<HashMap<&str, TokenKind>> = LazyLock::new(|| {
    let mut keywords: HashMap<&str, TokenKind> = HashMap::new();
    keywords.insert("true", TokenKind::True);
    keywords.insert("false", TokenKind::False);
    keywords.insert("if", TokenKind::If);
    keywords.insert("while", TokenKind::While);
    keywords.insert("yield", TokenKind::Yield);
    keywords.insert("continue", TokenKind::Continue);
    keywords.insert("break", TokenKind::Break);
    keywords.insert("return", TokenKind::Return);
    keywords.insert("as", TokenKind::As);
    keywords.insert("fun", TokenKind::Fun);
    keywords.insert("const", TokenKind::Const);
    keywords.insert("void", TokenKind::Void);
    keywords.insert("noreturn", TokenKind::Noreturn);
    keywords.insert("typedef", TokenKind::Typedef);
    keywords.insert("_", TokenKind::Underscore);
    keywords.insert("not", TokenKind::Not);
    keywords.insert("and", TokenKind::And);
    keywords.insert("or", TokenKind::Or);
    keywords.insert("else", TokenKind::Else);
    keywords.insert("module", TokenKind::Module);
    keywords.insert("struct", TokenKind::Struct);
    keywords.insert("union", TokenKind::Union);
    keywords.insert("using", TokenKind::Using);
    keywords.insert("sizeof", TokenKind::Sizeof);
    keywords.insert("typeof", TokenKind::Typeof);
    keywords.insert("alignof", TokenKind::Alignof);
    keywords.insert("compeval", TokenKind::Compeval);
    keywords
});

static DIRECTIVES: LazyLock<HashMap<&str, TokenKind>> = LazyLock::new(|| {
    let mut directives: HashMap<&str, TokenKind> = HashMap::new();
    directives.insert("#zero", TokenKind::DirectiveZero);
    directives.insert("#uninit", TokenKind::DirectiveUninit);
    directives.insert("#ghost", TokenKind::DirectiveGhost);
    directives.insert("#default", TokenKind::DirectiveDefault);
    directives.insert("#trivial", TokenKind::DirectiveTrivial);
    directives
});

impl Lexer {
    pub fn new(file_path: &str, text: &str) -> Self {
        Self {
            file_path: file_path.to_owned(),
            text: text.trim_end().to_owned(),
            start: 0,
            index: 0,
            line_info: LineInfo::default(),
        }
    }

    pub fn has_next_token(&self) -> bool {
        self.index < self.text.chars().count()
    }

    pub fn next_token(&mut self) -> CompileResult<Token> {
        let token = self.next_token_impl()?;
        // Skip comments so that has_next_token does not get confused
        self.skip_unwanted()?;
        Ok(token)
    }
    fn next_token_impl(&mut self) -> CompileResult<Token> {
        macro_rules! token {
            ($kind:ident) => {
                return Ok(self.make_token($kind))
            };
            ($kind:ident, $value:expr) => {
                return Ok(self.make_token_with_val($kind, Some($value)))
            };
        }
        use TokenKind::*;

        self.index = self.start;
        self.line_info.line_end = self.line_info.line_start;
        self.line_info.col_end = self.line_info.col_start;
        loop {
            self.skip_unwanted()?;
            let c = self.getchar()?;
            match c {
                '(' => token!(LParen),
                ')' => token!(RParen),
                '{' => token!(LBrace),
                '}' => token!(RBrace),
                '[' => token!(LBrack),
                ']' => token!(RBrack),
                '<' => {
                    if self.check("=") {
                        token!(LessEq)
                    } else if self.check("<") {
                        token!(ShiftLeft)
                    } else {
                        token!(LAngle)
                    }
                }
                '>' => {
                    if self.check("=") {
                        token!(GreaterEq)
                    } else if self.check(">") {
                        token!(ShiftRight)
                    } else {
                        token!(RAngle)
                    }
                }
                ',' => token!(Comma),
                ':' => token!(Colon),
                ';' => token!(Semicolon),
                '=' => {
                    if self.check("=") {
                        token!(EqEq)
                    } else {
                        token!(Equal)
                    }
                }
                '-' => {
                    if self.check(">") {
                        token!(Arrow)
                    } else {
                        token!(Minus)
                    }
                }
                '!' => {
                    self.expect("=")?;
                    token!(NotEq)
                }
                '.' => token!(Dot),
                '~' => token!(Tilde),
                '*' => token!(Star),
                '/' => {
                    token!(Slash)
                }
                '%' => token!(Percent),
                '+' => token!(Plus),
                '&' => token!(Ampersand),
                '^' => token!(Caret),
                '|' => token!(Pipe),
                '#' => {
                    self.expect_ident(true)?;
                    token!(Ident)
                }
                '$' => {
                    self.expect_ident(true)?;
                    token!(Label)
                }
                '_' | 'a'..='z' | 'A'..='Z' => {
                    self.expect_ident(false)?;
                    token!(Ident)
                }
                '"' => {
                    let str = self.expect_string("", '"', false, false)?;
                    token!(StringLit, TokenValue::String(str))
                }
                '`' => {
                    let str = self.expect_string("", '`', true, false)?;
                    token!(StringLit, TokenValue::String(str))
                }
                '0'..='9' => {
                    if c == '0' {
                        if let Some(c) = self.peek() {
                            match c {
                                // binary
                                'b' | 'B' => {
                                    self.advance();
                                    let integral = self.expect_number(NumberRadix::Binary)?;
                                    let suffix = self.check_int_suffix();
                                    token!(IntLit, TokenValue::Int { integral, suffix })
                                },
                                // octal
                                'o' | 'O' => {
                                    self.advance();
                                    let integral = self.expect_number(NumberRadix::Octal)?;
                                    let suffix = self.check_int_suffix();
                                    token!(IntLit, TokenValue::Int { integral, suffix })
                                },
                                // hex
                                'x' | 'X' => {
                                    self.advance();
                                    return self.get_number_token(NumberRadix::Hex, 'p');
                                },
                                _ => {},
                            }
                        }
                    }
                    self.index -= 1;
                    return self.get_number_token(NumberRadix::Decimal, 'e');
                }
                ' ' | '\t' | '\r' | '\n' => {
                    self.start = self.index;
                    self.line_info.line_start = self.line_info.line_end;
                    self.line_info.col_start = self.line_info.col_end;
                }
                _ => return Err(self.make_error_cur(format!("unexpected char '{}'", c))),
            }
        }
    }

    fn skip_unwanted(&mut self) -> CompileResult<()> {
        loop {
            let Some(c) = self.peek() else { return Ok(()) };
            match c {
                '/' => {
                    if let Some(c) = self.peek_at(1) {
                        match c {
                            '/' => {
                                // Single line comment
                                self.getchar()?;
                                self.getchar()?;
                                self.skip_line();
                            }
                            '*' => {
                                // Multi line comment
                                self.start = self.index;
                                self.line_info.line_start = self.line_info.line_end;
                                self.line_info.col_start = self.line_info.col_end;
                                self.getchar()?;
                                self.getchar()?;
                                self.skip_multiline_comment()?;
                            }
                            _ => break,
                        }
                    } else {
                        break;
                    }
                }
                ' ' | '\t' | '\r' | '\n' => {
                    self.getchar()?;
                }
                _ => break,
            }
        }
        self.start = self.index;
        self.line_info.line_start = self.line_info.line_end;
        self.line_info.col_start = self.line_info.col_end;
        Ok(())
    }

    fn skip_multiline_comment(&mut self) -> CompileResult<()> {
        let mut depth = 1;
        loop {
            if depth == 0 {
                break;
            }
            if let Some(c) = self.peek() {
                match c {
                    '/' => {
                        if let Some(c) = self.peek_at(1)
                            && c == '*'
                        {
                            self.getchar()?;
                            depth += 1;
                        }
                    }
                    '*' => {
                        if let Some(c) = self.peek_at(1)
                            && c == '/'
                        {
                            self.getchar()?;
                            depth -= 1;
                        }
                    }
                    _ => {}
                }
                self.advance();
            } else {
                return Err(errors![
                    self.make_error(format!("expected end of multiline comment, comment depth: '{}'", depth)),
                    self.make_note_at_start("comment starts here"),
                ]);
            }
        }
        Ok(())
    }

    fn skip_line(&mut self) {
        loop {
            if let Some(c) = self.peek() {
                if c == '\n' {
                    break;
                }
                self.advance();
            } else {
                break;
            }
        }
    }

    fn get_ident_kind(text: &str) -> TokenKind {
        KEYWORDS
            .get(text)
            .copied()
            .unwrap_or_else(|| DIRECTIVES.get(text).copied().unwrap_or(TokenKind::Ident))
    }

    fn make_token_with_val(&mut self, kind: TokenKind, value: Option<TokenValue>) -> Token {
        // Construct the token
        let text: String = self
            .text
            .chars()
            .skip(self.start)
            .take(self.index - self.start)
            .collect();
        let result = Token {
            line_info: self.line_info,
            kind: if kind == TokenKind::Ident {
                Self::get_ident_kind(&text)
            } else {
                kind
            },
            text,
            value,
        };
        // Move the marker
        self.start = self.index;
        self.line_info.line_start = self.line_info.line_end;
        self.line_info.col_start = self.line_info.col_end;
        // Return the token
        result
    }

    fn make_token(&mut self, kind: TokenKind) -> Token {
        self.make_token_with_val(kind, None)
    }

    fn peek_at(&self, i: usize) -> Option<char> {
        self.text.chars().nth(self.index + i)
    }

    fn peek(&self) -> Option<char> {
        self.peek_at(0)
    }

    fn getchar(&mut self) -> CompileResult<char> {
        match self.advance() {
            Some(c) => Ok(c),
            None => Err(self.make_error_cur("unexpected end of file")),
        }
    }

    fn advance(&mut self) -> Option<char> {
        let result = self.peek();

        if let Some(c) = result {
            self.index += 1;
            self.line_info.col_end += 1;
            if c == '\n' {
                self.line_info.line_end += 1;
                self.line_info.col_end = 1;
            }
        }

        result
    }

    fn check(&mut self, str: &str) -> bool {
        let old_index = self.index;
        let old_line_info = self.line_info;
        for c in str.chars() {
            match self.peek() {
                Some(peek_c) => {
                    if peek_c != c {
                        // Restore
                        self.index = old_index;
                        self.line_info = old_line_info;
                        return false;
                    }
                    self.advance();
                }
                None => {
                    // Restore
                    self.index = old_index;
                    self.line_info = old_line_info;
                    return false;
                }
            }
        }
        true
    }

    fn is_binary(c: char) -> bool {
        c == '0' || c == '1'
    }

    fn is_octal(c: char) -> bool {
        '0' <= c && c <= '7'
    }

    fn is_decimal(c: char) -> bool {
        '0' <= c && c <= '9'
    }

    fn is_hex(c: char) -> bool {
        ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')
    }

    fn check_float_suffix(&mut self) -> Option<TokenSuffix> {
        if      self.check("f32") { Some(TokenSuffix::F32) }
        else if self.check("f64") { Some(TokenSuffix::F64) }
        else                      { None }
    }

    fn check_int_suffix(&mut self) -> Option<TokenSuffix> {
        if      self.check("i8")    { Some(TokenSuffix::I8) }
        else if self.check("i16")   { Some(TokenSuffix::I16) }
        else if self.check("i32")   { Some(TokenSuffix::I32) }
        else if self.check("i64")   { Some(TokenSuffix::I64) }
        else if self.check("i128")  { Some(TokenSuffix::I128) }
        else if self.check("isize") { Some(TokenSuffix::ISize) }
        else if self.check("u8")    { Some(TokenSuffix::U8) }
        else if self.check("u16")   { Some(TokenSuffix::U16) }
        else if self.check("u32")   { Some(TokenSuffix::U32) }
        else if self.check("u64")   { Some(TokenSuffix::U64) }
        else if self.check("u128")  { Some(TokenSuffix::U128) }
        else if self.check("usize") { Some(TokenSuffix::USize) }
        else                        { None }
    }

    fn get_number_token(&mut self, radix: NumberRadix, exp: char) -> CompileResult<Token> {
        let integral = self.expect_number(radix)?;
        if let Some(c) = self.peek() {
            match c {
                '.' => {
                    // decimal float
                    self.getchar()?;
                    let fractional = self.expect_number(radix)?;
                    let mut mantissa = BigInt::ZERO;
                    if let Some(c) = self.peek()
                        && c.eq_ignore_ascii_case(&exp)
                    {
                        self.getchar()?;
                        let c = self.getchar()?;
                        if c != '+' && c != '-' {
                            return Err(self.make_error_cur("expected '+' or '-'"));
                        }
                        mantissa = self.expect_number(radix)?;
                        if c == '-' {
                            mantissa *= -1;
                        }
                    }
                    let suffix = self.check_float_suffix();
                    let value = TokenValue::Float { integral, fractional, mantissa, suffix };
                    return Ok(self.make_token_with_val(TokenKind::FloatLit, Some(value)));
                },
                c => {
                    if c == exp {
                        self.getchar()?;
                        let c = self.getchar()?;
                        if c != '+' && c != '-' {
                            return Err(self.make_error_cur("expected '+' or '-'"));
                        }
                        let mut mantissa = self.expect_number(radix)?;
                        if c == '-' {
                            mantissa *= -1;
                        }
                        let suffix = self.check_float_suffix();
                        let value = TokenValue::Float {
                            integral,
                            fractional: BigInt::ZERO,
                            mantissa,
                            suffix
                        };
                        return Ok(self.make_token_with_val(TokenKind::FloatLit, Some(value)));
                    } else {
                        let suffix = self.check_int_suffix();
                        return Ok(self.make_token_with_val(TokenKind::IntLit, Some(TokenValue::Int { integral, suffix })));
                    }
                },
            }
        } else {
            let suffix = self.check_int_suffix();
            return Ok(self.make_token_with_val(TokenKind::IntLit, Some(TokenValue::Int { integral, suffix })));
        }
    }

    fn expect_number(&mut self, radix: NumberRadix) -> CompileResult<BigInt> {
        match radix {
            NumberRadix::Binary => self.expect_number_impl(2, Self::is_binary),
            NumberRadix::Octal => self.expect_number_impl(8, Self::is_octal),
            NumberRadix::Decimal => self.expect_number_impl(10, Self::is_decimal),
            NumberRadix::Hex => self.expect_number_impl(16, Self::is_hex),
        }
    }

    fn expect_number_impl<F>(&mut self, base: u32, digit_checker: F) -> CompileResult<BigInt>
    where F: Fn(char) -> bool
    {
        let mut number = BigInt::ZERO;
        let c = self.getchar()?;
        if !digit_checker(c) {
            return Err(self.make_error_cur("expected decimal digit"));
        }
        number = number * base + c.to_digit(base).unwrap();
        loop {
            match self.peek() {
                Some(c) => {
                    if !digit_checker(c) {
                        break;
                    }
                    number = number * base + c.to_digit(base).unwrap();
                    self.advance();
                }
                None => break,
            }
        }
        Ok(number)
    }

    fn expect_string(
        &mut self,
        prefix: &str,
        quantifier: char,
        multiline: bool,
        do_start: bool,
    ) -> CompileResult<String> {
        // TODO: use prefix
        if do_start {
            let Some(c) = self.advance() else {
                return Err(self.make_error_cur(format!("expected <{prefix}{quantifier}...{quantifier}>")));
            };
            if c != quantifier {
                return Err(self.make_error_cur(format!("expected <{prefix}{quantifier}...{quantifier}>")));
            }
        }
        let mut text = String::new();
        loop {
            match self.peek() {
                Some(c) => {
                    if !multiline && c == '\n' {
                        return Err(self.make_error(format!("newlines are not allowed in single-line strings")));
                    }
                    self.advance();
                    if c == '\\' {
                        let c = self.getchar()?;
                        let unescaped: char = match c {
                            '0' => '\0',
                            'a' => '\x07',
                            'b' => '\x08',
                            'e' => '\x1b',
                            'f' => '\x0c',
                            'n' => '\n',
                            'r' => '\r',
                            't' => '\t',
                            'v' => '\x0b',
                            '"' | '\'' | '`' | '\\' => c,
                            'x' => {
                                let dig1 = self.getchar()?;
                                if !Self::is_octal(dig1) {
                                    return Err(self.make_error_cur(format!("expected octal digit")));
                                }
                                let dig2 = self.getchar()?;
                                if !Self::is_hex(dig2) {
                                    return Err(self.make_error_cur(format!("expected hex digit")));
                                }
                                let dig1 = dig1.to_digit(8).unwrap();
                                let dig2 = dig2.to_digit(16).unwrap();
                                let num = dig1 << 4 | dig2;
                                char::from_u32(num).unwrap()
                            }
                            'u' => {
                                self.expect("{")?;
                                let start = LineInfo {
                                    line_start: self.line_info.line_end,
                                    line_end: 0,
                                    col_start: self.line_info.col_end,
                                    col_end: 0,
                                };
                                let mut num = 0u32;
                                let mut times = 0;
                                loop {
                                    if let Some(c) = self.peek() {
                                        if c == '}' {
                                            break;
                                        }
                                        if !Self::is_hex(c) {
                                            return Err(self.make_error(format!("expected hex digit")));
                                        }
                                    }
                                    let c = self.getchar()?;
                                    num = num << 4 | c.to_digit(16).unwrap();
                                    times += 1;
                                    if times >= 6 {
                                        break;
                                    }
                                }
                                if times < 1 {
                                    return Err(self.make_error(format!("expected hex digit")));
                                }
                                let res = if let Some(result) = char::from_u32(num) {
                                    result
                                } else {
                                    return Err(self.make_error_range(
                                        &LineInfo::from_range(&start, &self.line_info),
                                        "invalid value of unicode codepoint",
                                    ));
                                };
                                self.expect("}")?;
                                res
                            }
                            '\n' => {
                                while let Some(c) = self.peek()
                                    && c.is_ascii_whitespace()
                                {
                                    self.advance();
                                }
                                c
                            }
                            _ => {
                                return Err(self.make_error_cur(format!("invalid escape sequence '\\{}'", c)));
                            }
                        };
                        text.push(unescaped);
                    } else {
                        if c == quantifier {
                            break;
                        }
                        text.push(c);
                    }
                }
                None => {
                    return Err(self.make_error(format!("expected end of string <{quantifier}>")));
                }
            }
        }
        Ok(text)
    }

    fn expect_ident(&mut self, do_start: bool) -> CompileResult<()> {
        if do_start {
            let Some(c) = self.advance() else {
                return Err(self.make_error_cur(format!("expected identifier")));
            };
            if c != '_' && !c.is_ascii_alphabetic() {
                return Err(self.make_error_cur(format!("expected identifier")));
            }
        }
        loop {
            match self.peek() {
                Some(c) => {
                    if c != '_' && !c.is_ascii_alphanumeric() {
                        break;
                    }
                    self.advance();
                }
                None => break,
            }
        }
        Ok(())
    }

    fn expect(&mut self, str: &str) -> CompileResult<()> {
        if !self.check(str) {
            Err(self.make_error(format!("expected '{}'", str)))
        } else {
            Ok(())
        }
    }

    fn make_error_range(&self, object: &impl HasLineInfo, msg: impl ToString) -> CompileError {
        CompileError::LexerError {
            file_path: self.file_path.clone(),
            line_info: object.get_line_info(),
            msg: msg.to_string(),
        }
    }

    fn make_error_cur(&self, msg: impl ToString) -> CompileError {
        self.make_error_range(
            &LineInfo {
                line_start: self.line_info.line_end,
                line_end: self.line_info.line_end,
                col_start: self.line_info.col_end - 1,
                col_end: self.line_info.col_end,
            },
            msg,
        )
    }

    fn make_error(&self, msg: impl ToString) -> CompileError {
        self.make_error_range(
            &LineInfo {
                line_start: self.line_info.line_end,
                line_end: self.line_info.line_end,
                col_start: self.line_info.col_end,
                col_end: self.line_info.col_end + 1,
            },
            msg,
        )
    }

    fn make_note_at_start(&self, msg: impl ToString) -> CompileError {
        CompileError::LexerNote {
            file_path: self.file_path.clone(),
            line_info: LineInfo {
                line_start: self.line_info.line_start,
                line_end: self.line_info.line_start,
                col_start: self.line_info.col_start,
                col_end: self.line_info.col_start + 1,
            },
            msg: msg.to_string(),
        }
    }
}
