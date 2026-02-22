use std::{collections::HashMap, sync::LazyLock};

use crate::common::{CompileError, CompileResult, HasLineInfo, LineInfo};

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
    WrapPlus,
    SatPlus,
    Minus,
    WrapMinus,
    SatMinus,
    Ampersand,
    Caret,
    Pipe,
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
    Type,
    Underscore,
    Not,
    And,
    Or,
    If,
    While,
    Loop,
    Yield,
    Continue,
    Break,
    Return,
    Else,
    Module,
    Struct,
    Union,
    Import,
    Sizeof,
    Typeof,
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
            TokenKind::WrapPlus => "'+%'",
            TokenKind::SatPlus => "'+:'",
            TokenKind::Minus => "'-'",
            TokenKind::WrapMinus => "'-%'",
            TokenKind::SatMinus => "'-:'",
            TokenKind::Ampersand => "'&'",
            TokenKind::Caret => "'^'",
            TokenKind::Pipe => "'|'",
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
            TokenKind::Type => "'type'",
            TokenKind::Underscore => "'_'",
            TokenKind::Not => "'not'",
            TokenKind::And => "'and'",
            TokenKind::Or => "'or'",
            TokenKind::If => "'if'",
            TokenKind::While => "'while'",
            TokenKind::Loop => "'loop'",
            TokenKind::Yield => "'yield'",
            TokenKind::Continue => "'continue'",
            TokenKind::Break => "'break'",
            TokenKind::Return => "'return'",
            TokenKind::Else => "'else'",
            TokenKind::Module => "'module'",
            TokenKind::Struct => "'struct'",
            TokenKind::Union => "'union'",
            TokenKind::Import => "'import'",
            TokenKind::Sizeof => "'sizeof'",
            TokenKind::Typeof => "'typeof'",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub line_info: LineInfo,
    pub kind: TokenKind,
    pub text: String,
}

impl HasLineInfo for Token {
    fn get_line_info(&self) -> LineInfo {
        self.line_info
    }
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
    keywords.insert("loop", TokenKind::Loop);
    keywords.insert("yield", TokenKind::Yield);
    keywords.insert("continue", TokenKind::Continue);
    keywords.insert("break", TokenKind::Break);
    keywords.insert("return", TokenKind::Return);
    keywords.insert("as", TokenKind::As);
    keywords.insert("fun", TokenKind::Fun);
    keywords.insert("const", TokenKind::Const);
    keywords.insert("void", TokenKind::Void);
    keywords.insert("noreturn", TokenKind::Noreturn);
    keywords.insert("type", TokenKind::Type);
    keywords.insert("_", TokenKind::Underscore);
    keywords.insert("not", TokenKind::Not);
    keywords.insert("and", TokenKind::And);
    keywords.insert("or", TokenKind::Or);
    keywords.insert("else", TokenKind::Else);
    keywords.insert("module", TokenKind::Module);
    keywords.insert("struct", TokenKind::Struct);
    keywords.insert("union", TokenKind::Union);
    keywords.insert("import", TokenKind::Import);
    keywords.insert("sizeof", TokenKind::Sizeof);
    keywords.insert("typeof", TokenKind::Typeof);
    keywords
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
        macro_rules! token {
            ($($arg:tt)*) => {
                return Ok(self.make_token($($arg)*))
            }
        }
        macro_rules! throw {
            ($($arg:tt)*) => {
                return Err(self.make_error(format!($($arg)*)))
            }
        }
        use TokenKind::*;

        self.index = self.start;
        self.line_info.line_end = self.line_info.line_start;
        self.line_info.col_end = self.line_info.col_start;
        loop {
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
                    } else {
                        token!(LAngle)
                    }
                }
                '>' => {
                    if self.check("=") {
                        token!(GreaterEq)
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
                    } else if self.check("%") {
                        token!(WrapMinus)
                    } else if self.check(":") {
                        token!(SatMinus)
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
                    if self.check("/") {
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
                    } else {
                        token!(Slash)
                    }
                }
                '%' => token!(Percent),
                '+' => {
                    if self.check("%") {
                        token!(WrapPlus)
                    } else if self.check(":") {
                        token!(SatPlus)
                    } else {
                        token!(Plus)
                    }
                }
                '&' => token!(Ampersand),
                '^' => token!(Caret),
                '|' => token!(Pipe),
                '$' => {
                    self.expect_ident(true)?;
                    token!(Label)
                }
                '_' | 'a'..='z' | 'A'..='Z' => {
                    self.expect_ident(false)?;
                    token!(Ident)
                }
                '"' => {
                    self.expect_string("", '"', false, false)?;
                    token!(StringLit)
                }
                '`' => {
                    self.expect_string("", '`', true, false)?;
                    token!(StringLit)
                }
                '1'..='9' => {
                    self.expect_decimal(false)?;
                    if let Some(c) = self.peek()
                        && c == '.'
                    {
                        // decimal float
                        self.advance();
                        self.expect_float('e', false)?;
                        self.check_float_suffix();
                        token!(FloatLit)
                    } else {
                        self.check_int_suffix();
                        token!(IntLit)
                    }
                }
                '0' => {
                    match self.peek() {
                        Some(c) => match c {
                            'b' | 'B' => {
                                // binary
                                self.advance();
                                self.expect_binary()?;
                                self.check_int_suffix();
                                token!(IntLit)
                            }
                            'x' | 'X' => {
                                // hex
                                self.advance();
                                self.expect_hex()?;
                                if let Some(c) = self.peek()
                                    && c == '.'
                                {
                                    // hex float
                                    self.advance();
                                    self.expect_float('p', true)?;
                                    self.check_float_suffix();
                                    token!(FloatLit)
                                } else {
                                    self.check_int_suffix();
                                    token!(IntLit)
                                }
                            }
                            'o' | 'O' => {
                                self.advance();
                                self.expect_octal()?;
                                self.check_int_suffix();
                                token!(IntLit)
                            }
                            '.' => {
                                // decimal float
                                self.advance();
                                self.expect_float('e', false)?;
                                self.check_float_suffix();
                                token!(FloatLit)
                            }
                            _ => {
                                self.check_int_suffix();
                                token!(IntLit)
                            }
                        },
                        None => token!(IntLit),
                    }
                }
                ' ' | '\t' | '\r' | '\n' => {
                    self.start = self.index;
                    self.line_info.line_start = self.line_info.line_end;
                    self.line_info.col_start = self.line_info.col_end;
                }
                _ => {
                    throw!("unexpected char '{}'", c);
                }
            }
        }
    }

    fn get_ident_kind(text: &str) -> TokenKind {
        KEYWORDS.get(text).copied().unwrap_or(TokenKind::Ident)
    }

    fn make_token(&mut self, kind: TokenKind) -> Token {
        // Construct the token
        // let text: String = self
        //     .text
        //     .chars()
        //     .skip(self.start)
        //     .take(self.index - self.start)
        //     .collect();
        let text = self.text[self.start..self.index].to_owned();
        let result = Token {
            line_info: self.line_info,
            kind: if kind == TokenKind::Ident {
                Self::get_ident_kind(&text)
            } else {
                kind
            },
            text,
        };
        // Move the marker
        self.start = self.index;
        self.line_info.line_start = self.line_info.line_end;
        self.line_info.col_start = self.line_info.col_end;
        // Return the token
        result
    }

    fn peek_at(&self, i: usize) -> Option<char> {
        self.text.chars().nth(self.index + i)
    }

    fn peek(&self) -> Option<char> {
        self.peek_at(0)
    }

    // fn cur(&self) -> Option<char> {
    //     if self.index == 0 {
    //         None
    //     } else {
    //         self.text.chars().nth(self.index - 1)
    //     }
    // }

    fn getchar(&mut self) -> CompileResult<char> {
        match self.advance() {
            Some(c) => Ok(c),
            None => Err(self.make_error("unexpected end of file")),
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

    fn check_float_suffix(&mut self) -> bool {
        !self.check("f16") && !self.check("f32") && !self.check("f64")
    }

    fn check_int_suffix(&mut self) -> bool {
        !self.check("i8")
            && !self.check("i16")
            && !self.check("i32")
            && !self.check("i64")
            && !self.check("i128")
            && !self.check("isize")
            && !self.check("u8")
            && !self.check("u16")
            && !self.check("u32")
            && !self.check("u64")
            && !self.check("u128")
            && !self.check("usize")
    }

    fn expect_binary(&mut self) -> CompileResult<()> {
        let Some(c) = self.advance() else {
            return Err(self.make_error("expected binary digit"));
        };
        if !Self::is_binary(c) {
            return Err(self.make_error("expected binary digit"));
        }
        loop {
            match self.peek() {
                Some(c) => {
                    if !Self::is_binary(c) {
                        break;
                    }
                    self.advance();
                }
                None => break,
            }
        }
        if let Some(c) = self.peek()
            && Self::is_decimal(c)
        {
            self.advance();
            return Err(self.make_error("expected binary digit"));
        }
        Ok(())
    }

    fn expect_octal(&mut self) -> CompileResult<()> {
        let Some(c) = self.advance() else {
            return Err(self.make_error("expected octal digit"));
        };
        if !Self::is_octal(c) {
            return Err(self.make_error("expected octal digit"));
        }
        loop {
            match self.peek() {
                Some(c) => {
                    if !Self::is_octal(c) {
                        break;
                    }
                    self.advance();
                }
                None => break,
            }
        }
        if let Some(c) = self.peek()
            && Self::is_decimal(c)
        {
            self.advance();
            return Err(self.make_error("expected octal digit"));
        }
        Ok(())
    }

    fn expect_decimal(&mut self, do_start: bool) -> CompileResult<()> {
        if do_start {
            let c = self.getchar()?;
            if !Self::is_decimal(c) {
                return Err(self.make_error("expected decimal digit"));
            }
        }
        loop {
            match self.peek() {
                Some(c) => {
                    if !Self::is_decimal(c) {
                        break;
                    }
                    self.advance();
                }
                None => break,
            }
        }
        Ok(())
    }

    fn expect_hex(&mut self) -> CompileResult<()> {
        let Some(c) = self.advance() else {
            return Err(self.make_error("expected hex digit"));
        };
        if !Self::is_hex(c) {
            return Err(self.make_error("expected hex digit"));
        }
        loop {
            match self.peek() {
                Some(c) => {
                    if !Self::is_hex(c) {
                        break;
                    }
                    self.advance();
                }
                None => break,
            }
        }
        Ok(())
    }

    fn expect_float(&mut self, exp: char, is_hex: bool) -> CompileResult<()> {
        if is_hex {
            self.expect_hex()?;
            if let Some(c) = self.peek()
                && c.eq_ignore_ascii_case(&exp)
            {
                self.advance().unwrap();
                let c = self.getchar()?;
                if c != '+' && c != '-' {
                    return Err(self.make_error("expected '+' or '-'"));
                }
                self.expect_decimal(true)?;
            }
        } else {
            self.expect_decimal(true)?;
            if let Some(c) = self.peek()
                && c.eq_ignore_ascii_case(&exp)
            {
                self.advance().unwrap();
                let c = self.getchar()?;
                if c != '+' && c != '-' {
                    return Err(self.make_error("expected '+' or '-'"));
                }
                self.expect_decimal(true)?;
            }
        }
        Ok(())
    }

    fn expect_string(
        &mut self,
        prefix: &str,
        quantifier: char,
        multiline: bool,
        do_start: bool,
    ) -> CompileResult<()> {
        if do_start {
            let Some(c) = self.advance() else {
                return Err(
                    self.make_error(format!("expected {prefix}{quantifier}...{quantifier}"))
                );
            };
            if c != quantifier {
                return Err(
                    self.make_error(format!("expected {prefix}{quantifier}...{quantifier}"))
                );
            }
        }
        loop {
            match self.peek() {
                Some(c) => {
                    self.advance();
                    if c == quantifier {
                        break;
                    }
                    if !multiline && c == '\n' {
                        return Err(self.make_error(format!(
                            "newlines are not allowed in single-line strings"
                        )));
                    }
                }
                None => {
                    return Err(self.make_error(format!("expected end of string {quantifier}")));
                }
            }
        }
        Ok(())
    }

    fn expect_ident(&mut self, do_start: bool) -> CompileResult<()> {
        if do_start {
            let Some(c) = self.advance() else {
                return Err(self.make_error(format!("expected identifier")));
            };
            if c != '_' && !c.is_ascii_alphabetic() {
                return Err(self.make_error(format!("expected identifier")));
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

    fn make_error(&self, msg: impl ToString) -> CompileError {
        CompileError::LexerError {
            file_path: self.file_path.clone(),
            line_info: LineInfo {
                line_start: self.line_info.line_end,
                line_end: self.line_info.line_end,
                col_start: self.line_info.col_end - 1,
                col_end: self.line_info.col_end,
            },
            msg: msg.to_string(),
        }
    }
}
