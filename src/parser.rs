use crate::{
    common::{CompilerError, CompilerResult, HasLineInfo},
    lexer::{Lexer, Token, TokenKind},
};

pub struct Parser {
    file_path: String,
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    pub fn new(lexer: &mut Lexer) -> CompilerResult<Self> {
        let mut tokens = Vec::new();
        while lexer.has_next_token() {
            tokens.push(lexer.next_token()?);
        }
        Ok(Self {
            file_path: lexer.file_path.clone(),
            tokens,
            index: 0,
        })
    }

    pub fn parse(&mut self) -> CompilerResult<()> {
        Ok(())
    }

    fn cur(&self) -> Option<&Token> {
        if self.index == 0 {
            None
        } else {
            self.tokens.get(self.index - 1)
        }
    }

    fn peek_at(&self, i: usize) -> Option<&Token> {
        self.tokens.get(self.index + i)
    }

    fn peek(&self) -> Option<&Token> {
        self.peek_at(0)
    }

    fn advance(&mut self) -> Option<&Token> {
        self.index += 1;
        let result = self.cur();
        result
    }

    fn check(&mut self, kind: TokenKind) -> bool {
        if let Some(tok) = self.peek()
            && tok.kind == kind
        {
            self.advance();
            true
        } else {
            false
        }
    }

    // fn advance(&mut self) -> CompilerResult<Token> {
    //     self.lexer.next_token()
    // }

    fn make_error(&self, object: &impl HasLineInfo, msg: impl ToString) -> CompilerError {
        CompilerError::ParserError {
            file_path: self.file_path.clone(),
            line_info: object.get_line_info(),
            msg: msg.to_string(),
        }
    }
}
