use crate::{
    ast::{self, Arg},
    common::{CompileError, CompileResult, HasLineInfo, LineInfo},
    lexer::{
        Lexer, Token,
        TokenKind::{self, *},
    },
};

pub struct Parser {
    file_path: String,
    tokens: Vec<Token>,
    index: usize,
}

macro_rules! define_rule_list {
    ($type: ident, $rule_result: ident, $rule_from: ident) => {
        fn $rule_result(&mut self) -> Vec<crate::ast::$type> {
            let mut items = Vec::new();
            loop {
                if let Some(item) = self.rule_optional(Self::$rule_from) {
                    items.push(item);
                    if !self.check(Comma) {
                        break;
                    }
                } else {
                    break;
                }
            }
            items
        }
    };
}

impl Parser {
    pub fn new(lexer: &mut Lexer) -> CompileResult<Self> {
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

    pub fn parse(&mut self) -> CompileResult<()> {
        self.parse_expr()?;
        Ok(())
    }

    fn parse_type_fun_param(&mut self) -> CompileResult<ast::TypeFunctionParam> {
        // type_fun_param ::= identifier ':' type;
        let name = self.expect(Ident)?;
        self.expect(Dot)?;
        let taipe = self.parse_type()?;
        Ok(ast::TypeFunctionParam { name, taipe })
    }

    fn parse_type(&mut self) -> CompileResult<ast::Type> {
        // type ::= identifier ('.' identifier)*
        //        | 'fun' '(' type_fun_param_list ')' '->' type
        //        | 'const' type
        //        | '*' type
        //        | '[' type ';' ('_' | expr)']'
        //        | '[' type ']'
        //        | '(' type ')'
        //        | type_tuple
        //        | 'void' | '!' | 'type';
        if let Some(tok) = self.peek() {
            match tok.kind {
                Ident => {
                    let mut items = Vec::new();
                    items.push(self.get_token()?);
                    while let Some(tok) = self.peek()
                        && tok.kind == Dot
                    {
                        items.push(self.get_token()?);
                    }
                    Ok(ast::Type::Path { items })
                }
                Fun => {
                    let start = self.get_token()?;
                    self.expect(LParen)?;
                    let params = self.parse_type_fun_param_list();
                    self.expect(RParen)?;
                    self.expect(Arrow)?;
                    let ret = self.parse_type()?;
                    Ok(ast::Type::Function {
                        line_info: LineInfo::from_range(&start, &ret),
                        params,
                        ret: Box::new(ret),
                    })
                }
                Const => {
                    let token = self.get_token()?;
                    let taipe = self.parse_type()?;
                    Ok(ast::Type::Const {
                        token,
                        taipe: Box::new(taipe),
                    })
                }
                Star => {
                    let token = self.get_token()?;
                    let taipe = self.parse_type()?;
                    Ok(ast::Type::Pointer {
                        token,
                        taipe: Box::new(taipe),
                    })
                }
                LBrack => {
                    let start = self.get_token()?;
                    let taipe = self.parse_type()?;
                    if let Some(tok) = self.peek()
                        && tok.kind == Semicolon
                    {
                        self.get_token()?;
                        let expr = if let Some(tok) = self.peek()
                            && tok.kind == Underscore
                        {
                            self.get_token()?;
                            None
                        } else {
                            Some(self.parse_expr()?)
                        };
                        let end = self.expect(RBrack)?;
                        Ok(ast::Type::Array {
                            line_info: LineInfo::from_range(&start, &end),
                            taipe: Box::new(taipe),
                            expr,
                        })
                    } else {
                        let end = self.expect(RBrack)?;
                        Ok(ast::Type::Fat {
                            line_info: LineInfo::from_range(&start, &end),
                            taipe: Box::new(taipe),
                        })
                    }
                }
                LParen => {
                    if let Some(tok) = self.peek_at(1)
                        && tok.kind == RParen
                    {
                        return self.parse_type_tuple();
                    }
                    let save = self.index;

                    let start = self.get_token()?;
                    let taipe = self.parse_type()?;
                    if let Some(tok) = self.peek()
                        && tok.kind == Comma
                    {
                        self.index = save;
                        return self.parse_type_tuple();
                    }
                    let end = self.expect(RParen)?;
                    Ok(ast::Type::Paren {
                        line_info: LineInfo::from_range(&start, &end),
                        taipe: Box::new(taipe),
                    })
                }
                Void | Bang | Type => Ok(ast::Type::Literal(self.get_token()?)),
                _ => {
                    Err(self
                        .expect_err(&[Ident, Fun, Const, Star, LBrack, LParen, Void, Bang, Type]))
                }
            }
        } else {
            Err(self.expect_err(&[Ident, Fun, Const, Star, LBrack, LParen, Void, Bang, Type]))
        }
    }

    fn parse_expr(&mut self) -> CompileResult<ast::Expr> {
        self.parse_cast()
    }

    fn parse_cast(&mut self) -> CompileResult<ast::Expr> {
        // cast ::= unary ('as' type)*;
        let mut expr = self.parse_unary()?;
        while let Some(tok) = self.peek()
            && tok.kind == As
        {
            let taipe = self.parse_type()?;
            expr = ast::Expr::Cast {
                expr: Box::new(expr),
                taipe: Box::new(taipe),
            }
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> CompileResult<ast::Expr> {
        // unary ::= ('+'|'-'|'~') primary;
        let op = if let Some(tok) = self.peek() {
            match tok.kind {
                Plus | Minus | Tilde => Some(self.get_token()?),
                _ => None,
            }
        } else {
            None
        };
        let expr = self.parse_postfix()?;
        Ok(ast::Expr::Unary {
            op,
            expr: Box::new(expr),
        })
    }

    fn parse_arg(&mut self) -> CompileResult<Arg> {
        // arg ::= (identifer ':')? expr;
        let mut name: Option<Token> = None;
        if let Some(tok1) = self.peek_at(0)
            && tok1.kind == Ident
            && let Some(tok2) = self.peek_at(1)
            && tok2.kind == Colon
        {
            name = Some(self.get_token()?);
            self.get_token()?;
        }
        let expr = self.parse_expr()?;
        Ok(Arg { name, expr })
    }

    fn parse_postfix(&mut self) -> CompileResult<ast::Expr> {
        // postifix ::= primary ('.' identifier | '(' args_list ')' | '[' expr_list ']');
        let expr = self.parse_primary()?;
        if let Some(tok) = self.peek() {
            match tok.kind {
                Dot => {
                    self.get_token()?;
                    let name = self.expect(Ident)?;
                    Ok(ast::Expr::Member {
                        expr: Box::new(expr),
                        name,
                    })
                }
                LParen => {
                    self.get_token()?;
                    let args = self.parse_arg_list();
                    let end = self.expect(RParen)?;
                    Ok(ast::Expr::Call {
                        line_info: LineInfo::from_range(&expr, &end),
                        expr: Box::new(expr),
                        args,
                    })
                }
                LBrack => {
                    self.get_token()?;
                    let items = self.parse_expr_list();
                    let end = self.expect(RBrack)?;
                    Ok(ast::Expr::Index {
                        line_info: LineInfo::from_range(&expr, &end),
                        expr: Box::new(expr),
                        items,
                    })
                }
                _ => Ok(expr),
            }
        } else {
            Ok(expr)
        }
    }

    fn parse_primary(&mut self) -> CompileResult<ast::Expr> {
        // primary ::= 'true' | 'false' | integer | float | identifier
        //           | '(' expr ')' | tuple
        //           | '[' expr_list ']';
        if let Some(tok) = self.peek() {
            match tok.kind {
                True | False | IntLit | FloatLit | Ident => {
                    Ok(ast::Expr::Literal(self.get_token()?.clone()))
                }
                LParen => {
                    if let Some(tok) = self.peek_at(1)
                        && tok.kind == RParen
                    {
                        return self.parse_tuple();
                    }
                    let save = self.index;

                    let start = self.get_token()?;
                    let expr = self.parse_expr()?;
                    if let Some(tok) = self.peek()
                        && tok.kind == Comma
                    {
                        self.index = save;
                        return self.parse_tuple();
                    }
                    let end = self.expect(RParen)?;
                    Ok(ast::Expr::Paren {
                        line_info: LineInfo::from_range(&start, &end),
                        expr: Box::new(expr),
                    })
                }
                RParen => {
                    let start = self.get_token()?;
                    let exprs = self.parse_expr_list();
                    let end = self.expect(RBrack)?;
                    Ok(ast::Expr::Tuple {
                        line_info: LineInfo::from_range(&start, &end),
                        exprs,
                    })
                }
                _ => Err(self.expect_err(&[
                    True, False, IntLit, FloatLit, Ident, LParen, LBrace, If, While, Loop, Break,
                    Continue, Return,
                ])),
            }
        } else {
            Err(self.expect_err(&[
                True, False, IntLit, FloatLit, Ident, LParen, LBrace, If, While, Loop, Break,
                Continue, Return,
            ]))
        }
    }

    fn parse_type_tuple(&mut self) -> CompileResult<ast::Type> {
        // type_tuple ::= '(' type_list ')';
        let start = self.expect(LParen)?;
        let types = self.parse_type_list();
        let end = self.expect(RParen)?;
        Ok(ast::Type::Tuple {
            line_info: LineInfo::from_range(&start, &end),
            types,
        })
    }

    fn parse_tuple(&mut self) -> CompileResult<ast::Expr> {
        // tuple ::= '(' expr_list ')';
        let start = self.expect(LParen)?;
        let exprs = self.parse_expr_list();
        let end = self.expect(RParen)?;
        Ok(ast::Expr::Tuple {
            line_info: LineInfo::from_range(&start, &end),
            exprs,
        })
    }

    define_rule_list!(
        TypeFunctionParam,
        parse_type_fun_param_list,
        parse_type_fun_param
    );
    define_rule_list!(Type, parse_type_list, parse_type);
    define_rule_list!(Arg, parse_arg_list, parse_arg);
    define_rule_list!(Expr, parse_expr_list, parse_expr);

    // fn parse_expr_list(&mut self) -> Vec<ast::Expr> {
    //     let mut items = Vec::new();
    //     loop {
    //         if let Some(item) = self.rule_optional(Self::parse_expr) {
    //             items.push(item);
    //             if !self.check(Comma) {
    //                 break;
    //             }
    //         } else {
    //             break;
    //         }
    //     }
    //     items
    // }

    // fn rule_or<T, F>(&mut self, rule1: F, rule2: F) -> Option<T>
    // where
    //     F: Fn(&mut Parser) -> CompilerResult<T>,
    // {
    //     let save = self.index;
    //     if let Ok(value) = rule1(self) {
    //         Some(value)
    //     } else {
    //         self.index = save;
    //         if let Ok(value) = rule2(self) {
    //             Some(value)
    //         } else {
    //             self.index = save;
    //             None
    //         }
    //     }
    // }

    fn rule_optional<T, F>(&mut self, rule: F) -> Option<T>
    where
        F: Fn(&mut Parser) -> CompileResult<T>,
    {
        let save = self.index;
        if let Ok(value) = rule(self) {
            Some(value)
        } else {
            self.index = save;
            None
        }
    }

    fn expect_err(&self, kinds: &[TokenKind]) -> CompileError {
        let mut msg = String::new();
        msg.push_str("expected ");
        for kind in kinds {
            msg.push('\'');
            msg.push_str(kind.get_repr());
            msg.push_str("', ");
        }
        if kinds.len() > 0 {
            msg.pop();
            msg.pop();
        }
        self.make_error(&self.peek().unwrap(), msg)
    }

    fn cur(&self) -> Option<Token> {
        if self.index == 0 {
            None
        } else {
            self.tokens.get(self.index - 1).cloned()
        }
    }

    fn peek_at(&self, i: usize) -> Option<Token> {
        self.tokens.get(self.index + i).cloned()
    }

    fn peek(&self) -> Option<Token> {
        self.peek_at(0)
    }

    fn advance(&mut self) -> Option<Token> {
        self.index += 1;
        self.cur()
    }

    fn get_token(&mut self) -> CompileResult<Token> {
        if let Some(tok) = self.advance() {
            Ok(tok)
        } else {
            // TODO: do not unwrap here
            Err(self.make_error(&self.cur().unwrap(), "unexpected end of file"))
        }
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

    fn expect(&mut self, kind: TokenKind) -> CompileResult<Token> {
        if self.check(kind) {
            Ok(self.cur().unwrap())
        } else {
            Err(self.expect_err(&[kind]))
        }
    }

    // fn advance(&mut self) -> CompilerResult<Token> {
    //     self.lexer.next_token()
    // }

    fn make_error(&self, object: &impl HasLineInfo, msg: impl ToString) -> CompileError {
        CompileError::ParserError {
            file_path: self.file_path.clone(),
            line_info: object.get_line_info(),
            msg: msg.to_string(),
        }
    }
}
