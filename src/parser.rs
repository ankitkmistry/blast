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

macro_rules! define_binary_op {
    ($rule_result:ident, $rule_prev:ident, $($ops:ident),+ $(,)?) => {
        fn $rule_result(&mut self) -> CompileResult<ast::Expr> {
            let mut left = self.$rule_prev()?;
            while let Some(tok) = self.peek()
                && ($(tok.kind == $ops ||)+ false)
            {
                let op = self.get_token()?;
                let right = self.$rule_prev()?;
                left = ast::Expr::Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                };
            }
            Ok(left)
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

    pub fn parse(&mut self) -> CompileResult<ast::Program> {
        Ok(ast::Program {
            decls: self.parse_decls()?,
        })
    }

    // decl ::= (identifier | '_') ':' type (';' | (':' '=' object))
    //        | (identifier | '_') ':' ((':'|'=') object)
    //        | 'import' identifier ('.' identifier)* ('.' '*')
    //        ;
    fn parse_decl(&mut self) -> CompileResult<ast::Decl> {
        if let Some(tok) = self.peek() {
            match tok.kind {
                Ident | Underscore => {
                    let name = self.get_token()?;
                    self.expect(Colon)?;
                    if let Some(taipe) = self.rule_optional(Self::parse_type) {
                        let object = if let Some(tok) = self.peek()
                            && (tok.kind == Equal || tok.kind == Colon)
                        {
                            self.get_token()?;
                            Some(self.parse_object()?)
                        } else {
                            self.expect_term()?;
                            None
                        };
                        Ok(ast::Decl::Decl {
                            name,
                            taipe: Some(taipe),
                            object,
                        })
                    } else {
                        let object = if let Some(tok) = self.peek()
                            && (tok.kind == Equal || tok.kind == Colon)
                        {
                            self.get_token()?;
                            Some(self.parse_object()?)
                        } else {
                            return Err(self.expect_err_more(&["<type>"], &[Equal, Colon]));
                        };
                        Ok(ast::Decl::Decl {
                            name,
                            taipe: None,
                            object,
                        })
                    }
                }
                Import => {
                    let start = self.get_token()?;

                    let mut items = Vec::new();
                    items.push(self.expect(Ident)?);
                    while let Some(tok) = self.peek()
                        && tok.kind == Dot
                    {
                        self.get_token()?;
                        if let Some(tok) = self.peek() {
                            match tok.kind {
                                Ident => items.push(tok),
                                Star => {
                                    items.push(tok);
                                    break;
                                }
                                _ => return Err(self.expect_err(&[Ident, Star])),
                            }
                        } else {
                            return Err(self.expect_err(&[Ident, Star]));
                        }
                    }

                    let end = self.expect_term()?;
                    Ok(ast::Decl::Import {
                        line_info: LineInfo::from_range(&start, &end),
                        items,
                    })
                }
                _ => Err(self.expect_err(&[Ident, Underscore])),
            }
        } else {
            Err(self.expect_err(&[Ident, Underscore]))
        }
    }

    // decls ::= decl*;
    fn parse_decls(&mut self) -> CompileResult<Vec<ast::Decl>> {
        let mut decls = Vec::new();
        while let Some(tok) = self.peek()
            && (tok.kind == Ident || tok.kind == Underscore)
        {
            decls.push(self.parse_decl()?);
        }
        Ok(decls)
    }

    // object ::= module | struct | union | fun
    //          | 'type' type ';'
    //          | expr ';'
    //          ;
    fn parse_object(&mut self) -> CompileResult<ast::Object> {
        if let Some(tok) = self.peek() {
            match tok.kind {
                Module => self.parse_module(),
                Struct => self.parse_struct(),
                Union => self.parse_union(),
                Fun => self.parse_fun(),
                Type => {
                    self.get_token()?;
                    Ok(ast::Object::Typedef(self.parse_type()?))
                }
                _ => {
                    if self.is_expr_start() {
                        let expr = self.parse_expr()?;
                        self.expect_term()?;
                        Ok(ast::Object::Expr(expr))
                    } else {
                        Err(self.expect_err(&[
                            // Object begin tokens
                            Module, Struct, Union, Fun, Type, //
                            // Expr begin tokens
                            Not, Plus, Minus, Tilde, Star, Ampersand, //
                            // Primary expr begin tokens
                            True, False, IntLit, FloatLit, Ident, LParen, //
                        ]))
                    }
                }
            }
        } else {
            Err(self.expect_err(&[
                // Object begin tokens
                Module, Struct, Union, Fun, Type, //
                // Expr begin tokens
                Not, Plus, Minus, Tilde, Star, Ampersand, //
                // Primary expr begin tokens
                True, False, IntLit, FloatLit, Ident, LParen, //
            ]))
        }
    }

    // module ::= 'module' (string ';' | '{' decls '}');
    fn parse_module(&mut self) -> CompileResult<ast::Object> {
        let start = self.expect(Module)?;
        if let Some(tok) = self.peek() {
            match tok.kind {
                StringLit => {
                    let value = self.get_token()?;
                    self.expect_term()?;
                    Ok(ast::Object::ExternModule {
                        line_info: LineInfo::from_range(&start, &value),
                        value,
                    })
                }
                LBrace => {
                    self.expect(LBrace)?;
                    let decls = self.parse_decls()?;
                    let end = self.expect(RBrace)?;
                    Ok(ast::Object::Module {
                        line_info: LineInfo::from_range(&start, &end),
                        decls,
                    })
                }
                _ => Err(self.expect_err(&[StringLit, LBrace])),
            }
        } else {
            Err(self.expect_err(&[StringLit, LBrace]))
        }
    }

    // struct ::= 'struct' '{' decls '}';
    fn parse_struct(&mut self) -> CompileResult<ast::Object> {
        let start = self.expect(Struct)?;
        self.expect(LBrace)?;
        let decls = self.parse_decls()?;
        let end = self.expect(RBrace)?;
        Ok(ast::Object::Struct {
            line_info: LineInfo::from_range(&start, &end),
            decls,
        })
    }

    // union ::= 'union' '{' decls '}';
    fn parse_union(&mut self) -> CompileResult<ast::Object> {
        let start = self.expect(Union)?;
        self.expect(LBrace)?;
        let decls = self.parse_decls()?;
        let end = self.expect(RBrace)?;
        Ok(ast::Object::Union {
            line_info: LineInfo::from_range(&start, &end),
            decls,
        })
    }

    // fun ::= 'fun' '(' param_list ')' ('->' type)? (';' | block);
    fn parse_fun(&mut self) -> CompileResult<ast::Object> {
        let start = self.expect(Fun)?;
        self.expect(LParen)?;
        let params = self.parse_param_list();
        self.expect(RParen)?;
        let ret = if let Some(tok) = self.peek()
            && tok.kind == Arrow
        {
            self.get_token()?;
            Some(self.parse_type()?)
        } else {
            None
        };
        let body = if let Some(tok) = self.peek() {
            match tok.kind {
                LBrace => Some(self.parse_block(false)?),
                Semicolon => {
                    self.get_token()?;
                    None
                }
                _ => {
                    return if ret.is_some() {
                        Err(self.expect_err(&[LBrace, Semicolon]))
                    } else {
                        Err(self.expect_err(&[Arrow, LBrace, Semicolon]))
                    };
                }
            }
        } else {
            return if ret.is_some() {
                Err(self.expect_err(&[LBrace, Semicolon]))
            } else {
                Err(self.expect_err(&[Arrow, LBrace, Semicolon]))
            };
        };
        let end = self.cur().unwrap();
        Ok(ast::Object::Fun {
            line_info: LineInfo::from_range(&start, &end),
            params,
            ret,
            body,
        })
    }

    // param ::= identifier ':' type;
    fn parse_param(&mut self) -> CompileResult<ast::Param> {
        let name = self.expect(Ident)?;
        self.expect(Colon)?;
        let taipe = self.parse_type()?;
        Ok(ast::Param { name, taipe })
    }

    // stmt := if_stmt | while_stmt | loop_stmt | block
    //       | 'yield' label? expr? ';'
    //       | 'continue' label? ';'
    //       | 'break' label? expr? ';'
    //       | 'return' expr ';'
    //       | expr ';'
    //       | ';'
    //       ;
    fn parse_stmt(&mut self) -> CompileResult<ast::Stmt> {
        if let Some(tok) = self.peek() {
            match tok.kind {
                If => self.parse_if_stmt(),
                Label => {
                    if let Some(tok) = self.peek_at(1) {
                        match tok.kind {
                            While => self.parse_while_stmt(),
                            Loop => self.parse_loop_stmt(),
                            LBrace => self.parse_block(true),
                            _ => Err(self.expect_err(&[While, Loop, LBrace])),
                        }
                    } else {
                        Err(self.expect_err(&[While, Loop, LBrace]))
                    }
                }
                While => self.parse_while_stmt(),
                Loop => self.parse_loop_stmt(),
                LBrace => self.parse_block(false),
                Yield => {
                    let token = self.get_token()?;
                    let label = if let Some(tok) = self.peek()
                        && tok.kind == Label
                    {
                        Some(self.get_token()?)
                    } else {
                        None
                    };
                    let expr = self.rule_optional(Self::parse_expr);
                    self.expect_term()?;
                    Ok(ast::Stmt::Single { token, label, expr })
                }
                Continue => {
                    let token = self.get_token()?;
                    let label = if let Some(tok) = self.peek()
                        && tok.kind == Label
                    {
                        Some(self.get_token()?)
                    } else {
                        None
                    };
                    self.expect_term()?;
                    Ok(ast::Stmt::Single {
                        token,
                        label,
                        expr: None,
                    })
                }
                Break => {
                    let token = self.get_token()?;
                    let label = if let Some(tok) = self.peek()
                        && tok.kind == Label
                    {
                        Some(self.get_token()?)
                    } else {
                        None
                    };
                    let expr = self.rule_optional(Self::parse_expr);
                    self.expect_term()?;
                    Ok(ast::Stmt::Single { token, label, expr })
                }
                Return => {
                    let token = self.get_token()?;
                    let expr = self.rule_optional(Self::parse_expr);
                    self.expect_term()?;
                    Ok(ast::Stmt::Single {
                        token,
                        label: None,
                        expr,
                    })
                }
                Semicolon => Ok(ast::Stmt::Nop(self.get_token()?)),
                _ => {
                    if self.is_expr_start() {
                        let expr = self.parse_expr()?;
                        self.expect_term()?;
                        Ok(ast::Stmt::Expr(Box::new(expr)))
                    } else {
                        Err(self.expect_err(&[
                            // Stmt begin tokens
                            If, Label, While, Loop, LBrace, Yield, Continue, Break, Return, //
                            // Expr begin tokens
                            Not, Plus, Minus, Tilde, Star, Ampersand, //
                            // Primary expr begin tokens
                            True, False, IntLit, FloatLit, Ident, LParen, //
                        ]))
                    }
                }
            }
        } else {
            Err(self.expect_err(&[
                // Stmt begin tokens
                If, Label, While, Loop, LBrace, Yield, Continue, Break, Return, //
                // Expr begin tokens
                Not, Plus, Minus, Tilde, Star, Ampersand, //
                // Primary expr begin tokens
                True, False, IntLit, FloatLit, Ident, LParen, //
            ]))
        }
    }

    // block ::= (<allow_label> label?) '{' (decl | stmt) '}';
    fn parse_block(&mut self, allow_label: bool) -> CompileResult<ast::Stmt> {
        let label = if allow_label
            && let Some(tok) = self.peek()
            && tok.kind == Label
        {
            Some(self.get_token()?)
        } else {
            None
        };
        let start = self.expect(LBrace)?;
        let mut stmts = Vec::new();
        while let Some(tok) = self.peek()
            && tok.kind != RBrace
        {
            stmts.push(self.rule_or(Self::parse_stmt, |parser| {
                Ok(ast::Stmt::Decl(Box::new(parser.parse_decl()?)))
            })?);
        }
        let end = self.expect(RBrace)?;
        Ok(ast::Stmt::Block {
            line_info: LineInfo::from_range(&start, &end),
            label,
            stmts,
        })
    }

    // if_stmt ::= 'if' expr block ('else' block)?;
    fn parse_if_stmt(&mut self) -> CompileResult<ast::Stmt> {
        let start = self.expect(If)?;
        let expr = self.parse_expr()?;
        let then_body = Box::new(self.parse_block(false)?);
        let else_body = if let Some(tok) = self.peek()
            && tok.kind == Else
        {
            Some(Box::new(self.parse_block(false)?))
        } else {
            None
        };
        let end = self.cur().unwrap();
        Ok(ast::Stmt::If {
            line_info: LineInfo::from_range(&start, &end),
            expr,
            then_body,
            else_body,
        })
    }

    // while_stmt ::= label? 'while' expr block ('else' block)?;
    fn parse_while_stmt(&mut self) -> CompileResult<ast::Stmt> {
        let label = if let Some(tok) = self.peek()
            && tok.kind == Label
        {
            Some(self.get_token()?)
        } else {
            None
        };
        let start = self.expect(While)?;
        let expr = self.parse_expr()?;
        let then_body = Box::new(self.parse_block(false)?);
        let else_body = if let Some(tok) = self.peek()
            && tok.kind == Else
        {
            Some(Box::new(self.parse_block(false)?))
        } else {
            None
        };
        let end = self.cur().unwrap();
        Ok(ast::Stmt::While {
            line_info: LineInfo::from_range(label.as_ref().unwrap_or(&start), &end),
            label,
            expr,
            then_body,
            else_body,
        })
    }

    // loop_stmt ::= label? 'loop' block;
    fn parse_loop_stmt(&mut self) -> CompileResult<ast::Stmt> {
        let label = if let Some(tok) = self.peek()
            && tok.kind == Label
        {
            Some(self.get_token()?)
        } else {
            None
        };
        let start = self.expect(Loop)?;
        let body = Box::new(self.parse_block(false)?);
        let end = self.cur().unwrap();
        Ok(ast::Stmt::Loop {
            line_info: LineInfo::from_range(label.as_ref().unwrap_or(&start), &end),
            body,
        })
    }

    // type_fun_param ::= identifier ':' type;
    fn parse_type_fun_param(&mut self) -> CompileResult<ast::TypeFunctionParam> {
        let name = self.expect(Ident)?;
        self.expect(Dot)?;
        let taipe = self.parse_type()?;
        Ok(ast::TypeFunctionParam { name, taipe })
    }

    // type ::= identifier ('.' identifier)*
    //        | 'fun' '(' type_fun_param_list ')' '->' type
    //        | 'const' type
    //        | '*' type
    //        | '[' type ';' ('_' | expr)']'
    //        | '[' type ']'
    //        | '(' type ')'
    //        | type_tuple
    //        | 'void' | 'noreturn' | 'type'
    //        ;
    fn parse_type(&mut self) -> CompileResult<ast::Type> {
        if let Some(tok) = self.peek() {
            match tok.kind {
                Ident => {
                    let mut items = Vec::new();
                    items.push(self.get_token()?);
                    while let Some(tok) = self.peek()
                        && tok.kind == Dot
                    {
                        self.get_token()?;
                        items.push(self.expect(Ident)?);
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
                Void | Noreturn | Type => Ok(ast::Type::Literal(self.get_token()?)),
                _ => Err(self.expect_err(&[
                    Ident, Fun, Const, Star, LBrack, LParen, Void, Noreturn, Type,
                ])),
            }
        } else {
            Err(self.expect_err(&[
                Ident, Fun, Const, Star, LBrack, LParen, Void, Noreturn, Type,
            ]))
        }
    }

    fn is_expr_start(&mut self) -> bool {
        [
            // Expr begin tokens
            Not, Plus, Minus, Tilde, Star, Ampersand, //
            // Primary expr begin tokens
            True, False, IntLit, FloatLit, Ident, LParen, //
        ]
        .into_iter()
        .any(|kind| {
            if let Some(tok) = self.peek() {
                kind == tok.kind
            } else {
                false
            }
        })
    }

    // expr ::= assigment | logic_or;
    fn parse_expr(&mut self) -> CompileResult<ast::Expr> {
        self.rule_or(Self::parse_assignment, Self::parse_logic_or)
    }

    // assignment ::= (<!empty>logic_or_list) '=' (<!empty>logic_or_list);
    fn parse_assignment(&mut self) -> CompileResult<ast::Expr> {
        let lhs = self.parse_logic_or_list();
        if lhs.is_empty() {
            return Err(self.make_error(
                &self.peek().unwrap(), // TODO: unwrap should be changed
                "expected left hand side of an assignment",
            ));
        }
        let op = self.expect(Equal)?;
        let rhs = self.parse_logic_or_list();
        if rhs.is_empty() {
            return Err(self.make_error(
                &self.peek().unwrap(), // TODO: unwrap should be changed
                "expected left hand side of an assignment",
            ));
        }
        Ok(ast::Expr::Assign { lhs, op, rhs })
    }

    // logic_or ::= logic_and ('^' logic_and)*;
    define_binary_op!(parse_logic_or, parse_logic_and, Or);
    // logic_and ::= logic_not ('^' logic_not)*;
    define_binary_op!(parse_logic_and, parse_logic_not, And);

    // logic_not ::= 'not'* relational;
    fn parse_logic_not(&mut self) -> CompileResult<ast::Expr> {
        let mut ops = Vec::new();
        while let Some(tok) = self.peek()
            && tok.kind == Not
        {
            ops.push(self.get_token()?);
        }
        let mut expr = self.parse_relational()?;
        for op in ops.into_iter().rev() {
            expr = ast::Expr::Unary {
                op: Some(op),
                expr: Box::new(expr),
            };
        }
        Ok(expr)
    }

    // relational ::= bit_or (('<'|'<='|'=='|'!='|'>='|'>') bit_or)*;
    define_binary_op!(
        parse_relational,
        parse_bit_or,
        LAngle,
        LessEq,
        EqEq,
        NotEq,
        GreaterEq,
        RAngle
    );
    // bit_or ::= bit_xor ('|' bit_xor)*;
    define_binary_op!(parse_bit_or, parse_bit_xor, Pipe);
    // bit_xor ::= bit_and ('^' bit_and)*;
    define_binary_op!(parse_bit_xor, parse_bit_and, Caret);
    // bit_and ::= shift ('&' shift)*;
    define_binary_op!(parse_bit_and, parse_shift, Ampersand);

    // shift ::= term (('<''<'|'>''>') term)*;
    fn parse_shift(&mut self) -> CompileResult<ast::Expr> {
        let mut left = self.parse_term()?;
        loop {
            if let Some(tok1) = self.peek()
                && let Some(tok2) = self.peek_at(1)
                && ((tok1.kind == LAngle && tok2.kind == LAngle)
                    || (tok1.kind == RAngle && tok2.kind == RAngle))
            {
                let op1 = self.get_token()?;
                let op2 = self.get_token()?;
                let right = self.parse_term()?;
                left = ast::Expr::Binary2 {
                    left: Box::new(left),
                    op1,
                    op2,
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    // term ::= factor (('+'('%'|':')?|'-'('%'|':')?) factor)*;
    define_binary_op!(
        parse_term,
        parse_factor,
        Plus,
        WrapPlus,
        SatPlus,
        Minus,
        WrapMinus,
        SatMinus
    );

    // factor ::= power (('*'|'/'|'%') power)*;
    fn parse_factor(&mut self) -> CompileResult<ast::Expr> {
        let mut left = self.parse_power()?;
        while let Some(tok) = self.peek()
            && (tok.kind == Star || tok.kind == Slash || tok.kind == Percent)
        {
            // let res = [Star, Slash,].iter().any(|&kind| tok.kind == kind);
            let op = self.get_token()?;
            let right = self.parse_power()?;
            left = ast::Expr::Binary {
                left: Box::new(left),
                op,
                right: Box::new(right),
            };
        }
        Ok(left)
    }

    // power ::= (cast '**')* cast;
    fn parse_power(&mut self) -> CompileResult<ast::Expr> {
        let mut left = self.parse_cast()?;
        while let Some(tok) = self.peek()
            && tok.kind == StarStar
        {
            let op = self.get_token()?;
            let right = self.parse_cast()?;
            left = if let ast::Expr::Binary {
                left: prev_left,
                op: prev_op,
                right: prev_right,
            } = left.clone() // TODO: clone is not the right thing
                && prev_op.kind == StarStar
            {
                ast::Expr::Binary {
                    left: prev_left,
                    op: prev_op,
                    right: Box::new(ast::Expr::Binary {
                        left: prev_right,
                        op,
                        right: Box::new(right),
                    }),
                }
            } else {
                ast::Expr::Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                }
            };
        }
        Ok(left)
    }

    // cast ::= unary ('as' type)*;
    fn parse_cast(&mut self) -> CompileResult<ast::Expr> {
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

    // unary ::= ('+'|'-'|'~'|'*'|'&') primary;
    fn parse_unary(&mut self) -> CompileResult<ast::Expr> {
        let op = if let Some(tok) = self.peek() {
            match tok.kind {
                Plus | Minus | Tilde | Star | Ampersand => Some(self.get_token()?),
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

    // arg ::= (identifer ':')? expr;
    fn parse_arg(&mut self) -> CompileResult<Arg> {
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

    // postifix ::= primary ('.' identifier | '(' args_list ')' | '[' expr_list ']');
    fn parse_postfix(&mut self) -> CompileResult<ast::Expr> {
        let mut expr = self.parse_primary()?;
        loop {
            if let Some(tok) = self.peek() {
                match tok.kind {
                    Dot => {
                        self.get_token()?;
                        let name = self.expect(Ident)?;
                        expr = ast::Expr::Member {
                            expr: Box::new(expr),
                            name,
                        };
                    }
                    LParen => {
                        self.get_token()?;
                        let args = self.parse_arg_list();
                        let end = self.expect(RParen)?;
                        expr = ast::Expr::Call {
                            line_info: LineInfo::from_range(&expr, &end),
                            expr: Box::new(expr),
                            args,
                        };
                    }
                    LBrack => {
                        self.get_token()?;
                        let items = self.parse_expr_list();
                        let end = self.expect(RBrack)?;
                        expr = ast::Expr::Index {
                            line_info: LineInfo::from_range(&expr, &end),
                            expr: Box::new(expr),
                            items,
                        };
                    }
                    _ => break,
                }
            } else {
                break;
            }
        }
        Ok(expr)
    }

    // primary ::= 'true' | 'false'
    //           | string | integer | float | identifier
    //           | '(' expr ')' | tuple
    //           | '[' expr_list ']';
    fn parse_primary(&mut self) -> CompileResult<ast::Expr> {
        if let Some(tok) = self.peek() {
            match tok.kind {
                True | False | StringLit | IntLit | FloatLit | Ident => {
                    Ok(ast::Expr::Literal(self.get_token()?))
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

    // type_tuple ::= '(' type_list ')';
    fn parse_type_tuple(&mut self) -> CompileResult<ast::Type> {
        let start = self.expect(LParen)?;
        let types = self.parse_type_list();
        let end = self.expect(RParen)?;
        Ok(ast::Type::Tuple {
            line_info: LineInfo::from_range(&start, &end),
            types,
        })
    }

    // tuple ::= '(' expr_list ')';
    fn parse_tuple(&mut self) -> CompileResult<ast::Expr> {
        let start = self.expect(LParen)?;
        let exprs = self.parse_expr_list();
        let end = self.expect(RParen)?;
        Ok(ast::Expr::Tuple {
            line_info: LineInfo::from_range(&start, &end),
            exprs,
        })
    }

    define_rule_list!(Param, parse_param_list, parse_param);
    define_rule_list!(
        TypeFunctionParam,
        parse_type_fun_param_list,
        parse_type_fun_param
    );
    define_rule_list!(Type, parse_type_list, parse_type);
    define_rule_list!(Expr, parse_logic_or_list, parse_logic_or);
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

    fn rule_or<T, F1, F2>(&mut self, rule1: F1, rule2: F2) -> CompileResult<T>
    where
        F1: Fn(&mut Parser) -> CompileResult<T>,
        F2: Fn(&mut Parser) -> CompileResult<T>,
    {
        let save = self.index;
        if let Ok(value) = rule1(self) {
            Ok(value)
        } else {
            self.index = save;
            rule2(self)
        }
    }

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

    fn get_last_line_info(&self) -> LineInfo {
        match self.tokens.last() {
            Some(tok) => LineInfo {
                line_start: tok.line_info.line_end,
                line_end: tok.line_info.line_end,
                col_start: tok.line_info.col_end,
                col_end: tok.line_info.col_end + 1,
            },
            None => LineInfo {
                line_start: 1,
                line_end: 1,
                col_start: 1,
                col_end: 2,
            },
        }
    }

    fn get_holy_line_info(&self, shit: Option<impl HasLineInfo>) -> LineInfo {
        if let Some(more_shit) = shit {
            more_shit.get_line_info()
        } else {
            self.get_last_line_info()
        }
    }

    fn expect_err_more(&self, items: &[&str], kinds: &[TokenKind]) -> CompileError {
        let mut msg = String::new();
        msg.push_str("expected ");
        for item in items {
            msg.push_str(item);
            msg.push_str(", ");
        }
        for kind in kinds {
            msg.push_str(kind.get_repr());
            msg.push_str(", ");
        }
        if items.len() > 0 || kinds.len() > 0 {
            msg.pop();
            msg.pop();
        }
        self.make_error(&self.get_holy_line_info(self.peek()), msg)
    }

    fn expect_err(&self, kinds: &[TokenKind]) -> CompileError {
        self.expect_err_more(&[], kinds)
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
            Err(self.make_error(&self.get_last_line_info(), "unexpected end of file"))
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
            Err(self.make_error(
                &self.get_holy_line_info(if let Some(tok) = self.cur() {
                    Some(LineInfo {
                        line_start: tok.line_info.line_end,
                        line_end: tok.line_info.line_end,
                        col_start: tok.line_info.col_end,
                        col_end: tok.line_info.col_end + 1,
                    })
                } else {
                    None
                }),
                format!("expected {}", kind.get_repr()),
            ))
        }
    }

    fn expect_term(&mut self) -> CompileResult<Token> {
        self.expect(Semicolon)
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
