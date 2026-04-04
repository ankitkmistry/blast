use crate::{
    ast,
    common::{CompileError, CompileResult, HasLineInfo, LineInfo},
    lexer::{
        Token,
        TokenKind::{self, *},
    },
};

pub struct Parser {
    file_path: String,
    tokens: Vec<Token>,
    index: usize,

    errors: Vec<CompileError>,
}

macro_rules! define_rule_list {
    ($type: path, $rule_result: ident, $rule_from: ident) => {
        fn $rule_result(&mut self) -> Vec<$type> {
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
    pub fn new(file_path: &str, tokens: &[Token]) -> CompileResult<Self> {
        Ok(Self {
            file_path: file_path.to_owned(),
            tokens: tokens.to_owned(),
            index: 0,
            errors: Vec::new(),
        })
    }

    // program ::= decls;
    pub fn parse(&mut self) -> CompileResult<ast::Object> {
        let decls = self.parse_decls()?;
        if self.errors.is_empty() {
            Ok(ast::Object::Module {
                line_info: decls.get_line_info(),
                decls,
            })
        } else {
            Err(CompileError::Errors(self.errors.clone()))
        }
    }

    // decl ::= (identifier | '_') ':' type (';' | ((':'|'=') object))
    //        | (identifier | '_') ':' ((':'|'=') object)
    //        | 'using' identifier ('.' identifier)* ('.' '*')
    //        ;
    fn parse_decl(&mut self) -> CompileResult<ast::Decl> {
        if let Some(tok) = self.peek() {
            match tok.kind {
                Ident | Underscore => {
                    let name = self.get_token()?;
                    self.expect(Colon)?;
                    if let Some(taipe) = self.rule_optional(Self::parse_type) {
                        if let Some(tok) = self.peek()
                            && (tok.kind == Equal || tok.kind == Colon)
                        {
                            let eq_tok = self.get_token()?;
                            let object = self.parse_object()?;
                            Ok(ast::Decl::Decl {
                                name,
                                taipe: Some(taipe),
                                eq_token: Some(eq_tok),
                                object: Some(object),
                            })
                        } else {
                            self.expect_term()?;
                            Ok(ast::Decl::Decl {
                                name,
                                taipe: Some(taipe),
                                eq_token: None,
                                object: None,
                            })
                        }
                    } else {
                        if let Some(tok) = self.peek()
                            && (tok.kind == Equal || tok.kind == Colon)
                        {
                            let eq_tok = self.get_token()?;
                            let object = self.parse_object()?;
                            Ok(ast::Decl::Decl {
                                name,
                                taipe: None,
                                eq_token: Some(eq_tok),
                                object: Some(object),
                            })
                        } else {
                            Err(self.expect_err_more(&["<type>"], &[Equal, Colon]))
                        }
                    }
                }
                Using => {
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
                    Ok(ast::Decl::Using {
                        line_info: LineInfo::from_range(&start, &end),
                        items,
                    })
                }
                _ => Err(self.expect_err(&[Ident, Underscore, Using])),
            }
        } else {
            Err(self.expect_err(&[Ident, Underscore, Using]))
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
    //          | 'typedef' type ';'
    //          | expr ';'
    //          ;
    fn parse_object(&mut self) -> CompileResult<ast::Object> {
        if let Some(tok) = self.peek() {
            match tok.kind {
                Module => self.parse_module(),
                Struct => self.parse_struct(),
                Union => self.parse_union(),
                Fun => self.parse_fun(),
                Typedef => {
                    self.get_token()?;
                    let result = ast::Object::Typedef(self.parse_type()?);
                    self.expect_term()?;
                    Ok(result)
                }
                _ => {
                    if self.is_expr_start() {
                        let expr = self.parse_expr()?;
                        self.expect_term()?;
                        Ok(ast::Object::Expr(expr))
                    } else {
                        Err(self.expect_err_more(&["<expression>"], &[Module, Struct, Union, Fun, Typedef]))
                    }
                }
            }
        } else {
            Err(self.expect_err_more(&["<expression>"], &[Module, Struct, Union, Fun, Typedef]))
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

    // struct ::= 'struct' '{' field_list '}';
    fn parse_struct(&mut self) -> CompileResult<ast::Object> {
        let start = self.expect(Struct)?;
        self.expect(LBrace)?;
        let fields = self.parse_field_list();
        let end = self.expect(RBrace)?;
        Ok(ast::Object::Compound {
            line_info: LineInfo::from_range(&start, &end),
            field: ast::Field::Compound {
                line_info: LineInfo::from_range(&start, &end),
                token: start,
                fields,
            },
        })
    }

    // union ::= 'union' '{' field_list '}';
    fn parse_union(&mut self) -> CompileResult<ast::Object> {
        let start = self.expect(Union)?;
        self.expect(LBrace)?;
        let fields = self.parse_field_list();
        let end = self.expect(RBrace)?;
        Ok(ast::Object::Compound {
            line_info: LineInfo::from_range(&start, &end),
            field: ast::Field::Compound {
                line_info: LineInfo::from_range(&start, &end),
                token: start,
                fields,
            },
        })
    }

    // field ::= (identifier | '_') ':' type ((':'|'=') expr)?
    //         | 'struct' '{' field_list '}'
    //         | 'union' '{' field_list '}'
    //         ;
    fn parse_field(&mut self) -> CompileResult<ast::Field> {
        if let Some(tok) = self.peek() {
            match tok.kind {
                Ident | Underscore => {
                    let name = self.get_token()?;
                    self.expect(Colon)?;
                    let taipe = self.parse_type()?;
                    if let Some(tok) = self.peek()
                        && (tok.kind == Equal || tok.kind == Colon)
                    {
                        let eq_tok = self.get_token()?;
                        let expr = self.parse_expr()?;
                        Ok(ast::Field::Decl {
                            name,
                            taipe,
                            eq_token: Some(eq_tok),
                            expr: Some(expr),
                        })
                    } else {
                        Ok(ast::Field::Decl {
                            name,
                            taipe,
                            eq_token: None,
                            expr: None,
                        })
                    }
                }
                Struct | Union => {
                    let token = self.get_token()?;
                    self.expect(LBrace)?;
                    let fields = self.parse_field_list();
                    let end = self.expect(RBrace)?;
                    Ok(ast::Field::Compound {
                        line_info: LineInfo::from_range(&token, &end),
                        token,
                        fields,
                    })
                }
                _ => Err(self.expect_err(&[Ident, Underscore, Struct, Union])),
            }
        } else {
            Err(self.expect_err(&[Ident, Underscore, Struct, Union]))
        }
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
                LBrace => Some(self.parse_block()?),
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

    // param ::= identifier ':' type ((':'|'=') expr)?;
    fn parse_param(&mut self) -> CompileResult<ast::Param> {
        let name = self.expect(Ident)?;
        self.expect(Colon)?;
        let taipe = self.parse_type()?;
        if let Some(tok) = self.peek()
            && (tok.kind == Colon || tok.kind == Equal)
        {
            let eq_token = self.get_token()?;
            let expr = self.parse_expr()?;
            Ok(ast::Param {
                name,
                taipe,
                eq_token: Some(eq_token),
                expr: Some(expr),
            })
        } else {
            Ok(ast::Param {
                name,
                taipe,
                eq_token: None,
                expr: None,
            })
        }
    }

    // stmt := if_stmt | while_stmt
    //       | block
    //       | 'yield' expr ';'
    //       | 'continue' label? ';'
    //       | 'break' label? ';'
    //       | 'return' expr? ';'
    //       | expr_or_assign ';'
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
                            LBrace => self.parse_block(),
                            _ => Err(self.expect_err(&[While, LBrace])),
                        }
                    } else {
                        Err(self.expect_err(&[While, LBrace]))
                    }
                }
                While => self.parse_while_stmt(),
                LBrace => self.parse_block(),
                Yield => {
                    let token = self.get_token()?;
                    let expr = self.parse_expr()?;
                    self.expect_term()?;
                    Ok(ast::Stmt::Yield { token, expr })
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
                    Ok(ast::Stmt::Continue { token, label })
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
                    self.expect_term()?;
                    Ok(ast::Stmt::Break { token, label })
                }
                Return => {
                    let token = self.get_token()?;
                    let expr = self.rule_optional(Self::parse_expr);
                    self.expect_term()?;
                    Ok(ast::Stmt::Return { token, expr })
                }
                Semicolon => Ok(ast::Stmt::Nop(self.get_token()?)),
                _ => {
                    if self.is_expr_start() {
                        let expr = self.parse_expr_or_assign()?;
                        self.expect_term()?;
                        Ok(ast::Stmt::Expr(Box::new(expr)))
                    } else {
                        Err(self.expect_err_more(
                            &["<expression>"],
                            &[If, Label, While, LBrace, Yield, Continue, Break, Return],
                        ))
                    }
                }
            }
        } else {
            Err(self.expect_err_more(
                &["<expression>"],
                &[If, Label, While, LBrace, Yield, Continue, Break, Return],
            ))
        }
    }

    // block ::= '{' (decl | stmt) '}';
    fn parse_block(&mut self) -> CompileResult<ast::Stmt> {
        let start = self.expect(LBrace)?;
        let mut stmts = Vec::new();
        while let Some(tok) = self.peek()
            && tok.kind != RBrace
        {
            stmts.push(self.rule_or(
                |parser| Ok(ast::Stmt::Decl(Box::new(parser.parse_decl()?))),
                Self::parse_stmt,
            )?);
        }
        let end = self.expect(RBrace)?;
        Ok(ast::Stmt::Block {
            line_info: LineInfo::from_range(&start, &end),
            stmts,
        })
    }

    // if_stmt ::= 'if' expr block ('else' block)?;
    fn parse_if_stmt(&mut self) -> CompileResult<ast::Stmt> {
        let start = self.expect(If)?;
        let expr = self.parse_expr()?;
        let then_body = Box::new(self.parse_block()?);
        let else_body = if let Some(tok) = self.peek()
            && tok.kind == Else
        {
            self.get_token()?;
            Some(Box::new(self.parse_block()?))
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

    // while_stmt ::= label? 'while' expr block;
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
        let then_body = Box::new(self.parse_block()?);
        let end = self.cur().unwrap();
        Ok(ast::Stmt::While {
            line_info: LineInfo::from_range(label.as_ref().unwrap_or(&start), &end),
            label,
            expr,
            then_body,
        })
    }

    // type ::= identifier ('.' identifier)*
    //        | 'fun' '(' type_list ')' '->' type
    //        | 'const' type                 # duplicate const is handled in the parser
    //        | '*' type
    //        | '[' ('_' | expr) ']' type
    //        | '['']' type
    //        | '(' type ')'
    //        | type_tuple
    //        | 'void' | 'noreturn' | 'typedef'
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
                    let params = self.parse_type_list();
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
                    if let Some(tok) = self.peek()
                        && tok.kind == Const
                    {
                        return Err(self.make_error(&tok, "duplicate 'const' is not allowed"));
                    }
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
                    if let Some(tok) = self.peek()
                        && tok.kind == RBrack
                    {
                        self.get_token()?;
                        let taipe = self.parse_type()?;
                        let end = self.cur().unwrap();
                        Ok(ast::Type::Fat {
                            line_info: LineInfo::from_range(&start, &end),
                            taipe: Box::new(taipe),
                        })
                    } else {
                        let expr = if let Some(tok) = self.peek()
                            && tok.kind == Underscore
                        {
                            self.get_token()?;
                            None
                        } else {
                            Some(self.parse_expr()?)
                        };
                        self.expect(RBrack)?;
                        let taipe = self.parse_type()?;
                        let end = self.cur().unwrap();
                        Ok(ast::Type::Array {
                            line_info: LineInfo::from_range(&start, &end),
                            taipe: Box::new(taipe),
                            expr,
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
                Void | Noreturn | Typedef => Ok(ast::Type::Literal(self.get_token()?)),
                _ => Err(self.expect_err(&[Ident, Fun, Const, Star, LBrack, LParen, Void, Noreturn, Typedef])),
            }
        } else {
            Err(self.expect_err(&[Ident, Fun, Const, Star, LBrack, LParen, Void, Noreturn, Typedef]))
        }
    }

    fn is_expr_start(&mut self) -> bool {
        let Some(peek) = self.peek() else {
            return false;
        };
        [
            // Expr begin tokens
            Not, Plus, Minus, Tilde, Star, Ampersand, Sizeof, Alignof, Typeof, //
            // Primary expr begin tokens
            True, False, StringLit, IntLit, FloatLit, Ident, LParen, LBrace, LBrack, //
        ]
        .into_iter()
        .any(|kind| kind == peek.kind)
    }

    // expr_or_assign ::= assigment | expr;
    fn parse_expr_or_assign(&mut self) -> CompileResult<ast::Expr> {
        self.rule_or(Self::parse_assignment, Self::parse_logical)
    }

    // expr ::= logical;
    fn parse_expr(&mut self) -> CompileResult<ast::Expr> {
        self.parse_logical()
    }

    // assignment ::= (<!empty>logic_or_list) '=' (<!empty>logic_or_list);
    fn parse_assignment(&mut self) -> CompileResult<ast::Expr> {
        let lhs = self.parse_logical_list();
        if lhs.is_empty() {
            return Err(self.make_error_peek("expected left hand size of an assignment"));
        }
        let op = self.expect(Equal)?;
        let rhs = self.parse_logical_list();
        if rhs.is_empty() {
            return Err(self.make_error_peek("expected right hand size of an assignment"));
        }
        Ok(ast::Expr::Assign {
            lhses: lhs,
            op,
            rhses: rhs,
        })
    }

    // logical ::= logic_not (('and'|'or') logic_not)*;
    define_binary_op!(parse_logical, parse_logic_not, And, Or);

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
                op,
                expr: Box::new(expr),
            };
        }
        Ok(expr)
    }

    // relational ::= bitwise (('<'|'<='|'=='|'!='|'>='|'>') bitwise)*;
    define_binary_op!(
        parse_relational,
        parse_bitwise,
        LAngle,
        LessEq,
        EqEq,
        NotEq,
        GreaterEq,
        RAngle
    );
    // bitwise ::= shift (('&'|'^'|'|') shift)*;
    define_binary_op!(parse_bitwise, parse_shift, Ampersand, Caret, Pipe);

    // shift ::= term (('<<'|'>>') term)*;
    fn parse_shift(&mut self) -> CompileResult<ast::Expr> {
        let mut left = self.parse_term()?;
        loop {
            if let Some(tok) = self.peek()
                && (tok.kind == ShiftLeft || tok.kind == ShiftRight)
            {
                let op = self.get_token()?;
                let right = self.parse_term()?;
                left = ast::Expr::Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                };
            } else {
                break;
            }
        }
        Ok(left)
    }

    // term ::= factor (('+'('%'|':')?|'-'('%'|':')?) factor)*;
    define_binary_op!(parse_term, parse_factor, Plus, Minus,);

    // factor ::= cast (('*'|'/'|'%') cast)*;
    define_binary_op!(parse_factor, parse_cast, Star, Slash, Percent);

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

    // unary ::= ('sizeof'|'typeof'|'alignof')? ('-'|'~'|'*'|'&')* primary;
    fn parse_unary(&mut self) -> CompileResult<ast::Expr> {
        let mut ops = Vec::new();
        loop {
            if let Some(tok) = self.peek() {
                match tok.kind {
                    Minus | Tilde | Star | Ampersand => {
                        ops.push(self.get_token()?);
                    }
                    Sizeof | Typeof | Alignof => {
                        ops.push(self.get_token()?);
                        break;
                    }
                    _ => break,
                }
            } else {
                break;
            }
        }
        let mut expr = self.parse_postfix()?;
        for op in ops.into_iter().rev() {
            expr = ast::Expr::Unary {
                op,
                expr: Box::new(expr),
            };
        }
        Ok(expr)
    }

    // arg ::= (identifer ':')? expr;
    fn parse_arg(&mut self) -> CompileResult<ast::Arg> {
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
        Ok(ast::Arg { name, expr })
    }

    // postifix ::= primary ('.' (identifier | integer) | '(' args_list ')' | '[' expr_list ']')*;
    fn parse_postfix(&mut self) -> CompileResult<ast::Expr> {
        let mut expr = self.parse_primary()?;
        loop {
            if let Some(tok) = self.peek() {
                match tok.kind {
                    Dot => {
                        self.get_token()?;
                        let name = if let Some(tok) = self.peek()
                            && (tok.kind == Ident || tok.kind == IntLit)
                        {
                            self.get_token()?
                        } else {
                            return Err(self.expect_err(&[Ident, IntLit]));
                        };
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
    //           | '[' expr_list ']'
    //           ;
    fn parse_primary(&mut self) -> CompileResult<ast::Expr> {
        if let Some(tok) = self.peek() {
            match tok.kind {
                True | False | StringLit | IntLit | FloatLit | Ident => Ok(ast::Expr::Literal(self.get_token()?)),
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
                LBrack => {
                    let start = self.get_token()?;
                    let items = self.parse_expr_list();
                    let end = self.expect(RBrack)?;
                    Ok(ast::Expr::ArrayLit {
                        line_info: LineInfo::from_range(&start, &end),
                        items,
                    })
                }
                _ => Err(self.expect_err(&[
                    True, False, IntLit, FloatLit, Ident, LParen, LBrace, LBrack, If, While, Break, Continue, Return,
                ])),
            }
        } else {
            Err(self.expect_err(&[
                True, False, IntLit, FloatLit, Ident, LParen, LBrace, LBrack, If, While, Break, Continue, Return,
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

    define_rule_list!(crate::ast::Field, parse_field_list, parse_field);
    define_rule_list!(crate::ast::Param, parse_param_list, parse_param);
    define_rule_list!(crate::ast::Type, parse_type_list, parse_type);
    define_rule_list!(crate::ast::Expr, parse_logical_list, parse_logical);
    define_rule_list!(crate::ast::Arg, parse_arg_list, parse_arg);
    define_rule_list!(crate::ast::Expr, parse_expr_list, parse_expr);

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
        let errors_save = self.errors.clone();
        if let Ok(value) = rule1(self) {
            Ok(value)
        } else {
            self.index = save;
            self.errors = errors_save;
            rule2(self)
        }
    }

    fn rule_optional<T, F>(&mut self, rule: F) -> Option<T>
    where
        F: Fn(&mut Parser) -> CompileResult<T>,
    {
        let save = self.index;
        let errors_save = self.errors.clone();
        if let Ok(value) = rule(self) {
            Some(value)
        } else {
            self.index = save;
            self.errors = errors_save;
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
        assert!(!items.is_empty() || !kinds.is_empty());

        let mut elements = Vec::new();
        for item in items {
            elements.push(item.to_string());
        }
        for kind in kinds {
            elements.push(kind.get_repr().to_string());
        }

        let mut msg = String::new();
        msg.push_str("expected ");

        let count = elements.len();
        let mut i = 0;
        for element in elements {
            msg.push_str(&element);
            if count >= 2 {
                if i < count - 2 {
                    msg.push_str(", ");
                } else if i == count - 2 {
                    msg.push_str(" or ");
                }
            }
            i += 1;
        }
        let line_info = self.get_holy_line_info(self.cur().map(|tok| LineInfo {
            line_start: tok.line_info.line_end,
            line_end: tok.line_info.line_end,
            col_start: tok.line_info.col_end,
            col_end: tok.line_info.col_end + 1,
        }));
        self.make_error(&line_info, msg)
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

    fn expect_term(&mut self) -> CompileResult<Token> {
        self.expect(Semicolon)
    }

    fn expect(&mut self, kind: TokenKind) -> CompileResult<Token> {
        if self.check(kind) {
            Ok(self.cur().unwrap())
        } else {
            let line_info = self.get_holy_line_info(self.cur().map(|tok| LineInfo {
                line_start: tok.line_info.line_end,
                line_end: tok.line_info.line_end,
                col_start: tok.line_info.col_end,
                col_end: tok.line_info.col_end + 1,
            }));
            match kind {
                Semicolon | RParen | RBrace | RBrack => Ok(self.recover_error(kind, line_info)),
                _ => Err(self.make_error(&line_info, format!("expected {}", kind.get_repr()))),
            }
        }
    }

    fn recover_error(&mut self, kind: TokenKind, line_info: LineInfo) -> Token {
        self.errors
            .push(self.make_error(&line_info, format!("expected {}", kind.get_repr())));
        Token {
            line_info,
            kind,
            text: kind.get_repr()[1..kind.get_repr().len() - 1].to_owned(),
            value: None,
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

    fn make_error_peek(&self, msg: impl ToString) -> CompileError {
        let line_info = self.get_holy_line_info(self.peek().map(|tok| tok.get_line_info()));
        CompileError::ParserError {
            file_path: self.file_path.clone(),
            line_info: line_info,
            msg: msg.to_string(),
        }
    }
}
