use crate::{
    common::{HasLineInfo, LineInfo},
    lexer::Token,
};

pub enum Decl {
    Decl {
        name: Token,
        taipe: Option<Type>,
        eq_token: Option<Token>,
        object: Option<Object>,
    },
    Using {
        line_info: LineInfo,
        items: Vec<Token>,
    },
}

pub enum Object {
    ExternModule {
        line_info: LineInfo,
        value: Token,
    },
    Module {
        line_info: LineInfo,
        decls: Vec<Decl>,
    },
    Struct {
        line_info: LineInfo,
        decls: Vec<Decl>,
    },
    Union {
        line_info: LineInfo,
        decls: Vec<Decl>,
    },
    Fun {
        line_info: LineInfo,
        params: Vec<Param>,
        ret: Option<Type>,
        body: Option<Stmt>,
    },
    Typedef(Type),
    Expr(Expr),
}

pub struct Param {
    pub name: Token,
    pub taipe: Type,
}

pub enum Stmt {
    If {
        line_info: LineInfo,
        expr: Expr,
        then_body: Box<Stmt>,
        else_body: Option<Box<Stmt>>,
    },
    While {
        line_info: LineInfo,
        label: Option<Token>,
        expr: Expr,
        then_body: Box<Stmt>,
        else_body: Option<Box<Stmt>>,
    },
    Loop {
        line_info: LineInfo,
        body: Box<Stmt>,
    },
    Block {
        line_info: LineInfo,
        label: Option<Token>,
        stmts: Vec<Stmt>,
    },
    Yield {
        token: Token,
        label: Option<Token>,
        expr: Option<Expr>,
    },
    Continue {
        token: Token,
        label: Option<Token>,
    },
    Break {
        token: Token,
        label: Option<Token>,
        expr: Option<Expr>,
    },
    Return {
        token: Token,
        expr: Option<Expr>,
    },
    Decl(Box<Decl>),
    Expr(Box<Expr>),
    Nop(Token),
}

#[derive(Clone)]
pub struct TypeFunctionParam {
    pub name: Option<Token>,
    pub taipe: Type,
}

#[derive(Clone)]
pub enum Type {
    Path {
        items: Vec<Token>,
    },
    Function {
        line_info: LineInfo,
        params: Vec<TypeFunctionParam>,
        ret: Box<Type>,
    },
    Const {
        token: Token,
        taipe: Box<Type>,
    },
    Pointer {
        token: Token,
        taipe: Box<Type>,
    },
    Array {
        line_info: LineInfo,
        taipe: Box<Type>,
        expr: Option<Expr>,
    },
    Fat {
        line_info: LineInfo,
        taipe: Box<Type>,
    },
    Paren {
        line_info: LineInfo,
        taipe: Box<Type>,
    },
    Tuple {
        line_info: LineInfo,
        types: Vec<Type>,
    },
    Literal(Token),
}

#[derive(Clone)]
pub struct Arg {
    pub name: Option<Token>,
    pub expr: Expr,
}

#[derive(Clone)]
pub enum Expr {
    Assign {
        lhs: Vec<Expr>,
        op: Token,
        rhs: Vec<Expr>,
    },
    Binary2 {
        left: Box<Expr>,
        op1: Token,
        op2: Token,
        right: Box<Expr>,
    },
    Binary {
        left: Box<Expr>,
        op: Token,
        right: Box<Expr>,
    },
    Cast {
        expr: Box<Expr>,
        taipe: Box<Type>,
    },
    Unary {
        op: Token,
        expr: Box<Expr>,
    },
    // Postfix
    Member {
        expr: Box<Expr>,
        name: Token,
    },
    Call {
        line_info: LineInfo,
        expr: Box<Expr>,
        args: Vec<Arg>,
    },
    Index {
        line_info: LineInfo,
        expr: Box<Expr>,
        items: Vec<Expr>,
    },
    // Primary expression
    Literal(Token),
    Paren {
        line_info: LineInfo,
        expr: Box<Expr>,
    },
    Tuple {
        line_info: LineInfo,
        exprs: Vec<Expr>,
    },
    ArrayLit {
        line_info: LineInfo,
        items: Vec<Expr>,
    },
}

impl Object {
    pub fn get_decls(&self) -> Option<&[Decl]> {
        match self {
            Object::ExternModule {
                line_info: _,
                value: _,
            } => None,
            Object::Module {
                line_info: _,
                decls,
            } => Some(&decls),
            Object::Struct {
                line_info: _,
                decls,
            } => Some(&decls),
            Object::Union {
                line_info: _,
                decls,
            } => Some(&decls),
            Object::Fun {
                line_info: _,
                params: _,
                ret: _,
                body: _,
            } => None,
            Object::Typedef(_) => None,
            Object::Expr(_) => None,
        }
    }
}

impl HasLineInfo for Decl {
    fn get_line_info(&self) -> LineInfo {
        match self {
            Decl::Decl {
                name,
                taipe,
                eq_token: _,
                object,
            } => {
                if let Some(obj) = object {
                    LineInfo::from_range(name, obj)
                } else if let Some(t) = taipe {
                    LineInfo::from_range(name, t)
                } else {
                    name.get_line_info()
                }
            }
            Decl::Using {
                line_info,
                items: _,
            } => *line_info,
        }
    }
}

impl HasLineInfo for Object {
    fn get_line_info(&self) -> LineInfo {
        match self {
            Object::ExternModule {
                line_info,
                value: _,
            } => *line_info,
            Object::Module {
                line_info,
                decls: _,
            } => *line_info,
            Object::Struct {
                line_info,
                decls: _,
            } => *line_info,
            Object::Union {
                line_info,
                decls: _,
            } => *line_info,
            Object::Fun {
                line_info,
                params: _,
                ret: _,
                body: _,
            } => *line_info,
            Object::Typedef(taipe) => taipe.get_line_info(),
            Object::Expr(expr) => expr.get_line_info(),
        }
    }
}

impl HasLineInfo for Param {
    fn get_line_info(&self) -> LineInfo {
        LineInfo::from_range(&self.name, &self.taipe)
    }
}

impl HasLineInfo for Stmt {
    fn get_line_info(&self) -> LineInfo {
        match self {
            Stmt::If {
                line_info,
                expr: _,
                then_body: _,
                else_body: _,
            } => *line_info,
            Stmt::While {
                line_info,
                label: _,
                expr: _,
                then_body: _,
                else_body: _,
            } => *line_info,
            Stmt::Loop { line_info, body: _ } => *line_info,
            Stmt::Block {
                line_info,
                label: _,
                stmts: _,
            } => *line_info,
            Stmt::Yield { token, label, expr } => {
                if let Some(e) = expr {
                    LineInfo::from_range(token, e)
                } else if let Some(l) = label {
                    LineInfo::from_range(token, l)
                } else {
                    token.get_line_info()
                }
            }
            Stmt::Continue { token, label } => {
                if let Some(l) = label {
                    LineInfo::from_range(token, l)
                } else {
                    token.get_line_info()
                }
            }
            Stmt::Break { token, label, expr } => {
                if let Some(e) = expr {
                    LineInfo::from_range(token, e)
                } else if let Some(l) = label {
                    LineInfo::from_range(token, l)
                } else {
                    token.get_line_info()
                }
            }
            Stmt::Return { token, expr } => {
                if let Some(e) = expr {
                    LineInfo::from_range(token, e)
                } else {
                    token.get_line_info()
                }
            }
            Stmt::Decl(decl) => decl.get_line_info(),
            Stmt::Expr(expr) => expr.get_line_info(),
            Stmt::Nop(token) => token.get_line_info(),
        }
    }
}

impl HasLineInfo for Type {
    fn get_line_info(&self) -> LineInfo {
        match self {
            Type::Path { items } => items.get_line_info(),
            Type::Function {
                line_info,
                params: _,
                ret: _,
            } => *line_info,
            Type::Const { token, taipe } => LineInfo::from_range(token, taipe),
            Type::Pointer { token, taipe } => LineInfo::from_range(token, taipe),
            Type::Array {
                line_info,
                taipe: _,
                expr: _,
            } => *line_info,
            Type::Fat {
                line_info,
                taipe: _,
            } => *line_info,
            Type::Paren {
                line_info,
                taipe: _,
            } => *line_info,
            Type::Tuple {
                line_info,
                types: _,
            } => *line_info,
            Type::Literal(token) => token.get_line_info(),
        }
    }
}

impl HasLineInfo for TypeFunctionParam {
    fn get_line_info(&self) -> LineInfo {
        if let Some(name) = &self.name {
            LineInfo::from_range(name, &self.taipe)
        } else {
            self.taipe.get_line_info()
        }
    }
}

impl HasLineInfo for Arg {
    fn get_line_info(&self) -> LineInfo {
        if let Some(name) = &self.name {
            LineInfo::from_range(name, &self.expr)
        } else {
            self.expr.get_line_info()
        }
    }
}

impl HasLineInfo for Expr {
    fn get_line_info(&self) -> LineInfo {
        match self {
            Expr::Assign { lhs, op: _, rhs } => LineInfo::from_range(lhs, rhs),
            Expr::Binary2 {
                left,
                op1: _,
                op2: _,
                right,
            } => LineInfo::from_range(left, right),
            Expr::Binary { left, op: _, right } => LineInfo::from_range(left, right),
            Expr::Cast { expr, taipe } => LineInfo::from_range(expr, taipe),
            Expr::Unary { op, expr } => LineInfo::from_range(op, expr),
            Expr::Member { expr, name } => LineInfo::from_range(expr, name),
            Expr::Call {
                line_info,
                expr: _,
                args: _,
            } => *line_info,
            Expr::Index {
                line_info,
                expr: _,
                items: _,
            } => *line_info,
            Expr::Literal(token) => token.get_line_info(),
            Expr::Paren { line_info, expr: _ } => *line_info,
            Expr::Tuple {
                line_info,
                exprs: _,
            } => *line_info,
            Expr::ArrayLit {
                line_info,
                items: _,
            } => *line_info,
        }
    }
}
