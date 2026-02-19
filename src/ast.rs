use crate::{
    common::{HasLineInfo, LineInfo},
    lexer::Token,
};

pub struct TypeFunctionParam {
    pub name: Token,
    pub taipe: Type,
}

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

pub struct Arg {
    pub name: Option<Token>,
    pub expr: Expr,
}

pub enum Expr {
    Cast {
        expr: Box<Expr>,
        taipe: Box<Type>,
    },
    Unary {
        op: Option<Token>,
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
    // Statements as expressions
    Continue {
        line_info: LineInfo,
        label: Option<Token>,
    },
    Break {
        line_info: LineInfo,
        label: Option<Token>,
        expr: Option<Box<Expr>>,
    },
    Return {
        line_info: LineInfo,
        label: Option<Token>,
        expr: Option<Box<Expr>>,
    },
}

impl HasLineInfo for Type {
    fn get_line_info(&self) -> LineInfo {
        match self {
            Type::Path { items } => LineInfo::from_list(items),
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

impl HasLineInfo for Expr {
    fn get_line_info(&self) -> LineInfo {
        match self {
            Expr::Cast { expr, taipe } => LineInfo::from_range(expr, taipe),
            Expr::Unary { op, expr } => {
                if let Some(tok) = op {
                    LineInfo::from_range(tok, expr)
                } else {
                    expr.get_line_info()
                }
            }
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
            Expr::Continue {
                line_info,
                label: _,
            } => *line_info,
            Expr::Break {
                line_info,
                label: _,
                expr: _,
            } => *line_info,
            Expr::Return {
                line_info,
                label: _,
                expr: _,
            } => *line_info,
        }
    }
}
