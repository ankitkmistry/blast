use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    fmt::{self, Write},
    fs,
    rc::Rc,
};

use color_print::{cprint, cprintln, cwrite};

use crate::{
    ast,
    common::{CompileError, HasLineInfo, LineInfo},
    lexer::Token,
    scope,
};

enum DiagKind {
    Error,
    Warning,
    Note,
}

pub fn print_error(err: CompileError) {
    match err {
        CompileError::LexerError {
            file_path,
            line_info,
            msg,
        } => print_diagnostic(DiagKind::Error, &file_path, line_info, &msg),
        CompileError::ParserError {
            file_path,
            line_info,
            msg,
        } => print_diagnostic(DiagKind::Error, &file_path, line_info, &msg),
        CompileError::Errors(errs) => {
            for err in errs {
                print_error(err);
            }
        }
        CompileError::SemError {
            file_path,
            line_info,
            msg,
        } => print_diagnostic(DiagKind::Error, &file_path, line_info, &msg),
        CompileError::SemWarning {
            file_path,
            line_info,
            msg,
        } => print_diagnostic(DiagKind::Warning, &file_path, line_info, &msg),
        CompileError::SemNote {
            file_path,
            line_info,
            msg,
        } => print_diagnostic(DiagKind::Note, &file_path, line_info, &msg),
        CompileError::SemHelp { msg } => print_help(&msg),
        CompileError::SemCyclic {
            file_path: _,
            line_info: _,
        } => unreachable!("this error is not supposed to come here"),
    }
}

fn interpolate_char(c1: char, c2: char) -> char {
    // This function handles \t and other kind of whitespaces
    // But ignores normal ' '
    if c1 != ' ' && c1.is_whitespace() {
        c1
    } else {
        c2
    }
}

fn num_digits(x: usize) -> usize {
    if x < 10 {
        1
    } else if x < 100 {
        2
    } else if x < 1000 {
        3
    } else if x < 10000 {
        4
    } else if x < 100000 {
        5
    } else if x < 1000000 {
        6
    } else if x < 10000000 {
        7
    } else if x < 100000000 {
        8
    } else if x < 1000000000 {
        9
    } else if x < 10000000000 {
        10
    } else {
        x.to_string().len()
    }
}

fn process_err_msg(msg: &str) -> String {
    let mut result = String::new();
    let mut flag = None;
    let mut flag_color_r = 0xFF;
    let mut flag_color_g = 0xFF;
    let mut flag_color_b = 0xFF;
    for i in 0..msg.chars().count() {
        let c = msg.chars().nth(i).unwrap();
        // FIXME: string lexer errors are not reported correctly
        if c == '\'' {
            if let Some(c) = flag
                && c == '\''
            {
                flag = None;
                continue;
            }
            flag = Some('\'');
            flag_color_r = 214;
            flag_color_g = 25;
            flag_color_b = 224;
        } else if c == '<' {
            flag = Some('<');
            flag_color_r = 3;
            flag_color_g = 189;
            flag_color_b = 187;
        } else if c == '>'
            && let Some(c) = flag
            && c == '<'
        {
            flag = None;
        } else {
            if flag.is_some() {
                result = format!(
                    "{}\x1b[1m\x1b[38;2;{};{};{}m{}\x1b[0m",
                    result, flag_color_r, flag_color_g, flag_color_b, c
                );
            } else {
                result.push(c);
            }
        }
    }
    result
}

fn print_help(msg: &str) {
    // cprint!("<g,s>help</>: ");
    cprint!("<rgb(0,230,0),s>help</>: ");
    cprintln!("<s>{}</>", process_err_msg(msg));
}

fn print_diagnostic(kind: DiagKind, file_path: &str, line_info: LineInfo, msg: &str) {
    let underline_char = match kind {
        DiagKind::Error => {
            cprint!("<r,s>error</>: ");
            '^'
        }
        DiagKind::Note => {
            // cprint!("<b,s>note</>: ");
            cprint!("<rgb(7,172,242),s>note</>: ");
            '-'
        }
        DiagKind::Warning => {
            cprint!("<y,s>warning</>: ");
            '~'
        }
    };
    cprintln!("<s>{}</>", process_err_msg(msg));
    cprintln!(
        "in file: <rgb(78,142,211)>{}</>:<m!>{}</>:<m!>{}</>",
        file_path,
        line_info.line_start,
        line_info.col_start
    );

    let line_column_width = num_digits(line_info.line_end) + 2;

    for (i, line) in fs::read_to_string(file_path)
        .unwrap()
        .split('\n')
        .skip(line_info.line_start - 1)
        .take(line_info.line_end - line_info.line_start + 1)
        .enumerate()
    {
        let lineno = line_info.line_start + i;
        let mut underline = String::new();
        if lineno == line_info.line_start && lineno == line_info.line_end {
            let count = line.chars().count().max(line_info.col_end - 1);
            for j in 0..count {
                let col = j + 1;
                let c = line.chars().nth(j).unwrap_or(' ');
                if line_info.col_start <= col && col < line_info.col_end {
                    let _ = cwrite!(
                        &mut underline,
                        "<y!>{}</>",
                        interpolate_char(c, underline_char)
                    );
                } else {
                    underline.push(interpolate_char(c, ' '));
                }
            }
        } else if lineno == line_info.line_start {
            let count = line.chars().count().max(line_info.col_end - 1);
            for j in 0..count {
                let col = j + 1;
                let c = line.chars().nth(j).unwrap_or(' ');
                if line_info.col_start <= col {
                    let _ = cwrite!(
                        &mut underline,
                        "<y!>{}</>",
                        interpolate_char(c, underline_char)
                    );
                } else {
                    underline.push(interpolate_char(c, ' '));
                }
            }
        } else if lineno == line_info.line_end {
            let count = line.chars().count().max(line_info.col_end - 1);
            for j in 0..count {
                let col = j + 1;
                let c = line.chars().nth(j).unwrap_or(' ');
                if col < line_info.col_end {
                    let _ = cwrite!(
                        &mut underline,
                        "<y!>{}</>",
                        interpolate_char(c, underline_char)
                    );
                } else {
                    underline.push(interpolate_char(c, ' '));
                }
            }
        } else {
            let count = line.chars().count().max(line_info.col_end - 1);
            for j in 0..count {
                let c = line.chars().nth(j).unwrap_or(' ');
                let _ = cwrite!(
                    &mut underline,
                    "<y!>{}</>",
                    interpolate_char(c, underline_char)
                );
            }
        }

        cprintln!("<m!,s>{:>line_column_width$}</> <b!>|</> {}", lineno, line);
        cprintln!(
            "<m!,s>{: >line_column_width$}</> <b!>|</> {}",
            "",
            underline
        );
    }
}

pub fn print_token(token: &Token) {
    println!("{}", token);
}

impl fmt::Display for LineInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}:{}]->[{}:{}]",
            self.line_start, self.col_start, self.line_end, self.col_end
        )
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // [{}:{}]->[{}:{}] ({}) {}
        write!(f, "{} ({:?}) {:?}", self.line_info, self.kind, self.text)
    }
}

pub fn print_scopes<'a>(scopes: &HashMap<String, Rc<RefCell<scope::Scope<'a>>>>) {
    for (name, scope) in scopes {
        print_scope(name, scope.borrow(), &mut Vec::new());
    }
}

fn print_scope<'a>(name: &str, scope: Ref<'_, scope::Scope<'a>>, is_last_vec: &mut Vec<bool>) {
    // TODO: show payload

    for (i, &is_last) in is_last_vec.iter().enumerate() {
        if i == is_last_vec.len() - 1 {
            if is_last {
                print!("└──");
            } else {
                print!("├──");
            }
        } else if is_last {
            print!("   ");
        } else {
            print!("│  ");
        }
    }
    print!("{}: ", name);
    match &scope.state {
        scope::State::NotVisited(_) => print!("not evaluated"),
        scope::State::VisitInProg => print!("evaluation in progress"),
        scope::State::Visited(ctx) => {
            print!("{}", ctx.to_string());
            if let Some(value) = &ctx.value {
                let repr = value.to_string();
                if !repr.is_empty() {
                    print!(" = {}", repr);
                }
            }
        }
    }
    println!();

    for (i, (name, child)) in scope.children.iter().enumerate() {
        is_last_vec.push(i + 1 >= scope.children.len());
        print_scope(name, child.borrow(), is_last_vec);
        is_last_vec.pop();
    }
}

pub fn print_ast(name: &str, ast: &impl PrintableNode) {
    let mut printer = AstPrinter::new();
    let node = ast.print_ast(name, &mut printer);
    print_tree_node(&node, &mut Vec::new());
}

fn print_tree_node(node: &TreeNode, is_last_vec: &mut Vec<bool>) {
    for (i, &is_last) in is_last_vec.iter().enumerate() {
        if i == is_last_vec.len() - 1 {
            if is_last {
                print!("└──");
            } else {
                print!("├──");
            }
        } else if is_last {
            print!("   ");
        } else {
            print!("│  ");
        }
    }
    println!("{}", node.value);

    for (i, child) in node.children.iter().enumerate() {
        is_last_vec.push(i + 1 >= node.children.len());
        print_tree_node(child, is_last_vec);
        is_last_vec.pop();
    }
}

pub struct TreeNode {
    value: String,
    children: Vec<TreeNode>,
}

impl Write for TreeNode {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.value.push_str(s);
        Ok(())
    }
}

pub struct AstPrinter {
    node_stack: Vec<TreeNode>,
}

impl Write for AstPrinter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        write!(self.node_stack.last_mut().unwrap(), "{}", s)
    }
}

pub trait PrintableNode {
    fn print_ast(&self, name: &str, printer: &mut AstPrinter) -> TreeNode;
}

impl PrintableNode for ast::Decl {
    fn print_ast(&self, name: &str, printer: &mut AstPrinter) -> TreeNode {
        printer.print_decl(name, self).unwrap().unwrap()
    }
}
impl PrintableNode for ast::Object {
    fn print_ast(&self, name: &str, printer: &mut AstPrinter) -> TreeNode {
        printer.print_object(name, self).unwrap().unwrap()
    }
}
impl PrintableNode for ast::Param {
    fn print_ast(&self, name: &str, printer: &mut AstPrinter) -> TreeNode {
        printer.print_param(name, self).unwrap().unwrap()
    }
}
impl PrintableNode for ast::Stmt {
    fn print_ast(&self, name: &str, printer: &mut AstPrinter) -> TreeNode {
        printer.print_stmt(name, self).unwrap().unwrap()
    }
}
impl PrintableNode for ast::Type {
    fn print_ast(&self, name: &str, printer: &mut AstPrinter) -> TreeNode {
        printer.print_type(name, self).unwrap().unwrap()
    }
}
impl PrintableNode for ast::Expr {
    fn print_ast(&self, name: &str, printer: &mut AstPrinter) -> TreeNode {
        printer.print_expr(name, self).unwrap().unwrap()
    }
}
impl PrintableNode for ast::Arg {
    fn print_ast(&self, name: &str, printer: &mut AstPrinter) -> TreeNode {
        printer.print_arg(name, self).unwrap().unwrap()
    }
}

fn remove_whitespace(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

macro_rules! define_printer {
    ($name:ident, $visitor:ident, $node:ident) => {
        pub fn $name(
            &mut self,
            name: &str,
            ast: &crate::ast::$node,
        ) -> Result<Option<TreeNode>, fmt::Error> {
            // Start a level
            let node = TreeNode {
                value: String::new(),
                children: Vec::new(),
            };
            // Write the meta information
            self.node_stack.push(node);
            write!(
                self,
                "{}: {} {}",
                name,
                ast.get_line_info(),
                remove_whitespace(stringify!(ast::$node))
            )?;
            self.$visitor(ast)?;
            // End the level
            let node = self.node_stack.pop().unwrap();
            if let Some(parent) = self.node_stack.last_mut() {
                parent.children.push(node);
                Ok(None)
            } else {
                Ok(Some(node))
            }
        }
    };
}

impl AstPrinter {
    fn new() -> Self {
        Self {
            node_stack: Vec::new(),
        }
    }

    fn visit_decl(&mut self, decl: &ast::Decl) -> fmt::Result {
        match decl {
            ast::Decl::Decl {
                name,
                taipe,
                eq_token,
                object,
            } => {
                write!(self, "::Decl")?;
                self.print_tok("name", name)?;
                if let Some(taipe) = taipe {
                    self.print_type("type", taipe)?;
                }
                if let Some(eq_token) = eq_token {
                    self.print_tok("eq_token", eq_token)?;
                }
                if let Some(object) = object {
                    self.print_object("object", object)?;
                }
            }
            ast::Decl::Using {
                line_info: _,
                items,
            } => {
                write!(self, "::Using")?;
                self.print_toks("items", items)?;
            }
        }
        Ok(())
    }

    fn visit_object(&mut self, object: &ast::Object) -> fmt::Result {
        match object {
            ast::Object::ExternModule {
                line_info: _,
                value,
            } => {
                write!(self, "::ExternModule")?;
                self.print_tok("value", value)?;
            }
            ast::Object::Module {
                line_info: _,
                decls,
            } => {
                write!(self, "::Module")?;
                self.print_list("decls", decls, Self::print_decl)?;
            }
            ast::Object::Fun {
                line_info: _,
                params,
                ret,
                body,
            } => {
                write!(self, "::Fun")?;
                self.print_list("params", params, Self::print_param)?;
                if let Some(ret) = ret {
                    self.print_type("ret", ret)?;
                }
                if let Some(body) = body {
                    self.print_stmt("body", body)?;
                }
            }
            ast::Object::Compound {
                line_info: _,
                field,
            } => {
                write!(self, "::Compound")?;
                self.print_field("field", field)?;
            }
            ast::Object::Typedef(taipe) => {
                write!(self, "::Typedef")?;
                self.print_type("type", taipe)?;
            }
            ast::Object::Expr(expr) => {
                write!(self, "::Expr")?;
                self.print_expr("expr", expr)?;
            }
        }
        Ok(())
    }

    fn visit_field(&mut self, field: &ast::Field) -> fmt::Result {
        match field {
            ast::Field::Compound { token, fields } => {
                write!(self, "::Compound")?;
                self.print_tok("token", token)?;
                self.print_list("fields", fields, Self::print_field)?;
            }
            ast::Field::Decl {
                name,
                taipe,
                eq_token,
                expr,
            } => {
                write!(self, "::Decl")?;
                self.print_tok("name", name)?;
                self.print_type("type", taipe)?;
                if let Some(eq_token) = eq_token {
                    self.print_tok("eq_token", eq_token)?;
                }
                if let Some(expr) = expr {
                    self.print_expr("expr", expr)?;
                }
            }
        }
        Ok(())
    }

    fn visit_param(&mut self, param: &ast::Param) -> fmt::Result {
        self.print_tok("name", &param.name)?;
        self.print_type("type", &param.taipe)?;
        Ok(())
    }

    fn visit_stmt(&mut self, stmt: &ast::Stmt) -> fmt::Result {
        match stmt {
            ast::Stmt::If {
                line_info: _,
                expr,
                then_body,
                else_body,
            } => {
                write!(self, "::If")?;
                self.print_expr("expr", expr)?;
                self.print_stmt("then_body", then_body)?;
                if let Some(stmt) = else_body {
                    self.print_stmt("else_body", stmt)?;
                }
            }
            ast::Stmt::While {
                line_info: _,
                label,
                expr,
                then_body,
                else_body,
            } => {
                write!(self, "::While")?;
                if let Some(tok) = label {
                    self.print_tok("label", tok)?;
                }
                self.print_expr("expr", expr)?;
                self.print_stmt("then_body", then_body)?;
                if let Some(stmt) = else_body {
                    self.print_stmt("else_body", stmt)?;
                }
            }
            ast::Stmt::Block {
                line_info: _,
                label,
                stmts,
            } => {
                write!(self, "::Block")?;
                if let Some(tok) = label {
                    self.print_tok("label", tok)?;
                }
                self.print_list("stmts", stmts, Self::print_stmt)?;
            }
            ast::Stmt::Yield { token, label, expr } => {
                write!(self, "::Yield")?;
                self.print_tok("token", token)?;
                if let Some(tok) = label {
                    self.print_tok("label", tok)?;
                }
                if let Some(expr) = expr {
                    self.print_expr("expr", expr)?;
                }
            }
            ast::Stmt::Continue { token, label } => {
                write!(self, "::Continue")?;
                self.print_tok("token", token)?;
                if let Some(tok) = label {
                    self.print_tok("label", tok)?;
                }
            }
            ast::Stmt::Break { token, label, expr } => {
                write!(self, "::Break")?;
                self.print_tok("token", token)?;
                if let Some(tok) = label {
                    self.print_tok("label", tok)?;
                }
                if let Some(expr) = expr {
                    self.print_expr("expr", expr)?;
                }
            }
            ast::Stmt::Return { token, expr } => {
                write!(self, "::Return")?;
                self.print_tok("token", token)?;
                if let Some(expr) = expr {
                    self.print_expr("expr", expr)?;
                }
            }
            ast::Stmt::Decl(decl) => {
                write!(self, "::Decl")?;
                self.print_decl("decl", decl)?;
            }
            ast::Stmt::Expr(expr) => {
                write!(self, "::Expr")?;
                self.print_expr("expr", expr)?;
            }
            ast::Stmt::Nop(token) => {
                write!(self, "::Nop")?;
                self.print_tok("token", token)?;
            }
        }
        Ok(())
    }

    fn visit_type(&mut self, taipe: &ast::Type) -> fmt::Result {
        match taipe {
            ast::Type::Path { items } => {
                write!(self, "::Path")?;
                self.print_toks("items", items)?;
            }
            ast::Type::Function {
                line_info: _,
                params,
                ret,
            } => {
                write!(self, "::Function")?;
                self.print_list("params", params, Self::print_type)?;
                self.print_type("ret", ret)?;
            }
            ast::Type::Const { token, taipe } => {
                write!(self, "::Const")?;
                self.print_tok("token", token)?;
                self.print_type("type", taipe)?;
            }
            ast::Type::Pointer { token, taipe } => {
                write!(self, "::Pointer")?;
                self.print_tok("token", token)?;
                self.print_type("type", taipe)?;
            }
            ast::Type::Array {
                line_info: _,
                taipe,
                expr,
            } => {
                write!(self, "::Array")?;
                self.print_type("type", taipe)?;
                if let Some(expr) = expr {
                    self.print_expr("expr", expr)?;
                }
            }
            ast::Type::Fat {
                line_info: _,
                taipe,
            } => {
                write!(self, "::Fat")?;
                self.print_type("type", taipe)?;
            }
            ast::Type::Paren {
                line_info: _,
                taipe,
            } => {
                write!(self, "::Paren")?;
                self.print_type("type", taipe)?;
            }
            ast::Type::Tuple {
                line_info: _,
                types,
            } => {
                write!(self, "::Tuple")?;
                self.print_list("types", types, Self::print_type)?;
            }
            ast::Type::Literal(token) => {
                write!(self, "::Literal")?;
                self.print_tok("token", token)?;
            }
        }
        Ok(())
    }

    fn visit_expr(&mut self, expr: &ast::Expr) -> fmt::Result {
        match expr {
            ast::Expr::Assign { lhs, op, rhs } => {
                write!(self, "::Assign")?;
                self.print_list("lhs", lhs, Self::print_expr)?;
                self.print_tok("op", op)?;
                self.print_list("rhs", rhs, Self::print_expr)?;
            }
            ast::Expr::Binary2 {
                left,
                op1,
                op2,
                right,
            } => {
                write!(self, "::Binary2")?;
                self.print_expr("left", left)?;
                self.print_tok("op1", op1)?;
                self.print_tok("op2", op2)?;
                self.print_expr("right", right)?;
            }
            ast::Expr::Binary { left, op, right } => {
                write!(self, "::Binary")?;
                self.print_expr("left", left)?;
                self.print_tok("op", op)?;
                self.print_expr("right", right)?;
            }
            ast::Expr::Cast { expr, taipe } => {
                write!(self, "::Cast")?;
                self.print_expr("expr", expr)?;
                self.print_type("type", taipe)?;
            }
            ast::Expr::Unary { op, expr } => {
                write!(self, "::Unary")?;
                self.print_tok("op", op)?;
                self.print_expr("expr", expr)?;
            }
            ast::Expr::Member { expr, name } => {
                write!(self, "::Member")?;
                self.print_expr("expr", expr)?;
                self.print_tok("name", name)?;
            }
            ast::Expr::Call {
                line_info: _,
                expr,
                args,
            } => {
                write!(self, "::Call")?;
                self.print_expr("expr", expr)?;
                self.print_list("args", args, Self::print_arg)?;
            }
            ast::Expr::Index {
                line_info: _,
                expr,
                items,
            } => {
                write!(self, "::Index")?;
                self.print_expr("expr", expr)?;
                self.print_list("items", items, Self::print_expr)?;
            }
            ast::Expr::Literal(token) => {
                write!(self, "::Literal")?;
                self.print_tok("token", token)?;
            }
            ast::Expr::Paren { line_info: _, expr } => {
                write!(self, "::Paren")?;
                self.print_expr("expr", expr)?;
            }
            ast::Expr::Tuple {
                line_info: _,
                exprs,
            } => {
                write!(self, "::Tuple")?;
                self.print_list("exprs", exprs, Self::print_expr)?;
            }
            ast::Expr::ArrayLit {
                line_info: _,
                items,
            } => {
                write!(self, "::ArrayLit")?;
                self.print_list("items", items, Self::print_expr)?;
            }
        }
        Ok(())
    }

    fn visit_arg(&mut self, arg: &ast::Arg) -> fmt::Result {
        if let Some(name) = &arg.name {
            self.print_tok("name", name)?;
        }
        self.print_expr("expr", &arg.expr)?;
        Ok(())
    }

    define_printer!(print_decl, visit_decl, Decl);
    define_printer!(print_object, visit_object, Object);
    define_printer!(print_field, visit_field, Field);
    define_printer!(print_param, visit_param, Param);
    define_printer!(print_stmt, visit_stmt, Stmt);
    define_printer!(print_type, visit_type, Type);
    define_printer!(print_expr, visit_expr, Expr);
    define_printer!(print_arg, visit_arg, Arg);

    fn print_tok(&mut self, name: &str, tok: &Token) -> fmt::Result {
        self.start_level();
        write!(self, "{}: {}", name, tok)?;
        self.end_level();
        Ok(())
    }

    fn print_toks(&mut self, name: &str, toks: &[Token]) -> fmt::Result {
        self.start_level();
        write!(self, "{}: ", name)?;
        if toks.is_empty() {
            write!(self, "[]")?;
        } else {
            for (i, item) in toks.iter().enumerate() {
                self.print_tok(&format!("{}", i), item)?;
            }
        }
        self.end_level();
        Ok(())
    }

    fn print_list<T, F>(&mut self, name: &str, list: &[T], mut print: F) -> fmt::Result
    where
        F: FnMut(&mut AstPrinter, &str, &T) -> Result<Option<TreeNode>, fmt::Error>,
    {
        self.start_level();
        write!(self, "{}: ", name)?;
        if list.is_empty() {
            write!(self, "[]")?;
        } else {
            for (i, item) in list.iter().enumerate() {
                print(self, &format!("{}", i), item)?;
            }
        }
        self.end_level();
        Ok(())
    }

    fn start_level(&mut self) {
        let node = TreeNode {
            value: String::new(),
            children: Vec::new(),
        };
        self.node_stack.push(node);
    }

    fn end_level(&mut self) {
        let node = self.node_stack.pop().unwrap();
        if let Some(parent) = self.node_stack.last_mut() {
            parent.children.push(node);
        }
    }
}
