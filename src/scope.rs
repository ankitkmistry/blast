use crate::{
    ast,
    common::{HasLineInfo, Layout, LayoutResult, LineInfo},
    context::Context,
    lexer::Token,
};
use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap},
    rc::{Rc, Weak},
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolPath {
    elms: Vec<String>,
}

impl From<&str> for SymbolPath {
    fn from(value: &str) -> Self {
        SymbolPath {
            elms: value
                .to_string()
                .split('.')
                .map(|item| item.to_owned())
                .collect::<Vec<String>>(),
        }
    }
}

impl ToString for SymbolPath {
    fn to_string(&self) -> String {
        self.elms.join(".")
    }
}

impl SymbolPath {
    pub fn new() -> Self {
        Self { elms: Vec::new() }
    }

    pub fn push_name(&mut self, name: &str) {
        self.elms.push(name.to_owned());
    }

    // pub fn is_empty(&self) -> bool {
    //     self.elms.is_empty()
    // }
    //
    // pub fn get_elements(&self) -> &[String] {
    //     &self.elms
    // }
}

#[derive(Clone)]
pub enum ScopeNode<'a> {
    Decl(&'a ast::Decl),
    Field(&'a ast::Field),
    Object(&'a ast::Object),
}

impl<'a> HasLineInfo for ScopeNode<'a> {
    fn get_line_info(&self) -> LineInfo {
        match self {
            ScopeNode::Decl(decl) => decl.get_line_info(),
            ScopeNode::Field(field) => field.get_line_info(),
            ScopeNode::Object(object) => object.get_line_info(),
        }
    }
}

#[derive(Clone)]
pub enum State<'a> {
    /// Scope is not visited yet
    NotVisited(ScopeNode<'a>),
    /// Visitation is in progress
    VisitInProg,
    /// Scope has been visited
    Visited(Context<'a>),
}

#[derive(Clone)]
pub enum Payload<'a> {
    Compound(Compound<'a>),
    None,
}

#[derive(Clone)]
pub enum Field<'a> {
    Struct(Vec<Field<'a>>),
    Union(Vec<Field<'a>>),
    Field { name: String, ctx: Context<'a> },
}

impl<'a> Field<'a> {
    fn get_layout(
        &self,
        offset_start: usize,
        offset_map: &mut HashMap<String, FieldData>,
    ) -> (Option<String>, LayoutResult) {
        match self {
            Field::Struct(fields) => {
                // Alignment of a struct is the alignment of the most aligned field
                let mut alignment = 1usize;
                // Calculate
                let mut offset = 0usize;
                for field in fields.iter() {
                    match field.get_layout(offset, offset_map) {
                        (name, LayoutResult::NoLayout) => return (name, LayoutResult::NoLayout),
                        (
                            field_name,
                            LayoutResult::Evaled(Layout {
                                size: field_size,
                                alignment: field_alignment,
                            }),
                        ) => {
                            if let Some(field_name) = field_name {
                                // Set the offset of field
                                offset_map.insert(
                                    field_name.clone(),
                                    FieldData {
                                        offset,
                                        size: field_size,
                                        alignment: field_alignment,
                                    },
                                );
                            }
                            // Advance the offset
                            offset += field_size;
                            // Add the padding
                            offset += Self::eval_padding(offset, field_alignment);
                            alignment = alignment.max(field_alignment);
                        }
                    }
                }
                // Extra padding at the end of the struct
                offset += Self::eval_padding(offset, alignment);
                let size = offset - offset_start;
                (
                    None,
                    LayoutResult::Evaled(Layout {
                        // TODO: think about empty structs
                        // Reference: https://doc.rust-lang.org/nightly/nomicon/exotic-sizes.html#zero-sized-types-zsts
                        size: if size == 0 { 1 } else { size },
                        alignment,
                    }),
                )
            }
            Field::Union(fields) => {
                // Alignment of a union is the alignment of the most aligned field
                let mut alignment = 0usize;
                // Size of a union is the size of the most aligned field
                let mut size = 0usize;
                // Calculate
                for field in fields.iter() {
                    match field.get_layout(offset_start, offset_map) {
                        (name, LayoutResult::NoLayout) => return (name, LayoutResult::NoLayout),
                        (
                            name,
                            LayoutResult::Evaled(Layout {
                                size: field_size,
                                alignment: field_alignment,
                            }),
                        ) => {
                            if let Some(name) = name {
                                // Set the offset of field
                                offset_map.insert(
                                    name.clone(),
                                    FieldData {
                                        offset: offset_start,
                                        size: field_size,
                                        alignment: field_alignment,
                                    },
                                );
                            }
                            alignment = alignment.max(field_alignment);
                            size = size.max(field_size);
                        }
                    }
                }
                (None, LayoutResult::Evaled(Layout { size, alignment }))
            }
            Field::Field { name, ctx } => (Some(name.clone()), ctx.taipe.get_layout()),
        }
    }

    fn eval_padding(cur_offset: usize, alignment: usize) -> usize {
        // Calculate the misalignment
        let misalignment = cur_offset % alignment;
        // Add the padding
        let padding = if misalignment > 0 {
            alignment - misalignment
        } else {
            0
        };
        padding
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FieldData {
    pub offset: usize,
    pub size: usize,
    pub alignment: usize,
}

#[derive(Clone)]
pub struct Compound<'a> {
    field: Field<'a>,
    layout: Option<LayoutResult>,
    pub offsets: HashMap<String, FieldData>,
}

impl<'a> Compound<'a> {
    pub fn new(field: Field<'a>) -> Self {
        Compound {
            field,
            layout: None,
            offsets: HashMap::new(),
        }
    }

    fn get_layout(&mut self) -> LayoutResult {
        if let Some(layout) = self.layout {
            match layout {
                LayoutResult::NoLayout => LayoutResult::NoLayout,
                LayoutResult::Evaled(Layout {
                    size,
                    alignment: align,
                }) => LayoutResult::Evaled(Layout {
                    size,
                    alignment: align,
                }),
            }
        } else {
            self.field.get_layout(0, &mut self.offsets).1
        }
    }
}

pub type Map<K, V> = BTreeMap<K, V>;

#[derive(Clone)]
pub struct Scope<'a> {
    /// Weak reference to the parent scope
    pub parent: Weak<RefCell<Scope<'a>>>,
    /// The file path to which this scope belongs to.
    /// If this is None, then the file path of this scope
    /// is the file path of the parent scope.
    pub file_path: Option<String>,
    /// The symbol path of the scope
    pub sym_path: SymbolPath,
    /// The name of the scope in the form of a token. (to improve error output)
    pub name: String,
    /// The line info of the scope.
    pub line_info: LineInfo,
    /// The state for the context evaluation of this scope
    pub state: State<'a>,
    /// The payload data for this scope.
    /// For example, a struct scope can have a payload related to field layout, padding, etc.
    pub payload: Payload<'a>,
    /// The children of this scope
    pub children: Map<String, Rc<RefCell<Scope<'a>>>>,
}

impl<'a> Scope<'a> {
    pub fn new_root(file_path: &str, node: &'a ast::Object) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            parent: Weak::new(),
            file_path: Some(file_path.to_owned()),
            sym_path: SymbolPath::new(),
            name: "".to_string(),
            line_info: node.get_line_info(),
            state: State::NotVisited(ScopeNode::Object(node)),
            payload: Payload::None,
            children: Map::new(),
        }))
    }

    pub fn add_child(
        parent: &Rc<RefCell<Scope<'a>>>,
        name: &str,
        state: State<'a>,
        line_info: &impl HasLineInfo,
    ) -> Rc<RefCell<Scope<'a>>> {
        // Create the symbol path
        let mut sym_path = parent.borrow().sym_path.clone();
        sym_path.push_name(name);
        // Create the child scope
        let child = Rc::new(RefCell::new(Self {
            parent: Rc::downgrade(parent),
            file_path: None,
            sym_path,
            name: name.to_string(),
            line_info: line_info.get_line_info(),
            state,
            payload: Payload::None,
            children: Map::new(),
        }));
        // Clone it so we can return later
        let result = Rc::clone(&child);
        // Finishing up
        let ret = parent.borrow_mut().children.insert(name.to_owned(), child);
        if name != "_" {
            assert!(
                ret.is_none(),
                "redeclaration should be prohibited from analyzer"
            );
        }
        result
    }

    pub fn get_layout(&mut self) -> LayoutResult {
        match &mut self.payload {
            Payload::Compound(compound) => compound.get_layout(),
            Payload::None => unreachable!("probably some analyzer bug"),
        }
    }
}

pub trait HasSrcInfo: HasLineInfo {
    fn get_src_path(&self) -> String;
}

impl<'a> HasLineInfo for Scope<'a> {
    fn get_line_info(&self) -> LineInfo {
        self.line_info
    }
}

impl<'a> HasSrcInfo for Scope<'a> {
    fn get_src_path(&self) -> String {
        if let Some(path) = &self.file_path {
            path.clone()
        } else if let Some(parent) = self.parent.upgrade() {
            parent.borrow().get_src_path()
        } else {
            panic!("all scopes must designated to some source file");
        }
    }
}
