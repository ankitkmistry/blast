#[derive(Clone, Debug)]
pub enum Value {
    Bool(bool),
    Char(char),
    Array(Vec<Value>),
}

impl Value {
    pub fn from_str(text: &str) -> Self {
        Self::Array(text.chars().map(|c| Value::Char(c)).collect::<Vec<_>>())
    }
}
