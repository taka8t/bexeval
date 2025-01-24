use std::collections::HashMap;
use crate::parser::{Parser, ParserError};
use crate::value_type::Integer;

pub struct Context<T: Integer = i32> {
    parser: Parser<T>,
    var_info: HashMap<String, T>
}

/// By default, `i32` is used as the value type
impl Default for Context {
    fn default() -> Self {
        Context::<i32>::new()
    }
}

impl<T: Integer> Context<T> {
    pub fn new() -> Self {
        Self {
            parser: Parser::<T>::new(),
            var_info: HashMap::new()
        }
    }

    pub fn assign(&mut self, var: &str, val: T) {
        self.var_info.insert(var.to_string(), val);
    }

    pub fn assign_stmt(&mut self, stmt: &str) -> Result<(), ParserError> {
        let (var, val) = self.parser.parse_statement(stmt, &self.var_info)?;
        self.assign(&var, val);
        Ok(())
    }

    pub fn eval(&self, src: &str) -> Result<T, ParserError> {
        self.parser.eval_context(src, &self.var_info)
    }

    pub fn clear(&mut self) {
        self.var_info.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context() {
        let mut ctx = Context::<i32>::new();
        ctx.assign("x", 1);
        assert_eq!(ctx.eval("x + 3").unwrap(), 4);
        ctx.assign_stmt("y = x + 5").unwrap();
        assert_eq!(ctx.eval("y + x * 2").unwrap(), 8);
    }
}