use std::collections::HashMap;
use crate::lexer::{Lexer, LexToken};
use crate::value_type::Integer;

#[derive(Clone, Debug, PartialEq)]
pub struct ParserError {
    msg: String,
}

impl ParserError {
    pub fn new(msg: &str) -> ParserError {
        ParserError {
            msg: msg.to_string(),
        }
    }
    pub fn msg(&self) -> &str {
        self.msg.as_str()
    }
}
impl std::fmt::Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.msg())
    }
}
impl std::error::Error for ParserError {}

pub struct Parser<T: Integer = i32> {
    _phantom: std::marker::PhantomData<T>
}

/// By default, `i32` is used as the value type
impl Default for Parser {
    fn default() -> Self {
        Parser::<i32>::new()
    }
}

impl<T: Integer> Parser<T> {

    pub fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }

    /// Available when expression string does not contain variables
    pub fn eval(&self, src: &str) -> Result<T, ParserError>{
        self.eval_inner(src, &HashMap::new())
    }

    /// Used when the expression string contains variables
    /// The ctx argument stores information about the variable in array of tuples(&str, T).
    pub fn eval_context(&self, src: &str, ctx: &[(&str, T)]) -> Result<T, ParserError> {
        self.eval_inner(src, &HashMap::from_iter(ctx.iter().map(|(s, i)| (s.to_string(), *i))))
    }

    /// Internal method to convert the expression string to integer values
    pub(crate) fn eval_inner(&self, src: &str, ctx: &HashMap<String, T>) -> Result<T, ParserError> {
        let mut stack = Vec::new();
        for token in self.to_rpn(src)?.into_iter() {
            match token {
                Token::Value(val) => {stack.push(val);},
                Token::Variable(var) => {
                    if let Some(&val) = ctx.get(&var) {
                        stack.push(val);
                    }
                    else {
                        return Err(ParserError::new(format!("Undefined Variable: {}", var).as_str()));
                    }
                },
                Token::Unary(op) => {
                    if let Some(val) = stack.pop() {
                        stack.push(op.eval(val));
                    }
                    else {
                        return Err(ParserError::new("The expression is incorrect"));
                    }
                },
                Token::Binary(op) => {
                    if let (Some(val2), Some(val1)) = (stack.pop(), stack.pop()) {
                        stack.push(op.eval(val1, val2));
                    }
                    else {
                        return Err(ParserError::new("The expression is incorrect"));
                    }
                }
                Token::Function(func) => {
                    let ret = match func.n_arg() {
                        1 => {
                            if let Some(val) = stack.pop() {
                                func.eval1(val)
                            }
                            else {
                                return Err(ParserError::new("The expression is incorrect"));
                            }
                        },
                        2 => {
                            if let (Some(val2), Some(val1)) = (stack.pop(), stack.pop()) {
                                func.eval2(val1, val2)
                            }
                            else {
                                return Err(ParserError::new("The expression is incorrect"));
                            }
                        }
                        _ => unreachable!()
                    };
                    stack.push(ret);
                },
                _ => {
                    return Err(ParserError::new("The expression is incorrect"));
                }
            }
        }
        if stack.len() == 1 {
            Ok(stack.pop().unwrap())
        }
        else {
            Err(ParserError::new("Failed to evaluate"))
        }
    }
    
    /// From a string statement of the form “var = expr”, evaluate `expr` and assign it to `var`.
    /// Example of `src` argument : 
    /// "x = 2 + 6"
    /// "y = x * 2"
    /// ParserError if `expr` contains a variable with no information
    pub(crate) fn parse_statement(&self, stmt: &str, ctx: &HashMap<String, T>) -> Result<(String, T), ParserError> {
        let mut split = stmt.splitn(2, '=');
        if let (Some(var_str), Some(expr)) = (split.next(), split.next()) {
            let mut var_iter = Lexer::new(var_str)?.into_iter();
            
            let var = if let (Some(LexToken::Variable(s)), None) = (var_iter.next(), var_iter.next()) {
                s
            }
            else {
                return Err(ParserError::new("The syntax on the left side is incorrect"));
            };
            
            let val = self.eval_inner(expr, ctx)?;

            Ok((var, val))
        }
        else {
            Err(ParserError::new("The format of the statement must be \"var = expression\""))
        }
    }

    /// Convert LexToken to Token and then to Reverse Polish Notation
    /// Overflow due to the type of the number is treated as a ParserError
    /// If the number type is u8, strings parsed as greater than 256 will result in a ParserError
    /// (Based on the rules of the `from_str` function)
    fn to_rpn(&self, src: &str) -> Result<Vec<Token<T>>, ParserError> {
        // from lextokens to tokens
        let mut tokens = Vec::new();
        let mut paren_count = 0;
        let mut lt_iter = Lexer::new(src)?.into_iter().peekable();
        while let Some(lt) = lt_iter.next() {
            match lt {
                LexToken::LeftParen => {
                    tokens.push(Token::Symbol(Symbol::LeftParen));
                    paren_count += 1;
                },
                LexToken::RightParen => {
                    tokens.push(Token::Symbol(Symbol::RightParen));
                    paren_count -= 1;
                },
                LexToken::Comma => {
                    tokens.push(Token::Symbol(Symbol::Comma));
                },
                LexToken::Plus => {
                    tokens.push(Token::Binary(BinOp::Add));
                },
                LexToken::Minus => {
                    match tokens.last() {
                        Some(Token::Symbol(Symbol::RightParen)) | Some(Token::Value(_)) | Some(Token::Variable(_)) => {
                            tokens.push(Token::Binary(BinOp::Sub));
                        },
                        _ => {tokens.push(Token::Unary(UnaryOp::Neg));}   
                    }
                },
                LexToken::Star => {
                    tokens.push(Token::Binary(BinOp::Mul));
                },
                LexToken::Slash => {
                    tokens.push(Token::Binary(BinOp::Div));
                },
                LexToken::Percent => {
                    tokens.push(Token::Binary(BinOp::Mod));
                },
                LexToken::And => {
                    tokens.push(Token::Binary(BinOp::And));
                },
                LexToken::Or => {
                    tokens.push(Token::Binary(BinOp::Or));
                },
                LexToken::Xor => {
                    tokens.push(Token::Binary(BinOp::Xor));
                },
                LexToken::Not => {
                    tokens.push(Token::Unary(UnaryOp::Not));
                },
                LexToken::Less => {
                    tokens.push(Token::Binary(BinOp::Less));
                },
                LexToken::LessEqual => {
                    tokens.push(Token::Binary(BinOp::LessEqual));
                },
                LexToken::Greater => {
                    tokens.push(Token::Binary(BinOp::Greater));
                },
                LexToken::GreaterEqual => {
                    tokens.push(Token::Binary(BinOp::GreaterEqual));
                },
                LexToken::LeftShift => {
                    tokens.push(Token::Binary(BinOp::Shl));
                },
                LexToken::RightShift => {
                    tokens.push(Token::Binary(BinOp::Shr));
                },
                LexToken::Equal => {
                    tokens.push(Token::Equal);
                },
                LexToken::EqualEqual => {
                    tokens.push(Token::Binary(BinOp::EqualEqual));
                },
                LexToken::NotEqual => {
                    tokens.push(Token::Binary(BinOp::NotEqual));
                },
                LexToken::Variable(s) => {
                    if let Some(LexToken::LeftParen) = lt_iter.peek() {
                        tokens.push(Token::Function(s.parse::<Function>()?));
                    }
                    else {
                        tokens.push(Token::Variable(s));
                    }
                }
                LexToken::Number(s) => {
                    let n = match s.replace("_", "").parse::<T>() {
                        Ok(n) => {n},
                        Err(_) => {
                            return Err(ParserError::new(format!("Cannot parse string \"{}\" to {}", s, std::any::type_name::<T>()).as_str()));
                        }
                    };
                    tokens.push(Token::Value(n));
                }
            }
            if paren_count < 0 {
                return Err(ParserError::new("The number of parentheses does not match"));
            }
        }
        
        if paren_count != 0 {
            return Err(ParserError::new("The number of parentheses does not match"));
        }
        

        // From Infix notation to Reverse Polish Notation using Shunting yard Algorithm
        let mut rpn_stack: Vec<Token<T>> = Vec::new();
        let mut op_stack: Vec<Token<T>> = Vec::new();

        for token in tokens.into_iter() {
            match token {
                Token::Variable(_) | Token::Value(_) => {
                    rpn_stack.push(token);
                }
                _ => {
                    let (lp, _) = token.precedence();
                    while let Some(top_token) = op_stack.last() {
                        let (_, rp) = top_token.precedence();
                        if lp > rp {
                            break;
                        }
                        rpn_stack.push(op_stack.pop().unwrap());
                    }

                    if matches!(token, Token::Symbol(Symbol::RightParen)) {
                        match op_stack.last() {
                            Some(Token::Symbol(Symbol::LeftParen)) => {
                                op_stack.pop();
                                if let Some(Token::Function(_)) = op_stack.last() {
                                    rpn_stack.push(op_stack.pop().unwrap());
                                }
                                continue;
                            },
                            _ => {
                                return Err(ParserError::new("Unexpected parenthesis"));
                            }
                        }
                    }

                    if !matches!(token, Token::Symbol(Symbol::Comma)) {
                        op_stack.push(token);
                    }
                }
            }
        }

        while let Some(top_token) = op_stack.pop() {
            if matches!(top_token, Token::Symbol(Symbol::RightParen)) || matches!(top_token, Token::Symbol(Symbol::LeftParen)) {
                return Err(ParserError::new("Unexpected parenthesis"));
            }
            rpn_stack.push(top_token);
        }

        Ok(rpn_stack)
    }
    
}

#[derive(Debug)]
pub enum Token<T: Integer> {
    Equal,
    Symbol(Symbol),
    Unary(UnaryOp),
    Binary(BinOp),
    Value(T),
    Variable(String),
    Function(Function),
}

#[derive(Debug)]
pub enum Symbol {
    LeftParen,
    RightParen,
    Comma,
}

#[derive(Debug)]
pub enum UnaryOp {
    Neg,
    Not,
}

impl UnaryOp {
    fn eval<T: Integer>(&self, a: T) -> T {
        match self {
            Self::Neg => a.wrapping_neg(),
            Self::Not => !a,
        }
    }
}

#[derive(Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    EqualEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    NotEqual
}

impl BinOp {
    fn eval<T: Integer>(&self, a: T, b: T) -> T {
        match self {
            Self::Add => a.wrapping_add(&b),
            Self::Sub => a.wrapping_sub(&b),
            Self::Mul => a.wrapping_mul(&b),
            Self::Div => a / b,
            Self::Mod => a % b,
            Self::And => a & b,
            Self::Or => a | b,
            Self::Xor => a ^ b,
            Self::Shl => a.wrapping_shl(b.as_()),
            Self::Shr => a.wrapping_shr(b.as_()),
            Self::EqualEqual => T::from(a == b),
            Self::Less => T::from(a < b),
            Self::LessEqual => T::from(a <= b),
            Self::Greater => T::from(a > b),
            Self::GreaterEqual => T::from(a >= b),
            Self::NotEqual => T::from(a != b),
        }
    }
}

#[derive(Debug)]
pub enum Function {
    Pow,
    Max,
    Min,
    Abs,
    AbsDiff,
    CountOnes,
    CountZeros,
    LeadingZeros,
    TrailingZeros,
    RotateLeft,
    RotateRight
}

impl Function {
    fn n_arg(&self) -> u8 {
        match self {
            Self::Pow | Self::Max | Self::Min
            | Self::AbsDiff 
            | Self::RotateLeft | Self::RotateRight => {2},
            _ => {1}
        }
    }

    fn eval1<T: Integer>(&self, x1: T) -> T {
        match self {
            Self::CountOnes => x1.count_ones(),
            Self::CountZeros => x1.count_zeros(),
            Self::LeadingZeros => x1.leading_zeros(),
            Self::TrailingZeros => x1.trailing_zeros(),
            Self::Abs => x1.abs(),
            _ => unreachable!("The number of arguments should be 1")
        }
    }

    fn eval2<T: Integer>(&self, x1: T, x2: T) -> T {
        match self {
            Self::Pow => x1.wrapping_pow(x2.as_()),
            Self::Max => x1.max(x2),
            Self::Min => x1.min(x2),
            Self::AbsDiff => x1.abs_diff(x2),
            Self::RotateLeft => x1.rotate_left(x2.as_()),
            Self::RotateRight => x1.rotate_right(x2.as_()),
            _ => unreachable!("The number of arguments should be 2")
        }
    }
}

impl std::str::FromStr for Function {
    type Err = ParserError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "pow" => Ok(Self::Pow),
            "max" => Ok(Self::Max),
            "min" => Ok(Self::Min),
            "abs" => Ok(Self::Abs),
            "abs_diff" => Ok(Self::AbsDiff),
            "count_ones" => Ok(Self::CountOnes),
            "count_zeros" => Ok(Self::CountZeros),
            "leading_zeros" => Ok(Self::LeadingZeros),
            "trailing_zeros" => Ok(Self::TrailingZeros),
            "rotate_left" => Ok(Self::RotateLeft),
            "rotate_right" => Ok(Self::RotateRight),
            _ => Err(ParserError::new(format!("Cannot use function: {}", s).as_str()))
        }
    }
}

impl<T: Integer> Token<T> {
    fn precedence(&self) -> (u8, u8) {
        match self {
            Self::Binary(BinOp::Add) | Self::Binary(BinOp::Sub) => (50, 51),
            Self::Binary(BinOp::Mul) | Self::Binary(BinOp::Div) | Self::Binary(BinOp::Mod) => (55, 56),
            Self::Binary(BinOp::Shl) | Self::Binary(BinOp::Shr) => (48, 49),
            Self::Binary(BinOp::Less) | Self::Binary(BinOp::LessEqual)
            | Self::Binary(BinOp::Greater) | Self::Binary(BinOp::GreaterEqual) => (44, 45),
            Self::Binary(BinOp::EqualEqual) | Self::Binary(BinOp::NotEqual) => (42, 43),
            Self::Binary(BinOp::And) => (39, 40),
            Self::Binary(BinOp::Xor) => (37, 38),
            Self::Binary(BinOp::Or) => (35, 36),
            Self::Unary(UnaryOp::Neg) | Self::Unary(UnaryOp::Not) => (99, 80),
            Self::Function(_) => (97, 3),
            Self::Symbol(Symbol::LeftParen) => (99, 3),
            Self::Symbol(Symbol::RightParen) => (4, 100),
            Self::Equal => (2, 1),
            Self::Symbol(Symbol::Comma) => (5, 6),
            _ => (100, 100)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_expr() {
        assert_eq!(
            Parser::default().eval("1 + 4").unwrap(),
            1 + 4
        );
        assert_eq!(
            Parser::<i32>::new().eval("5 * 7 * 36 % 13 / 3").unwrap(),
            5 * 7 * 36 % 13 / 3
        );
        assert_eq!(
            Parser::<i32>::new().eval("1 + 2 * 3 - 8 ^ 5 & 29 | 15 / 2 % 9 & 25").unwrap(),
            1 + 2 * 3 - 8 ^ 5 & 29 | 15 / 2 % 9 & 25
        );
        assert_eq!(
            Parser::<i32>::new().eval("1+2*3-8^5&29|15/2%9&25").unwrap(),
            1 + 2 * 3 - 8 ^ 5 & 29 | 15 / 2 % 9 & 25
        );
        assert_eq!(
            Parser::<i32>::new().eval("(1 == 1) + 5 * (3 <= 2)").unwrap(),
            1
        );
        assert_eq!(
            Parser::<i32>::new().eval("max(1, 2) + min(3, 5) + pow(2, 3)").unwrap(),
            1.max(2) + 3.min(5) + 2i32.pow(3)
        );

        assert_eq!(
            Parser::<u8>::new().eval("123 * 146 | 126").unwrap(),
            123u8.wrapping_mul(146) | 126
        );
        assert_eq!(
            Parser::<u64>::new().eval("-1245 - 214_456").unwrap(),
            1245u64.wrapping_neg() - 214456
        );
        assert_eq!(
            Parser::<u16>::new().eval("max(1, 2) + min(3, 5) + pow(2, 3)").unwrap(),
            1.max(2) + 3.min(5) + 2u16.pow(3)
        );

        assert!(
            matches!(
                Parser::<i8>::new().eval("256"),
                Err(ParserError{..})
            )
        );
        assert!(
            matches!(
                Parser::<i8>::new().eval("1+4 5*4"),
                Err(ParserError{..})
            )
        );
        assert!(
            matches!(
                Parser::<i8>::new().eval("(1+4 ) ) * 3"),
                Err(ParserError{..})
            )
        );     
        assert!(
            matches!(
                Parser::<i8>::new().eval("1++41"),
                Err(ParserError{..})
            )
        );                                   
    }

    #[test]
    fn parse_expr_with_context() {
        let ctx = [("x", 5), ("y", 2)];
        assert_eq!(
            Parser::<i32>::new().eval_context("1 + y * 3 - (8 ^ x) | 15 / 2 % 9 & 25", &ctx).unwrap(), 
            1 + 2 * 3 - (8 ^ 5) | 15 / 2 % 9 & 25
        );
        assert_eq!(
            Parser::<i32>::new().eval_context("(1 == 0) + 5 * (3 >= y)", &ctx).unwrap(),
            5
        );
        assert_eq!(
            Parser::<i32>::new().eval_context("max(1, y) + min(9, x) + pow(2, x)", &ctx).unwrap(),
            1.max(2) + 9.min(5) + 2i32.pow(5)
        );

        assert!(
            matches!(
                Parser::<i32>::new().eval_context("1+x y*4", &ctx),
                Err(ParserError{..})
            )
        );
    }
}
