use crate::parser::ParserError;

#[derive(Debug, Clone, PartialEq)]
pub enum LexToken {
    LeftParen,
    RightParen,
    Comma,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    And,
    Or,
    Xor,
    Not,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    LeftShift,
    RightShift,
    Equal,
    EqualEqual,
    NotEqual,
    Variable(String),
    Number(String),
}

impl std::fmt::Display for LexToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexToken::LeftParen => write!(f, "("),
            LexToken::RightParen => write!(f, ")"),
            LexToken::Comma => write!(f, ","),
            LexToken::Plus => write!(f, "+"),
            LexToken::Minus => write!(f, "-"),
            LexToken::Star => write!(f, "*"),
            LexToken::Slash => write!(f, "/"),
            LexToken::Percent => write!(f, "%"),
            LexToken::And => write!(f, "&"),
            LexToken::Or => write!(f, "|"),
            LexToken::Xor => write!(f, "^"),
            LexToken::Not => write!(f, "!"),
            LexToken::Less => write!(f, "<"),
            LexToken::LessEqual => write!(f, "<="),
            LexToken::Greater => write!(f, ">"),
            LexToken::GreaterEqual => write!(f, ">="),
            LexToken::LeftShift => write!(f, "<<"),
            LexToken::RightShift => write!(f, ">>"),
            LexToken::Equal => write!(f, "="),
            LexToken::EqualEqual => write!(f, "=="),
            LexToken::NotEqual => write!(f, "!="),
            LexToken::Variable(s) => write!(f, "{s}"),
            LexToken::Number(i) => write!(f, "{i}"),
        }
    }
}

pub struct Lexer {
    tokens: Vec<LexToken>,
}

impl Lexer {
    /// Convert string to Vec<LexToken>.
    /// If the first character without '_' is ascii_alphabetic, it is interpreted as Variable
    /// If the first character is numeric, it is interpreted as a Number
    /// It is allowed to use '_' for Variable or Number
    /// variable -> OK: `x`, `abc`, `_y12` NG: `____`, `12a`
    /// number -> OK: `123`, `2_000`, NG: `_123`, `12EF`
    pub fn new(src: &str) -> Result<Lexer, ParserError> {
        let mut tokens = vec![];
        let mut src_iter = src.chars().peekable();
        while let Some(c) = src_iter.next() {
            if c.is_whitespace() {
                continue;
            }
            let next_token = match c {
                '(' => Ok(LexToken::LeftParen),
                ')' => Ok(LexToken::RightParen),
                ',' => Ok(LexToken::Comma),
                '+' => Ok(LexToken::Plus),
                '-' => Ok(LexToken::Minus),
                '*' => Ok(LexToken::Star),
                '/' => Ok(LexToken::Slash),
                '%' => Ok(LexToken::Percent),
                '&' => Ok(LexToken::And),
                '|' => Ok(LexToken::Or),
                '^' => Ok(LexToken::Xor),
                '!' => {
                    match src_iter.peek() {
                        Some('=') => {
                            src_iter.next();
                            Ok(LexToken::NotEqual)
                        },
                        _ => Ok(LexToken::Not)
                    }
                },
                '<' => {
                    match src_iter.peek() {
                        Some('=') => {
                            src_iter.next();
                            Ok(LexToken::LessEqual)
                        },
                        Some('<') => {
                            src_iter.next();
                            Ok(LexToken::LeftShift)
                        },
                        _ => Ok(LexToken::Less)
                    }
                },
                '>' => {
                    match src_iter.peek() {
                        Some('=') => {
                            src_iter.next();
                            Ok(LexToken::GreaterEqual)
                        },
                        Some('>') => {
                            src_iter.next();
                            Ok(LexToken::RightShift)
                        },
                        _ => Ok(LexToken::Greater)
                    }
                },
                '=' => {
                    match src_iter.peek() {
                        Some('=') => {
                            src_iter.next();
                            Ok(LexToken::EqualEqual)
                        },
                        _ => Ok(LexToken::Equal)
                    }
                },
                '0'..='9' => {
                    let mut num = c.to_string();
                    let mut non_numeric_char = false;
                    while let Some(next_char) = src_iter.peek() {
                        match next_char {
                            '_' | '0'..='9' => {
                                num.push(*next_char);
                                src_iter.next();
                            },
                            'a'..='z' | 'A'..='Z' => {
                                non_numeric_char = true;
                                num.push(*next_char);
                                src_iter.next();
                            }
                            _ => {break;}
                        }
                    }
                    if !non_numeric_char {
                        Ok(LexToken::Number(num))
                    }
                    else {
                        return Err(ParserError::new(format!("{}: cannot be used for numeric literals", &num).as_str()));
                    }
                },
                '_' | 'a'..='z' | 'A'..='Z' => {
                    let mut var = c.to_string();
                    while let Some(next_char) = src_iter.peek() {
                        if next_char.is_ascii_alphanumeric() || *next_char == '_' {
                            var.push(*next_char);
                            src_iter.next();
                        }
                        else {
                            break;
                        }
                    }
                    if let Some(c) = var.chars().find(|c| *c != '_') {
                        if c.is_ascii_alphabetic() {
                            Ok(LexToken::Variable(var))
                        }
                        else {
                            return Err(ParserError::new(format!("{}: cannot be used as the first character in a variable", &var).as_str()));
                        }
                    }
                    else {
                        return Err(ParserError::new("Underscore-only variables are not allowed"));
                    }
                },
                _ => {
                    return Err(ParserError::new(format!("Unexpected character: {}", c).as_str()));
                }
            };

            match next_token {
                Ok(token) => {
                    tokens.push(token);
                },
                Err(e) => {
                    return Err(e);
                }
            }
        }
        
        Ok(
            Self {
                tokens
            }
        )
    }

    pub fn into_iter(self) -> std::vec::IntoIter<LexToken> {
        self.tokens.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn lexer_test() {
        let input1 = "123 + abc & 5";
        let input2 = "()+-*/><=4==7!=^<< |>>_xyz";
        assert_eq!(Lexer::new(&input1).unwrap().tokens, vec![LexToken::Number(123.to_string()), LexToken::Plus, LexToken::Variable("abc".to_string()), LexToken::And, LexToken::Number(5.to_string())]);
        assert_eq!(Lexer::new(&input2).unwrap().tokens,
            vec![
                    LexToken::LeftParen,
                    LexToken::RightParen,
                    LexToken::Plus,
                    LexToken::Minus,
                    LexToken::Star,
                    LexToken::Slash,
                    LexToken::Greater,
                    LexToken::LessEqual,
                    LexToken::Number(4.to_string()),
                    LexToken::EqualEqual,
                    LexToken::Number(7.to_string()),
                    LexToken::NotEqual,
                    LexToken::Xor,
                    LexToken::LeftShift,
                    LexToken::Or,
                    LexToken::RightShift,
                    LexToken::Variable("_xyz".to_string())
                ]
        );

        let ng1 = "_456";
        let ng2 = "3zx";
        let ng3 = "#";
        let ng4 = "234.0";
        assert!(matches!(Lexer::new(&ng1), Err(ParserError{..})));
        assert!(matches!(Lexer::new(&ng2), Err(ParserError{..})));
        assert!(matches!(Lexer::new(&ng3), Err(ParserError{..})));
        assert!(matches!(Lexer::new(&ng4), Err(ParserError{..})));
    }
}
