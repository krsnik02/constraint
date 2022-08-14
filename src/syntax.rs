use std::collections::HashMap;

use regex_lexer::{LexerBuilder, Lexer, Token};

#[derive(Clone, Debug)]
pub enum Term<'s> {
    Var(usize),
    Apply(Box<Term<'s>>, Box<Term<'s>>),
    Lambda(&'s str, Box<Term<'s>>),
    Let(&'s str, Box<Term<'s>>, Box<Term<'s>>),
    Coerce(Box<Type<'s>>),
}

#[derive(Clone, Debug)]
pub enum Type<'s> {
    Var(usize),
    Arrow(Box<Type<'s>>, Box<Type<'s>>),
    Forall(&'s str, Option<Box<Type<'s>>>, Box<Type<'s>>),
}

pub fn parse_term<'s>(s: &'s str) -> Option<Term<'s>> {
    Parser::new(s).parse_term()
}

pub fn parse_type<'s>(s: &'s str) -> Option<Type<'s>> {
    Parser::new(s).parse_type()
}

struct Parser<'s> {
    tokens: std::iter::Peekable<regex_lexer::Tokens<'static, 's, TokenKind>>,

    type_vars: HashMap<&'s str, Vec<(Option<Type<'s>>, usize)>>,
    type_binders: usize,

    term_vars: HashMap<&'s str, Vec<(Option<Type<'s>>, usize)>>,
    term_binders: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    Identifier,
    KeywordLet,
    KeywordIn,
    Lambda,
    Forall,
    Arrow,
    OpenParen,
    CloseParen,
    LessThanOrEqual,
    Colon,
    Equal,
}

lazy_static::lazy_static! {
    static ref LEXER: Lexer<TokenKind> = LexerBuilder::new()
        .ignore(r"\p{White_Space}")
        .token(r"\p{XID_Start}\p{XID_Continue}*", TokenKind::Identifier)
        .token("let", TokenKind::KeywordLet)
        .token("in", TokenKind::KeywordIn)
        .token("λ", TokenKind::Lambda)
        .token("∀", TokenKind::Forall)
        .token("→", TokenKind::Arrow)
        .token(r"\(", TokenKind::OpenParen)
        .token(r"\)", TokenKind::CloseParen)
        .token("≤", TokenKind::LessThanOrEqual)
        .token(":", TokenKind::Colon)
        .token("=", TokenKind::Equal)
        .build().unwrap();
}

impl<'s> Parser<'s> {
    fn new(s: &'s str) -> Parser<'s> {
        Parser { 
            tokens: LEXER.tokens(s).peekable(), 
            type_vars: HashMap::new(),
            type_binders: 0,
            term_vars: HashMap::new(),
            term_binders: 0,
        }
    }

    fn parse_term(&mut self) -> Option<Term<'s>> {
        let mut term = None;
        loop {
            let arg = match self.tokens.peek() {
                Some(&Token { kind: TokenKind::Identifier, text, .. }) => { 
                    self.tokens.next(); 
                    self.term_variable(text)? 
                }
                Some(Token { kind: TokenKind::Lambda, .. }) => { 
                    self.tokens.next(); 
                    self.term_lambda()? 
                }
                Some(Token { kind: TokenKind::KeywordLet, .. }) => { 
                    self.tokens.next(); 
                    self.term_let()? 
                }
                Some(Token { kind: TokenKind::OpenParen, .. }) => { 
                    self.tokens.next(); 
                    self.term_paren()? 
                }
                _ => break term,
            };

            term = match term {
                None => Some(arg),
                Some(func) => Some(Term::Apply(Box::new(func), Box::new(arg))),
            }
        }
    }

    fn term_variable(&mut self, id: &'s str) -> Option<Term<'s>> {
        let binder = self.term_vars.get(&id).unwrap().last().unwrap().1;
        Some(Term::Var(binder))
    }

    fn term_lambda(&mut self) -> Option<Term<'s>> {
        self.require(TokenKind::OpenParen)?;
        let id = self.require(TokenKind::Identifier)?;
        match self.tokens.next() {
            Some(Token { kind: TokenKind::CloseParen, .. }) => self.term_lambda_untyped(id.text),
            Some(Token { kind: TokenKind::Colon, .. }) => self.term_lambda_typed(id.text),
            _ => None,
        }
    }

    fn term_lambda_untyped(&mut self, id: &'s str) -> Option<Term<'s>> {
        self.bind_term(id, None);
        let body = self.parse_term()?;
        self.unbind_term(id);
        Some(Term::Lambda(id, Box::new(body)))
    }

    fn term_lambda_typed(&mut self, id: &'s str) -> Option<Term<'s>> {
        let ty = self.parse_type()?;
        self.require(TokenKind::CloseParen)?;
        self.bind_term(id, None);
        let body = self.parse_term()?;
        self.unbind_term(id);
        // λ(x : t) e == let x = λ(x) coerce[t] x in e
        Some(Term::Let(id, 
            Box::new(Term::Lambda(id, 
                Box::new(Term::Apply(
                    Box::new(Term::Coerce(Box::new(ty))),
                    Box::new(Term::Var(1)),
                )),
            )), 
            Box::new(body),
        ))
    }

    fn term_let(&mut self) -> Option<Term<'s>> {
        let id = self.require(TokenKind::Identifier)?;
        self.require(TokenKind::Equal)?;
        let value = self.parse_term()?;
        self.require(TokenKind::KeywordIn)?;
        self.bind_term(id.text, None);
        let body = self.parse_term()?;
        self.unbind_term(id.text);
        Some(Term::Let(id.text, Box::new(value), Box::new(body)))
    }

    fn term_paren(&mut self) -> Option<Term<'s>> {
        let term = self.parse_term()?;
        match self.tokens.next() {
            Some(Token { kind: TokenKind::CloseParen, .. }) => Some(term),
            Some(Token { kind: TokenKind::Colon, .. }) => {
                let typ = self.parse_type()?;
                // (e : t) == coerce[t] e
                Some(Term::Apply(Box::new(Term::Coerce(Box::new(typ))), Box::new(term)))
            }
            _ => None,
        }
    }
    
    fn bind_term(&mut self, id: &'s str, ty: Option<Type<'s>>) {
        self.term_vars.entry(id).or_default().push((ty, self.term_binders));
        self.term_binders += 1;
    }

    fn unbind_term(&mut self, id: &'s str) -> Option<Type<'s>> {
        self.term_binders -= 1;
        self.term_vars.get_mut(&id).unwrap().pop().unwrap().0
    }

    fn parse_type(&mut self) -> Option<Type<'s>> {
        let arg = match self.tokens.next() {
            Some(Token { kind: TokenKind::Identifier, text, .. }) => self.type_variable(text)?,
            Some(Token { kind: TokenKind::Forall, .. }) => self.type_forall()?,
            _ => return None,
        };

        if let Some(Token { kind: TokenKind::Arrow, .. }) = self.tokens.peek() {
            self.tokens.next();
            self.parse_type().map(|ret| Type::Arrow(Box::new(arg), Box::new(ret)))
        } else {
            Some(arg)
        }
    }

    fn type_variable(&mut self, id: &'s str) -> Option<Type<'s>> {
        let binder = self.type_vars.get(&id).unwrap().last().unwrap().1;
        Some(Type::Var(binder))
    }

    fn type_forall(&mut self) -> Option<Type<'s>> {
        self.require(TokenKind::OpenParen)?;
        let id = self.require(TokenKind::Identifier)?;
        match self.tokens.next() {
            Some(Token { kind: TokenKind::CloseParen, .. }) => self.type_forall_bottom(id.text),
            Some(Token { kind: TokenKind::LessThanOrEqual, .. }) => self.type_forall_bound(id.text),
            _ => None,
        }
    }

    fn type_forall_bottom(&mut self, id: &'s str) -> Option<Type<'s>> {
        self.bind_type(id, None);
        let body = self.parse_type()?;
        self.unbind_type(id);
        Some(Type::Forall(id, None, Box::new(body)))
    }

    fn type_forall_bound(&mut self, id: &'s str) -> Option<Type<'s>> {
        let bound = self.parse_type()?;
        self.require(TokenKind::CloseParen)?;
        self.bind_type(id, Some(bound));
        let body = self.parse_type()?;
        let bound = self.unbind_type(id).unwrap();
        Some(Type::Forall(id, Some(Box::new(bound)), Box::new(body)))
    }

    fn bind_type(&mut self, id: &'s str, ty: Option<Type<'s>>) {
        self.type_vars.entry(id).or_default().push((ty, self.type_binders));
        self.type_binders += 1;
    }

    fn unbind_type(&mut self, id: &'s str) -> Option<Type<'s>> {
        self.type_binders -= 1;
        self.type_vars.get_mut(&id).unwrap().pop().unwrap().0
    }
    
    #[must_use]
    fn require(&mut self, kind: TokenKind) -> Option<Token<'s, TokenKind>> {
        match self.tokens.next() {
            Some(token) if token.kind == kind => Some(token),
            _ => None
        }
    }
}