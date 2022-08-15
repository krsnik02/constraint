use regex_lexer::{Lexer, LexerBuilder, Token};

#[derive(Clone, Debug)]
pub enum Term<'s> {
    Var(usize),
    Apply(Box<Term<'s>>, Box<Term<'s>>),
    Lambda(&'s str, Box<Term<'s>>),
    Let(&'s str, Box<Term<'s>>, Box<Term<'s>>),
    Coerce(Type<'s>),
}

impl<'s> Term<'s> {
    pub fn typed_lambda(name: &'s str, ty: Type<'s>, body: Box<Self>) -> Self {
        // λ(x : t) e ==> let x = λ(x) (x : t) in e
        Self::Let(
            name,
            Box::new(Self::Lambda(
                name,
                Box::new(Self::annotate(Box::new(Self::Var(1)), ty)),
            )),
            body,
        )
    }

    pub fn annotate(term: Box<Self>, ty: Type<'s>) -> Self {
        // (e : t) ==> coerce[t] e
        Self::Apply(Box::new(Self::Coerce(ty)), term)
    }
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

struct Parser<'s> {
    tokens: std::iter::Peekable<regex_lexer::Tokens<'static, 's, TokenKind>>,
    type_vars: Vec<&'s str>,
    term_vars: Vec<&'s str>,
}

impl<'s> Parser<'s> {
    fn new(s: &'s str) -> Self {
        Self {
            tokens: LEXER.tokens(s).peekable(),
            type_vars: Vec::new(),
            term_vars: Vec::new(),
        }
    }

    fn parse_term(&mut self) -> Option<Term<'s>> {
        let mut term = None;
        loop {
            let arg = match self.tokens.peek().map(|tok| (tok.kind, tok.text)) {
                Some((TokenKind::Identifier, text)) => {
                    self.tokens.next();
                    self.term_vars
                        .iter()
                        .rev()
                        .position(|var| *var == text)
                        .map(Term::Var)?
                }
                Some((TokenKind::Lambda, _)) => {
                    self.tokens.next();
                    self.require(TokenKind::OpenParen)?;
                    let name = self.require(TokenKind::Identifier)?.text;
                    match self.tokens.next().map(|tok| tok.kind) {
                        Some(TokenKind::CloseParen) => {
                            let body = self.with_term(name, Self::parse_term)?;
                            Term::Lambda(name, Box::new(body))
                        }
                        Some(TokenKind::Colon) => {
                            let ty = self.parse_type()?;
                            self.require(TokenKind::CloseParen)?;
                            let body = self.with_term(name, Self::parse_term)?;
                            Term::typed_lambda(name, ty, Box::new(body))
                        }
                        _ => return None,
                    }
                }
                Some((TokenKind::KeywordLet, _)) => {
                    self.tokens.next();
                    let id = self.require(TokenKind::Identifier)?.text;
                    self.require(TokenKind::Equal)?;
                    let value = self.parse_term()?;
                    self.require(TokenKind::KeywordIn)?;
                    let body = self.with_term(id, Self::parse_term)?;
                    Term::Let(id, Box::new(value), Box::new(body))
                }
                Some((TokenKind::OpenParen, _)) => {
                    self.tokens.next();
                    let term = self.parse_term()?;
                    match self.tokens.next().map(|tok| tok.kind) {
                        Some(TokenKind::CloseParen) => term,
                        Some(TokenKind::Colon) => {
                            let ty = self.parse_type()?;
                            Term::annotate(Box::new(term), ty)
                        }
                        _ => return None,
                    }
                }
                _ => break term,
            };

            term = match term {
                None => Some(arg),
                Some(func) => Some(Term::Apply(Box::new(func), Box::new(arg))),
            }
        }
    }

    fn with_term<T>(&mut self, id: &'s str, f: impl FnOnce(&mut Self) -> T) -> T {
        self.term_vars.push(id);
        let t = f(self);
        self.term_vars.pop();
        t
    }

    fn parse_type(&mut self) -> Option<Type<'s>> {
        let arg = match self.tokens.next().map(|tok| (tok.kind, tok.text)) {
            Some((TokenKind::Identifier, text)) => self
                .type_vars
                .iter()
                .rev()
                .position(|var| *var == text)
                .map(Type::Var)?,
            Some((TokenKind::Forall, _)) => {
                self.require(TokenKind::OpenParen)?;
                let id = self.require(TokenKind::Identifier)?.text;
                let bound = match self.tokens.next().map(|tok| tok.kind) {
                    Some(TokenKind::CloseParen) => None,
                    Some(TokenKind::OpenParen) => Some(self.parse_type()?),
                    _ => return None,
                };
                let body = self.with_type(id, Self::parse_type)?;
                Type::Forall(id, bound.map(Box::new), Box::new(body))
            }
            _ => return None,
        };

        if let Some(TokenKind::Arrow) = self.tokens.peek().map(|tok| tok.kind) {
            self.tokens.next();
            self.parse_type()
                .map(|ret| Type::Arrow(Box::new(arg), Box::new(ret)))
        } else {
            Some(arg)
        }
    }

    fn with_type<T>(&mut self, id: &'s str, f: impl FnOnce(&mut Self) -> T) -> T {
        self.type_vars.push(id);
        let t = f(self);
        self.type_vars.pop();
        t
    }

    #[must_use]
    fn require(&mut self, kind: TokenKind) -> Option<Token<'s, TokenKind>> {
        match self.tokens.next() {
            Some(token) if token.kind == kind => Some(token),
            _ => None,
        }
    }
}
