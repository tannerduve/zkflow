from typing import Any
from dataclasses import dataclass
import re

# ------------------------  TOKENS  --------------------------
@dataclass
class Token:
    typ: str   # KEYWORD, IDENT, NUMBER, OP, DELIM
    val: str

KEYWORDS = {
    "let", "in", "assert",
    "if", "then", "else",
    "true", "false"
}

TOKEN_SPEC = [
    ("NUMBER",   r'\d+(\.\d+)?'),
    ("IDENT",    r'[A-Za-z_]\w*'),
    ("OP",       r'==|&&|\|\||[+\-*!=]'),
    ("DELIM",    r'[(){};,]'),
    ("SKIP",     r'[ \t\n]+'),
    ("MISMATCH", r'.'),
]
REGEX = re.compile('|'.join(f'(?P<{n}>{p})' for n, p in TOKEN_SPEC))

def tokenize(src: str) -> list[Token]:
    toks: list[Token] = []
    for m in REGEX.finditer(src):
        kind = m.lastgroup
        lex  = m.group()
        if kind == "SKIP":
            continue
        if kind == "IDENT" and lex in KEYWORDS:
            toks.append(Token("KEYWORD", lex))
        elif kind == "MISMATCH":
            raise SyntaxError(f"Unexpected char {lex!r}")
        else:
            toks.append(Token(kind, lex))
    return toks

# ------------------------  AST  -----------------------------
@dataclass
class TNum:    val: str
@dataclass
class TBool:   val: bool
@dataclass
class TVar:    name: str
@dataclass
class TBin:    
    op: str
    left: Any
    right: Any
@dataclass
class TNot:    
    expr: Any
@dataclass
class TLet:    
    name: str
    rhs: Any
    body: Any
@dataclass
class TAssert: 
    expr: Any
@dataclass
class TSeq:
    first: Any
    second: Any
@dataclass
class TIfz:    
    cond: Any
    tcase: Any
    fcase: Any

# ---------------------  PARSER  -----------------------------
class Parser:
    def __init__(self, toks): self.toks, self.i = toks, 0
    def peek(self):  return self.toks[self.i] if self.i < len(self.toks) else None
    def advance(self): self.i += 1
    def match(self, typ, val=None):
        tok = self.peek()
        if tok and tok.typ == typ and (val is None or tok.val == val):
            self.advance(); return tok
        return None
    def expect(self, typ, val=None):
        tok = self.match(typ, val)
        if not tok: raise SyntaxError(f"Expected {val or typ}")
        return tok

    def parse(self): 
        expr = self.parse_let()
        if self.peek(): raise SyntaxError("Trailing tokens")
        return expr

    def parse_let(self):
        if self.match("KEYWORD", "let"):
            name = self.expect("IDENT").val
            self.expect("OP", "=")
            rhs  = self.parse_let()
            self.expect("KEYWORD", "in")
            body = self.parse_let()
            return TLet(name, rhs, body)
        return self.parse_seq()

    def parse_seq(self):
        e = self.parse_assert()
        while self.match("DELIM", ";"):
            rhs = self.parse_assert()
            e   = TSeq(e, rhs)
        return e

    def parse_assert(self):
        if self.match("KEYWORD", "assert"):
            self.expect("DELIM", "(")
            e = self.parse_let()
            self.expect("DELIM", ")")
            return TAssert(e)
        return self.parse_if()

    def parse_if(self):
        if self.match("KEYWORD", "if"):
            cond = self.parse_let()
            self.expect("KEYWORD", "then")
            tcase = self.parse_let()
            self.expect("KEYWORD", "else")
            fcase = self.parse_let()
            return TIfz(cond, tcase, fcase)
        return self.parse_logic_or()

    def parse_logic_or(self):
        e = self.parse_logic_and()
        while self.match("OP", "||"):
            e = TBin("||", e, self.parse_logic_and())
        return e

    def parse_logic_and(self):
        e = self.parse_eq()
        while self.match("OP", "&&"):
            e = TBin("&&", e, self.parse_eq())
        return e

    def parse_eq(self):
        e = self.parse_add()
        if self.match("OP", "=="):
            e = TBin("==", e, self.parse_add())
        return e

    def parse_add(self):
        e = self.parse_mul()
        while True:
            if self.match("OP", "+"):
                e = TBin("+", e, self.parse_mul())
            elif self.match("OP", "-"):
                e = TBin("-", e, self.parse_mul())
            else:
                return e

    def parse_mul(self):
        e = self.parse_unary()
        while self.match("OP", "*"):
            e = TBin("*", e, self.parse_unary())
        return e

    def parse_unary(self):
        if self.match("OP", "!"):
            return TNot(self.parse_unary())
        return self.parse_primary()

    def parse_primary(self):
        if tok := self.match("NUMBER"):
            return TNum(tok.val)
        if tok := self.match("KEYWORD", "true"):
            return TBool(True)
        if tok := self.match("KEYWORD", "false"):
            return TBool(False)
        if tok := self.match("IDENT"):
            return TVar(tok.val)
        if self.match("DELIM", "("):
            e = self.parse_let()
            self.expect("DELIM", ")")
            return e
        raise SyntaxError("Unexpected token")
