#!/usr/bin/env python3
from typing import Any
from dataclasses import dataclass
from pathlib import Path
import re
import sys
import textwrap

# ------------------------  TOKENS  --------------------------

@dataclass

class Token:
    typ: str   # KEYWORD, IDENT, NUMBER, OP, DELIM
    val: str

KEYWORDS = {
    "let", "in", "assert",
    "if", "then", "else",
    "true", "false", "inn"
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

class TNum:
    val: str

@dataclass

class TBool:
    val: bool

@dataclass

class TVar:
    name: str

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
    cond: Any
    body: Any

@dataclass

class TSeq:
    first: Any
    second: Any

@dataclass

class TIfz:
    cond: Any
    tcase: Any
    fcase: Any
    
@dataclass
class TInSet:
    elem : Any
    choices : list[str]

# ---------------------  PARSER  -----------------------------

class Parser:
    def __init__(self, toks: list[Token]):
        self.toks = toks
        self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def advance(self):
        self.i += 1

    def match(self, typ, val=None):
        tok = self.peek()
        if tok and tok.typ == typ and (val is None or tok.val == val):
            self.advance()
            return tok
        return None

    def expect(self, typ, val=None):
        tok = self.match(typ, val)
        if not tok:
            raise SyntaxError(f"Expected {val or typ}")
        return tok

    def parse(self): 
        expr = self.parse_let()
        if self.peek():
            raise SyntaxError("Trailing tokens")
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
            e = TSeq(e, rhs)
        return e

    def parse_assert(self):
        if self.match("KEYWORD", "assert"):
            self.expect("DELIM", "(")
            e = self.parse_let()
            self.expect("DELIM", ")")
            self.expect("KEYWORD", "then")   
            body = self.parse_let()            
            return TAssert(e, body)  
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
        if self.match("KEYWORD", "inn"):
            choices = self._parse_set_literal()
            return TInSet(e, choices)
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
    
    def parse_set_literal(self) -> list[str]:
        self.expect("DELIM", "{")
        nums: list[str] = []
        if not self.match("DELIM", "}"):           # non‑empty set
            while True:
                tok = self.expect("NUMBER")
                nums.append(tok.val)
                if self.match("DELIM", "}"):
                    break
                self.expect("DELIM", ",")
        return nums

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
    

# ------------------  Lean code generation  ------------------

def to_lean(t) -> str:
    match t:
        case TNum(v):      return f"(Term.lit {v})"
        case TBool(b):     return f"(Term.bool {'true' if b else 'false'})"
        case TVar(n):      return f'(Term.var "{n}")'
        case TBin(op, l, r):
            table = {
                "+": "ArithBinOp.add", "-": "ArithBinOp.sub", "*": "ArithBinOp.mul",
                "&&": "BoolBinOp.and", "||": "BoolBinOp.or", "==": None
            }
            if op == "==":
                return f"(Term.eq {to_lean(l)} {to_lean(r)})"
            elif op in ["&&", "||"]:
                return f"(Term.boolB {table[op]} {to_lean(l)} {to_lean(r)})"
            else:
                return f"(Term.arith {table[op]} {to_lean(l)} {to_lean(r)})"
        case TNot(e):      return f"(Term.not {to_lean(e)})"
        case TLet(n, r, b):return f'(Term.lett "{n}" {to_lean(r)} {to_lean(b)})'
        case TAssert(c, b): return f"(Term.assert {to_lean(c)} {to_lean(b)})"
        case TSeq(a, b):   return f"(Term.seq {to_lean(a)} {to_lean(b)})"
        case TIfz(c, t, e):return f"(Term.ifz {to_lean(c)} {to_lean(t)} {to_lean(e)})"
        case TInSet(elem, xs):
            xs_lean = ", ".join(xs)
            return f"(Term.inSet {to_lean(elem)} [{xs_lean}])"
        case _: raise ValueError("unknown AST node")


def emit_lean(code: str, stem: str):
    path = Path("ZkLeanCompiler/Frontend/Parsed.lean")
    path.parent.mkdir(parents=True, exist_ok=True)

    header = textwrap.dedent("""\
        import ZkLeanCompiler.Compile
        import Mathlib.Algebra.Field.Rat
        import Mathlib.Data.Rat.Defs
        open Term

        instance hash : Hashable ℚ where
          hash q :=
            let n := q.num.natAbs
            let d := q.den
            (n + d).toUInt64

        instance witness : Witnessable ℚ (ZKExpr ℚ) where
          witness := do
            let st ← get
            let id := st.allocated_witness_count
            set { st with allocated_witness_count := id + 1 }
            pure (ZKExpr.WitnessVar id)

        instance : JoltField ℚ where
          toField := inferInstance
          toBEq := inferInstance
          toToString := inferInstance
          toInhabited := inferInstance
          toWitnessable := witness
          toHashable := hash
          eq_of_beq := by
            intros a b h
            simp only [BEq.beq, decide_eq_true_eq] at h
            exact h
          rfl := by
            intro a
            simp only [BEq.beq, decide_eq_true_eq]
    """)
    parsed_def = f"\ndef parsedProg_{stem} : Term ℚ := {code}\n"
    path.write_text(header + parsed_def)
    print(f"Overwrote Parsed.lean with parsedProg_{stem}")



# ------------------  CLI  ------------------

def main():
    if len(sys.argv) != 2:
        print("Usage: zkparse.py examples/test.zk"); sys.exit(1)
    src_path = Path(sys.argv[1])
    stem = src_path.stem
    src = src_path.read_text()
    toks = tokenize(src)
    ast = Parser(toks).parse()
    lean_code = to_lean(ast)
    emit_lean(lean_code, stem)

if __name__ == "__main__":
    main()
