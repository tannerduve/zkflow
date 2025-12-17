import «ZkLeanCompiler».Lean.AST
import Parser

open Parser
open Parser.Char
open Parser.Char.ASCII

namespace ZkLeanCompiler.Lean.Parse

/-!
# `.zk` Parser

This module defines a small parser for the demo source language using the `Parser` combinator
library (https://github.com/fgdorais/lean4-parser).
-/

abbrev ZkParser (α : Type) := SimpleParser Substring Char α

namespace ZkParser

/-- Consume zero or more ASCII whitespace characters. -/
def ws : ZkParser PUnit := do
  _ ← takeMany ASCII.whitespace
  return ()

/-- Run `p` then consume trailing whitespace. -/
def lexeme (p : ZkParser α) : ZkParser α :=
  p <* ws

/-- Parse a fixed string token and consume trailing whitespace. -/
def symbol (s : String) : ZkParser String :=
  lexeme (Parser.Char.string s)

/--
Parse a keyword `s` and ensure it is not immediately followed by an identifier character.

This prevents parsing `let` as a prefix of `letter`, etc.
-/
def keyword (s : String) : ZkParser PUnit := do
  _ ← Parser.Char.string s
  notFollowedBy (ASCII.alphanum <|> char '_')
  ws

/-- Parse `(`, then `p`, then `)`, consuming trailing whitespace. -/
def parens (p : ZkParser α) : ZkParser α :=
  symbol "(" *> p <* symbol ")"

/-- First character of an identifier. -/
def identStart : ZkParser Char :=
  ASCII.alpha <|> char '_'

/-- Subsequent character of an identifier. -/
def identRest : ZkParser Char :=
  ASCII.alphanum <|> char '_'

/-- Parse an identifier and consume trailing whitespace. -/
def ident : ZkParser String := lexeme do
  let c ← identStart
  let cs ← takeMany identRest
  return String.mk (c :: cs.toList)

/-- Parse a natural-number literal (decimal) and consume trailing whitespace. -/
def natLit : ZkParser Nat :=
  lexeme (ASCII.parseNat (decimalOnly := true))

section
variable {f : Type} [NatCast f]

/--
Left-associative chain parser.

Parses `p (op p)*` where `op` yields a binary operator.
-/
partial def chainl1 (p : ZkParser α) (op : ZkParser (α → α → α)) : ZkParser α := do
  let mut acc ← p
  while true do
    match ← option? op with
    | some f =>
        let rhs ← p
        acc := f acc rhs
    | none => break
  return acc

mutual
  /-- Parse a full expression, including sequencing with `;`. -/
  partial def expr : ZkParser (Term f) :=
    seqExpr

  /-- Parse an expression excluding top-level sequencing. -/
  partial def exprNoSeq : ZkParser (Term f) :=
    boolOr

  /-- Parse left-associative sequencing `e1 ; e2 ; ...`. -/
  partial def seqExpr : ZkParser (Term f) := do
    let mut acc ← boolOr
    while true do
      match ← option? (symbol ";") with
      | some _ =>
          let rhs ← boolOr
          acc := Term.seq acc rhs
      | none => break
    return acc

  /-- Parse boolean disjunction `||` (left-associative). -/
  partial def boolOr : ZkParser (Term f) :=
    chainl1 boolAnd (symbol "||" *> pure (fun a b => Term.boolB .or a b))

  /-- Parse boolean conjunction `&&` (left-associative). -/
  partial def boolAnd : ZkParser (Term f) :=
    chainl1 eqExpr (symbol "&&" *> pure (fun a b => Term.boolB .and a b))

  /-- Parse equality `==` (left-associative). -/
  partial def eqExpr : ZkParser (Term f) :=
    chainl1 addSub (symbol "==" *> pure (fun a b => Term.eq a b))

  /-- Parse addition/subtraction `+`/`-` (left-associative). -/
  partial def addSub : ZkParser (Term f) :=
    chainl1 mul <|
      (symbol "+" *> pure (fun a b => Term.arith .add a b))
      <|>
      (symbol "-" *> pure (fun a b => Term.arith .sub a b))

  /-- Parse multiplication `*` (left-associative). -/
  partial def mul : ZkParser (Term f) :=
    chainl1 unary (symbol "*" *> pure (fun a b => Term.arith .mul a b))

  /-- Parse unary negation `!`/`not` (right-associative). -/
  partial def unary : ZkParser (Term f) := do
    match ← option? (symbol "!") with
    | some _ => return Term.not (← unary)
    | none =>
        match ← option? (keyword "not") with
        | some _ => return Term.not (← unary)
        | none => atom

  /--
Parse an atomic term:

`let`, `assert ... then ...`, boolean literal, natural literal, variable, or parenthesized expression.
-/
  partial def atom : ZkParser (Term f) :=
    parseLet <|> parseAssert <|> parseBool <|> parseLit <|> parseVar <|> parens expr
  where
    /-- Parse a variable reference. -/
    parseVar : ZkParser (Term f) := do
      let x ← ident
      return Term.var x

    /-- Parse a natural literal into a field element via `NatCast`. -/
    parseLit : ZkParser (Term f) := do
      let n ← natLit
      return Term.lit (Nat.cast n)

    /-- Parse `true` or `false`. -/
    parseBool : ZkParser (Term f) :=
      (keyword "true" *> pure (Term.bool true))
      <|>
      (keyword "false" *> pure (Term.bool false))

    /-- Parse `let x = rhs in body`. -/
    parseLet : ZkParser (Term f) := do
      keyword "let"
      let x ← ident
      _ ← symbol "="
      let rhs ← exprNoSeq
      keyword "in"
      let body ← exprNoSeq
      return Term.lett x rhs body

    /-- Parse `assert (cond) then body` (parentheses optional). -/
    parseAssert : ZkParser (Term f) := do
      keyword "assert"
      let cond ← (parens expr <|> exprNoSeq)
      keyword "then"
      let body ← exprNoSeq
      return Term.assert cond body
end

/-- Parse a complete program from start to end of input. -/
def program : ZkParser (Term f) :=
  ws *> expr <* ws <* endOfInput

end

/-- Parse a `.zk` source program from a string. -/
def parseString {f : Type} [NatCast f] (input : String) : Except String (Term f) :=
  match (program (f := f)).run input with
  | .ok _ t => .ok t
  | .error _ e => .error (toString e)

end ZkParser

end ZkLeanCompiler.Lean.Parse
