import Utils

open Parser Char

namespace Day3

structure MulOp where
  lhs : Nat
  rhs : Nat
  proof : lhs >= 0 ∧ rhs >= 0 ∧ lhs < 1000 ∧ rhs < 1000

inductive Op where
  | mulOp : MulOp -> Op
  | enable : Op
  | disable : Op

def evalMulOp : MulOp -> Nat
  | {lhs, rhs, ..} => lhs * rhs

def ignoreJunk : AocParser $ Option a := Functor.mapConst none anyToken

def enable : AocParser Op := Functor.mapConst .enable $ string "do()"
def disable : AocParser Op := Functor.mapConst .disable $ string "don't()"

def parseMulOperation : AocParser MulOp := do
  ignore $ string "mul("
  let lhs <- parseNat
  ignore $ string ","
  let rhs <- parseNat
  ignore $ string ")"
  if proof:lhs >= 0 ∧ rhs >= 0 ∧ lhs < 1000 ∧ rhs < 1000 then
    pure {lhs, rhs, proof}
  else throwUnexpected

def parseOp : AocParser Op := .mulOp <$> parseMulOperation <|> enable <|> disable

def parser : AocParser $ Array Op := do
  let {fst := result, ..} <- takeUntil endOfInput (some <$> parseOp <|> ignoreJunk)
  pure $ result.clean

def part1Eval : Op -> Nat
  | .mulOp op => evalMulOp op
  | _ => 0

def part1 (op: Array Op) := (op.map part1Eval).sum

def part2Eval : Op → StateM Bool Nat
  | .enable => do set true; pure 0
  | .disable => do set false; pure 0
  | .mulOp op => do if (<- get) then pure $ evalMulOp op else pure 0

def part2 (op: Array Op) := ((op.mapM part2Eval).run' true).sum

def day: Day := {parser, part1, part2}

