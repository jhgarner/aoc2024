import Utils

open Parser

namespace Day7

abbrev Collect := MLList (OptionT Id)

def split (ops: List (Nat → Nat → Nat)) : List Nat → Collect Nat
  | [] => failure
  | [x] => pure x
  | x::xs => do
    let total <- split ops xs
    MLList.ofList $ ops.map (· x total)

structure Row where
  target: Nat
  operands: Array Nat

def part (ops: List (Nat → Nat → Nat)) (rows : Array Row) : Nat := Array.sum $ rows.map
  fun {target, operands} =>
    ((split ops operands.toListRev).first (· == target)).getD 0

def part1 := part [Add.add, Mul.mul]

instance : Coe String (AocParser Unit) where
  coe s := ignore $ Char.string s

def parseLine : AocParser Row := do
  let target <- parseNat
  ": "
  let operands <- sepBy1 Char.space parseNat
  pure {target, operands}

def parser : AocParser $ Array Row :=
  sepEndBy1 Char.eol parseLine

def concat (a: Nat) (b: Nat) : Nat := ((toString b) ++ (toString a)).toNat!

def part2 := part [Add.add, Mul.mul, concat]

def day: Day := {parser, part1, part2}
