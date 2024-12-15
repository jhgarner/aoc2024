import Utils

open Parser Char ASCII
open Std

namespace Day13

structure Presses where
  a: Nat
  b: Nat
deriving BEq, Hashable, Repr

instance : ToString Presses where
  toString | {a, b} => s!"\{a:={a}, b:={b}}"

def allABs: List Presses := Id.run do
  let mut result := []
  for a in [:100] do
    for b in [:100] do
      result := {a, b} :: result
  result

structure Button where
  dir: Dir
  cost: Nat
instance : ToString Button where
  toString | {dir, cost} => s!"\{dir:={dir}, cost:={cost}}"

def valid (target: Dir) (a: Button) (b: Button) (p: Presses): Option Nat :=
  if a.dir * p.a + b.dir * p.b == target
    then .some $ a.cost * p.a + b.cost * p.b
    else .none

structure Machine where
  a: Button
  b: Button
  target: Dir
instance : ToString Machine where
  toString | {a, b, target} => s!"\{a:={a}, b:={b}, target:={target}}"

def part1 (ms: List Machine): Nat := List.sum $ ms.map fun m =>
  (allABs.mapOption $ valid m.target m.a m.b).min?.getD 0

def parseButton (cost: Nat): AocParser Button := do
  -- Not being able to coerce string corectly here is sad :(
  -- It would read pretty well if I could write it without the string function
  let dir <- Dir.mk <$> (string "Button " *> anyToken *> string ": X+" *> parseInt) <*> (string ", Y+" *> parseInt)
  pure {dir, cost}

def parsePrize: AocParser Dir := do
  Dir.mk <$> (string "Prize: " *> string "X=" *> parseInt) <*> (string ", Y=" *> parseInt)

def parseMachine: AocParser Machine := do
  let a <- parseButton 3 <* eol
  let b <- parseButton 1 <* eol
  let target <- parsePrize <* eol
  pure {a, b, target}

def parser: AocParser $ List Machine :=
  Array.toList <$> sepEndBy1 eol parseMachine

def part2 (ms: List Machine): Nat := List.sum $ ms.map fun m => Id.run do
  let m := {m with target := m.target + (10000000000000: Nat)}
  -- Names from the variables I used in Wolfram Alpha
  let q := m.a.dir.dx
  let r := m.a.dir.dy
  let u := m.b.dir.dx
  let v := m.b.dir.dy
  let c := m.target.dx
  let d := m.target.dy
  if q * v == r * u then return 0
  let a := (d*u-c*v) / (r*u-q*v)
  let b := (d*q-c*r) / (q*v-r*u)
  if a < 0 ∨ b < 0 then return 0
  -- Rounding
  if q * a + u * b ≠ c ∨ r * a + v * b ≠ d then return 0

  a.toNat * m.a.cost + b.toNat * m.b.cost

def day: Day := {parser, part1, part2}

