import Utils

open Parser Char ASCII

namespace Day1

structure Problem where
  left : Array Nat
  right : Array Nat
deriving Repr

def parseLine : AocParser (Nat × Nat) := do
  let l <- parseNat
  dropMany whitespace
  let r <- parseNat
  pure (l, r)

def parseLines : AocParser Problem := do
  let lines <- sepEndBy whitespace parseLine
  let (left, right) := lines.unzip
  pure {left, right}

def part1 : Problem → Nat
  | {left, right} => Id.run do
    let lSorted := (left.heapSort (· < ·)).map Int.ofNat
    let rSorted := (right.heapSort (· < ·)).map Int.ofNat
    let difs := lSorted.zipWith rSorted (fun l r => (l - r).natAbs)
    pure (difs.foldl Add.add 0)

def part2 : Problem → Nat
  | {left, right} =>
    let rWithCount := right.map (·, 1)
    let rCounts := Batteries.HashMap.ofListWith rWithCount.toList (Add.add)
    let scores := left.map (fun n => n * rCounts.findD n 0)
    scores.foldl Add.add 0

def day: Day := { Repr := Problem, parser := parseLines, part1, part2 }
