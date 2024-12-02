import Utils

open Parser Char ASCII

structure Problem where
  left : Array Nat
  right : Array Nat
deriving Repr

def parseLine : SimpleParser Substring Char (Nat × Nat) := do
  let l <- parseNat
  dropMany whitespace
  let r <- parseNat
  pure (l, r)

def parseLines : SimpleParser Substring Char (Array (Nat × Nat)) := do
  sepEndBy whitespace parseLine

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

def readInput : IO Problem := do
  let all <- readAll (<- IO.getStdin) ""
  if let Parser.Result.ok _ result := Parser.run parseLines all then
    let (left, right) := result.unzip
    pure {left, right}
  else pure {left := Array.empty, right := Array.empty}
