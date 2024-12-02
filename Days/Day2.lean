import Utils

open Parser Char ASCII

structure Problem where
  levels : Array (Array Nat)
deriving Repr

def parseLine : SimpleParser Substring Char (Array Nat) := do
  sepBy1 (char ' ') parseNat

def parseLines : SimpleParser Substring Char Problem := do
  pure {levels := (<- sepEndBy whitespace parseLine)}

def validStep (n : Int) : Bool := n.natAbs > 0 && n.natAbs <= 3
def validSigns : Option Int → Int → Option Int
  | .none, _ => none
  | .some 0, sign => some sign
  | .some prev, sign => if prev = sign then some sign else none

def isSafe (level : Array Nat) : Bool :=
  let tail := level.toSubarray 1
  let steps := level.zipWith tail (· - Int.ofNat ·)
  let signs := steps.map (·.sign)
  steps.all validStep && (signs.foldl validSigns $ some 0).isSome

def part1 : Problem → Nat
  | {levels} =>
    (levels.filter isSafe).size

partial def allOptions (level : Array Nat) (result : Array Nat) : Nondet Id $ Array Nat :=
  if let .some top := level.get? 0 then
    let rest := level.toSubarray 1
    allOptions rest (result.push top) <|> pure (result ++ rest)
  else pure result

def allValidOptions (level : Array Nat) : List $ Array Nat :=
  (allOptions level #[]).toList'


def part2 : Problem → Nat
  | {levels} =>
    ((levels.map allValidOptions).filter (·.any isSafe)).size

def readInput : IO Problem := do
  let all <- readAll (<- IO.getStdin) ""
  if let Parser.Result.ok _ result := Parser.run parseLines all then
    pure result
  else sorry

