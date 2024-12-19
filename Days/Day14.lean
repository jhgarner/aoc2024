import Utils

open Parser Char ASCII

def sizeNeZero (size: Size): Prop := NeZero size.x ∧ NeZero size.y

def Pos.wrapAdd [NeZero size.x] [NeZero size.y] (p: Pos size) (dir: Dir): Pos size :=
  let x := Fin.ofNat' size.x $ ((p.x + dir.dx) % size.x).natAbs
  let y := Fin.ofNat' size.y $ ((p.y + dir.dy) % size.y).natAbs
  {x, y}

namespace Day14

structure Robot (size: Size) where
  pos: Pos size
  dir: Dir
  nex: NeZero size.x
  ney: NeZero size.y

def plotRobot (g: Grid size Char) (r: Robot size): Grid size Char :=
  (g.setFocus r.pos).set '#'

instance : ToString (List $ Robot size) where
  toString rs :=
    if p:size.x > 0 ∧ size.y > 0
      then
        let rows := SArray.replicate (SArray.replicate ' ')
        let focus := ⟨Fin.mk 0 p.left, Fin.mk 0 p.right⟩
        toString $ rs.foldl plotRobot {rows, focus}
      else ""

structure SomeRobots where
  size: Size
  arr: Array $ Robot size

def Robot.step  (r: Robot size): Robot size :=
  let _ := r.nex
  let _ := r.ney
  {r with pos := r.pos.wrapAdd r.dir}

def walkAround (rs: List $ Robot size): Nat → List (Robot size)
| 0 => rs
| n + 1 =>
  if (toString rs).containsSubstr "##########"
    then dbgTrace s!"\n {n}\n{rs}" fun _ => walkAround (rs.map Robot.step) n
    else walkAround (rs.map Robot.step) n

structure Quads where
  tl: Nat
  tr: Nat
  bl: Nat
  br: Nat

def Quads.mul (q: Quads): Nat := q.tl * q.tr * q.bl * q.br
def Quads.zero: Quads := {tl := 0, tr := 0, bl := 0, br := 0}

def score (q: Quads) (r: Robot size): Quads := Id.run do
  let sx := size.x / 2
  let sy := size.y / 2
  if r.pos.x < sx ∧ r.pos.y < sy then return {q with tl := q.tl + 1}
  if r.pos.x > sx ∧ r.pos.y < sy then return {q with tr := q.tr + 1}
  if r.pos.x < sx ∧ r.pos.y > sy then return {q with bl := q.bl + 1}
  if r.pos.x > sx ∧ r.pos.y > sy then return {q with br := q.br + 1}
  q

def part1 (rs: SomeRobots): Nat :=
  ((walkAround rs.arr.toList 100).foldl score Quads.zero).mul

-- Example doesn't work without changing this
/- def parseLine: AocParser $ Robot ⟨11, 7⟩ := do -/
def parseLine: AocParser $ Robot ⟨101, 103⟩ := do
  let pos <- Pos.mk <$> (string "p=" *> parseFin) <*> (string "," *> parseFin)
  let dir <- Dir.mk <$> (string " v=" *> parseInt) <*> (string "," *> parseInt)
  let nex := ⟨by simp⟩
  let ney := ⟨by simp⟩
  pure {pos, dir, nex, ney}

def parser: AocParser $ SomeRobots := do
  let arr <- sepEndBy1 eol parseLine
  endOfInput
  pure {arr}

def part2 (rs: SomeRobots): Nat :=
  ((walkAround rs.arr.toList 10000).foldl score Quads.zero).mul

def day: Day := {parser, part1, part2}

