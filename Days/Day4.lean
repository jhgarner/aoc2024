import Utils
import Mathlib.Tactic.DeriveTraversable

open Parser

namespace Day4

def parser : AocParser $ SomeGrid Char := do
  let arrays <- takeMany $ Prod.fst <$> (takeUntil Char.eol anyToken)
  if let .some grid := SomeGrid.tryMk arrays
    then pure grid
    else throwUnexpectedWithMessage (msg := "Invalid Grid")

def isXmas (grid: Grid size Char) (dir : Dir) : Bool :=
  (grid.across String.push "" dir 3) == some "XMAS"

-- All 8 of the adjacent directions
def dirs : List Dir := Id.run do
  let mut result := []
  for dx in [:3] do
    for dy in [:3] do
      if dx ≠ 1 ∨ dy ≠ 1 then
        result := ⟨Int.ofNat dx - 1, Int.ofNat dy - 1⟩ :: result
  result

def xmasAround : Grid size Char → Nat :=
  dirs.countP ∘ isXmas

def part1 (grid : SomeGrid Char) : Nat :=
  (grid.val.extend xmasAround).sum


def isMas (grid : Grid size Char) (dir : Dir) : Bool :=
  [some "MAS", some "SAM"].contains $ grid.across String.push "" dir 2

def isMasDiag (grid: Grid size Char) (dir: Dir) : Bool :=
  ((isMas · dir) <$> grid.step (-dir)).getD false

def masAround (grid: Grid size Char) : Nat :=
  if isMasDiag grid ⟨1, 1⟩ ∧ isMasDiag grid ⟨-1, 1⟩
    then 1
    else 0

def part2 (grid : SomeGrid Char) : Nat :=
  (grid.val.extend masAround).sum

def day: Day := {parser, part1, part2}
