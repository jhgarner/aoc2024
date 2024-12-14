import Utils

open Parser
open Std

namespace Day10

def orth : List Dir := [⟨0, 1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]

structure Tile (size: Size) where
  height: Nat
  ends: HashSet (Pos size)

def combine (g: Grid size (Tile size)) (u: HashSet (Pos size)) (dir: Dir) :=
  if let .some {height, ends} := Grid.extract <$> g.step dir
    then if height - g.extract.height = 1
      then u.union ends
      else u
    else u

def check (g: Grid size (Tile size)) : Tile size :=
  let {height, ends} := g.extract
  if height = 9
    then {height, ends := {g.focus}}
    else {height, ends :=  orth.foldl (combine g) ends}

def findHikesLen (g: Grid size (Tile size)) : Nat → Grid size (Tile size)
| 0 => g
| n + 1 => findHikesLen (g.extend check) n

def score (tile: Tile size) : Nat :=
  if tile.height = 0
    then tile.ends.size
    else 0

structure SomeMap where
  size: Size
  g: Grid size (Tile size)

def part1 (map: SomeMap) : Nat := ((findHikesLen map.g 10).map score).sum

def digit : AocParser Nat :=
  (String.toNat! ∘ Char.toString) <$> Char.ASCII.numeric

def parseLine : AocParser $ Array Nat := takeMany1 digit
def parseGrid : AocParser $ Array $ Array Nat := sepEndBy1 Char.eol parseLine
def parser : AocParser SomeMap := do
  let arrs <- parseGrid
  if let .some grid := SomeGrid.tryMk arrs
    then
      let tiled := grid.val.map ({height := ·, ends := {}})
      pure {grid with g := tiled}
    else throwUnexpectedWithMessage (msg := "Bad grid")

structure Tile2 where
  height: Nat
  distinct: Nat

def combine2 (g: Grid size Tile2) (s: Nat) (dir: Dir) :=
  if let .some {height, distinct} := Grid.extract <$> g.step dir
    then if height - g.extract.height = 1
      then s + distinct
      else s
    else s

def check2 (g: Grid size Tile2) : Tile2 :=
  let {height, distinct} := g.extract
  if height = 9
    then {height, distinct := 1}
    else {height, distinct := orth.foldl (combine2 g) distinct}

def findHikesLen2 (g: Grid size Tile2) : Nat → Grid size Tile2
| 0 => g
| n + 1 => findHikesLen2 (g.extend check2) n

def Tile2.of: Tile size → Tile2
| {height, ..} => {height, distinct := 0}

def score2 (tile: Tile2) : Nat :=
  if tile.height = 0
    then tile.distinct
    else 0

def part2 (map: SomeMap) : Nat := ((findHikesLen2 (map.g.map Tile2.of) 10).map score2).sum

def day: Day := {parser, part1, part2}

