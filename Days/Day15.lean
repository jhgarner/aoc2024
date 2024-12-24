import Utils

open Parser Char ASCII
open Std

namespace Day15

inductive Side where
| left
| right
deriving BEq, Hashable

inductive Tile where
| empty
| box: Option Side → Tile
| wall
| robot
deriving BEq, Hashable
instance : ToString Tile where
  toString | .empty => "." | .box .none => "O" | .box (.some .left) => "[" | .box (.some .right) => "]" | .wall => "#" | .robot => "@"


structure Push (size: Size) where
  tile: Tile
  to: Pos size
deriving BEq, Hashable

-- TODO This is gross
partial def findEmpty (dir: Dir) (g: Grid size Tile): StateT (HashMap (Pos size) $ Push size) Option Unit :=
  let og := g
  match g.extract with
  | .empty => pure ()
  | .box .none => do
    let g <- g.step dir
    let push := {tile := .box .none, to := g.focus}
    if (<- get).get? g.focus == .some push then return
    modify (·.insert g.focus push)
    findEmpty dir g
  | .box (.some .left) => do
    let g <- g.step dir
    let push := {tile := .box $ .some .left, to := g.focus}
    if (<- get).get? g.focus == .some push then return
    modify (·.insert g.focus push)
    findEmpty dir g
    let g <- og.step ⟨1, 0⟩
    if (<- get).get? g.focus == .none
      then modify (·.insert g.focus {tile := .empty, to := g.focus})
    findEmpty dir g
  | .box (.some .right) => do
    let g <- g.step dir
    let push := {tile := .box $ .some .right, to := g.focus}
    if (<- get).get? g.focus == .some push then return
    modify (·.insert g.focus push)
    findEmpty dir g
    let g <- og.step ⟨-1, 0⟩
    if (<- get).get? g.focus == .none
      then modify (·.insert g.focus {tile := .empty, to := g.focus})
    findEmpty dir g
  | .wall => failure
  | .robot => failure

partial def push (g: Grid size Tile) (push: Push size): Grid size Tile :=
  g.setAt push.to push.tile

def step (g: Grid size Tile) (dir: Dir): Grid size Tile :=
  let start := g.focus
  let stepping := do
    let g <- g.step dir
    let (_, pushes) <- (findEmpty dir g) {}
    let g := pushes.values.foldl push g
    let g := g.setAt start Tile.empty
    let g := g.setAt g.focus Tile.robot
    pure g
  dbgTraceVal $ stepping.getD g

def scoreTile (g: Grid size Tile): Nat := Id.run do
  if let .wall := g.extract then return 0
  if let .robot := g.extract then return 0
  if let .empty := g.extract then return 0
  if let .box (.some .right) := g.extract then return 0
  g.focus.y.val * 100 + g.focus.x.val

def score (g: Grid size Tile): Nat := (g.extend scoreTile).sum

structure Problem where
  g: SomeGrid Tile
  steps: Array Dir

def part1 (p: Problem): Nat :=
  score $ p.steps.foldl step p.g.val

def parseTile: AocParser Tile :=
  char '.' $> .empty <|> char '@' $> .robot <|> char 'O' $> .box .none <|> char '#' $> .wall

def parseRow: AocParser $ Array Tile := takeMany1 parseTile

def isStart (g: Grid size Tile): Option $ Pos size :=
  if let .robot := g.extract
    then .some g.focus
    else .none

def parseGrid: AocParser $ SomeGrid Tile := do
  let arrs <- sepEndBy1 eol parseRow
  let maybeG := do
    let g <- SomeGrid.tryMk arrs
    let start <- (g.val.extend isStart).fold (· <|> ·) .none
    pure {g with val := g.val.setFocus start}
  if let .some g := maybeG
    then pure g
    else throwUnexpectedWithMessage (msg := s!"Bad grid {arrs}")

def parseDir: AocParser Dir :=
  char '^' $> ⟨0, -1⟩ <|> char 'v' $> ⟨0, 1⟩ <|> char '<' $> ⟨-1, 0⟩ <|> char '>' $> ⟨1, 0⟩

def parseDirs: AocParser $ Array Dir :=
  Array.flatten <$> sepEndBy1 eol (takeMany parseDir)

def parser: AocParser Problem := do
  let g <- parseGrid
  let _ <- eol
  let steps <- parseDirs
  endOfInput
  pure {g, steps}

def grow (gt: m > n) (f: Fin n): (Fin m) :=
  let _: NeZero m := ⟨by exact Nat.not_eq_zero_of_lt gt⟩
  Fin.ofNat' m f.val

abbrev double (size: Size): Size := ⟨size.x + size.x, size.y⟩

def expandTile (pos: Pos size) (tile: Tile): StateM (Grid (double size) Tile) Unit := do
  -- TODO This is a ton of noise just to multiply a number by 2
  let xNotZero := pos.x.isLt
  let newPos: Pos (double size) := ⟨grow (by simp; exact Nat.zero_lt_of_lt xNotZero) pos.x, pos.y⟩
  let _: NeZero (double size).x := ⟨by simp; exact Nat.not_eq_zero_of_lt xNotZero⟩
  let newPos: Pos (double size) := ⟨newPos.x * 2, newPos.y⟩
  let newPos1: Pos (double size) := ⟨newPos.x + 1, newPos.y⟩
  match tile with
  | .box .none => do
    modify (·.setAt newPos $ .box $ .some .left)
    modify (·.setAt newPos1 $ .box $ .some .right)
  | .robot => do
    modify (·.setAt newPos .robot)
    modify (·.setAt newPos1 .empty)
  | _ => do
    modify (·.setAt newPos tile)
    modify (·.setAt newPos1 tile)

def expand (g: Grid size Tile): Grid (double size) Tile := Id.run do
  let rows := SArray.replicate $ SArray.replicate Tile.empty
  let xNotZero := g.focus.x.isLt
  let _: NeZero (double size).x := ⟨by simp; exact Nat.not_eq_zero_of_lt xNotZero ⟩
  let focus := ⟨grow (by simp; exact Nat.zero_lt_of_lt xNotZero) g.focus.x * 2, g.focus.y⟩
  let bg: Grid (double size) Tile := {rows, focus}
  let (_, bg) := ((g.mapFinIdx expandTile).fold (· *> ·) (pure ())) bg
  bg

def part2 (p: Problem): Nat :=
  score $ p.steps.foldl step $ dbgTraceVal $ expand p.g.val

def day: Day := {parser, part1, part2}

