import Utils

open Parser
open Std

namespace Day6

inductive Facing where
  | up : Facing
  | right : Facing
  | down : Facing
  | left : Facing
deriving BEq

def Facing.next : Facing → Facing
  | .up => right
  | .right => down
  | .down => left
  | .left => up

def Facing.dir : Facing → Dir
  | .up => ⟨0, -1⟩
  | .right => ⟨1, 0⟩
  | .down => ⟨0, 1⟩
  | .left => ⟨-1, 0⟩

abbrev Visited := List Facing

inductive Cell where
  | empty : Visited → Cell
  | wall : Cell
deriving BEq

def Cell.fromChar : Char → Option Cell
  | '.' | '^' => some $ empty []
  | '#' => some wall
  | _ => none

def Cell.isVisited : Cell → Bool
  | .empty (_ :: _) => true
  | _ => false

structure Map (size: Size) where
  room: Grid size Cell
  facing: Facing

partial def Map.steps : Map size → Map size
  | {room, facing} =>
    if let .wall := room.extract
      then if let .some room := room.step (-facing.dir)
        then {room, facing := facing.next : Map size}.steps
        else {room, facing}
      else
        let room := room.set (.empty [facing])
        if let .some room := room.step facing.dir
          then {room, facing : Map size}.steps
          else {room, facing}

def Map.visited : Map size → Nat
  | {room, ..} => (room.map (bool 0 1 ·.isVisited)).sum

structure SomeMap where
  size: Size
  map: Map size

def SomeMap.of {size: Size} (map: Map size) : SomeMap := {size, map}

def part1 : SomeMap → Nat
  | {map, ..} => map.steps.visited

def findGuard (rows: SArray y $ SArray x Char) : Option $ Pos ⟨x, y⟩ :=
  rows.findSomeIdx?
    fun y cols => cols.findSomeIdx?
      fun x c => if c == '^' then some ⟨x, y⟩ else none

instance : Coe Char (AocParser Char) where
  coe c := char c

def parseLine : AocParser $ Array Char :=
  takeMany1 ('.' <|> '#' <|> '^')

def parser : AocParser SomeMap := do
  let table <- sepEndBy1 Char.eol parseLine
  if let .some map := do
    let grid <- SomeGrid.tryMk table
    let guard <- findGuard grid.val.rows
    let grid := {grid with val := grid.val.setFocus guard}
    let room <- grid.val.traverse Cell.fromChar
    pure $ SomeMap.of {room, facing := .up}
  then pure map
  else throwUnexpectedWithMessage (msg := "Bad grid")

mutual 
  partial def Map.steps2 (start: Pos size) (used: Option $ Pos size) : Map size → HashSet (Option $ Pos size)
    | map@{room, facing} =>
      match room.extract with
        | .wall =>
          if let .some room := room.step (-facing.dir)
            then {room, facing := facing.next : Map size}.steps2 start used
            else HashSet.empty
        | .empty ogFacing =>
          if ogFacing.contains facing ∧ used.isSome
            then HashSet.ofList [used]
            else map.steps2Empty start used ogFacing

  partial def Map.steps2Empty (start: Pos size) (used: Option $ Pos size) (og: List Facing) : Map size → HashSet (Option $ Pos size)
    | {room, facing} =>
      let room := room.set (.empty $ facing :: og)
      let normal := if let .some room := room.step facing.dir
        then {room, facing : Map size}.steps2 start used
        else HashSet.empty
      let paradox := if used.isNone ∧ room.focus != start ∧ room.extract == .empty [facing]
        then
          let room := room.set .wall
          {room, facing : Map size}.steps2 start $ some room.focus
        else HashSet.empty
      normal.union paradox
end

def part2 : SomeMap → Nat
  | {map, ..} => (map.steps2 map.room.focus none).size

def day: Day := {parser, part1, part2}

