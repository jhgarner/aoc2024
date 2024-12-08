import Utils

open Parser Char ASCII
open Std

namespace Day8

abbrev Antennas size := HashMap Char $ HashSet $ Pos size
abbrev Antinodes size := HashSet $ Pos size

inductive Cell where
  | antenna : Char → Cell
  | empty : Cell

def addAntenna (pos: Pos size) : Cell → Antennas size
  | .antenna c => HashMap.ofList [(c, HashSet.ofList [pos])]
  | _ => HashMap.empty

def mergeAntennas (a: Antennas size) (b: Antennas size) : Antennas size :=
  a.mergeWith (fun _ => HashSet.union) b

def findAntennas (g: Grid size Cell) : Antennas size :=
  (g.mapFinIdx addAntenna).fold mergeAntennas HashMap.empty

def findAntinodes (antennas: Antennas size) (g: Grid size Cell) : Antinodes size :=
  if let .antenna c := g.extract
    then
      let others := (antennas.getD c HashSet.empty).erase g.focus
      let self := g.focus
      let mapped := others.toList.map fun other => self + (self - other)
      HashSet.ofList $ mapped.filterMap id
    else HashSet.empty

def part1 (g: SomeGrid Cell) : Nat :=
  let antinodes := g.val.extend $ findAntinodes $ findAntennas g.val
  (antinodes.fold HashSet.union HashSet.empty).size

def parseCell : AocParser Cell := char '.' $> .empty <|> .antenna <$> alphanum

def parser : AocParser $ SomeGrid Cell := do
  let table <- sepEndBy eol $ takeMany1 parseCell
  if let .some grid := SomeGrid.tryMk table
    then pure grid
    else throwUnexpectedWithMessage (msg := "Bad grid")

partial def steps (g: Grid size Cell) (dir: Dir) : Antinodes size :=
  if let .some g := g.step dir
    then (steps g dir).insert g.focus
    else HashSet.empty

def findAntinodes2 (antennas: Antennas size) (g: Grid size Cell) : Antinodes size :=
  if let .antenna c := g.extract
    then
      let others := (antennas.getD c HashSet.empty).erase g.focus
      let self := g.focus
      let mapped := others.toList.map (steps g $ · - self)
      mapped.foldl HashSet.union HashSet.empty
    else HashSet.empty

def part2 (g: SomeGrid Cell) : Nat :=
  let antinodes := g.val.extend $ findAntinodes2 $ findAntennas g.val
  (antinodes.fold HashSet.union HashSet.empty).size

def day: Day := {parser, part1, part2}
