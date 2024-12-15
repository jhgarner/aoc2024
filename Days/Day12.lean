import Utils

open Parser
open Std

namespace Day12

def orth : List Dir := [⟨0, 1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]

abbrev Visited size := HashSet (Pos size)

structure Tree (α: Type) where
  self: α
  pos: AnyPos
  edgeDirs: List Dir
  others: List $ Tree α
deriving Nonempty

partial def treeify [Nonempty α] [BEq α] (g: Grid size α): StateM (Visited size) (Option $ Tree α) := do
  let pos := g.focus
  if (<- get).contains pos
    then return .none
  modify (·.insert pos)
  let self := g.extract
  let (edgeDirs, neighbors) := orth.mapSplit $ fun dir =>
    ((g.step dir).keepIf (·.extract == self)).elim (Sum.inl dir) Sum.inr
  let others <- neighbors.traverse treeify
  pure $ .some {self, pos := pos.forget, edgeDirs, others := others.catOption}

structure Score where
  area: Nat
  perim: Nat
deriving Nonempty

def Score.total (s: Score) := s.area * s.perim

instance : Add Score where
  add l r := {area := l.area + r.area, perim := l.perim + r.perim}

instance : Zero Score where
  zero := {area := 0, perim := 0}

-- TODO I should be able to prove this isn't partial. It's just cata.
partial def score (t: Tree α): Score :=
  let perim := t.edgeDirs.length
  let others := (t.others.map score).sum
  others + {area := 1, perim}

def go [Nonempty α] [BEq α] (g: Grid size α): Nat := Id.run do
  let extended := g.extend treeify
  let groups <- ((sequence (extended.foldr (· :: ·) [])).run' {}).catOption
  (groups.map (Score.total ∘ score)).sum

def part1 (g: SomeGrid Char): Nat := go g.val

def parser: AocParser $ SomeGrid Char := do
  let arrs <- sepEndBy1 Char.eol $ takeMany1 Char.ASCII.alpha
  if let .some grid := SomeGrid.tryMk arrs
    then pure grid
    else throwUnexpectedWithMessage (msg := "Bad Grid")

structure Edge where
  pos: AnyPos
  dir: Dir
deriving BEq, Hashable

def Tree.edges (t: Tree α): List Edge :=
  t.edgeDirs.map ({pos := t.pos, dir := ·})


partial def mergeEdges (edge: Edge): StateM (HashSet Edge) (Option Edge) := do
  if ¬(<- get).contains edge then return .none
  modify (·.erase edge)
  let adj := orth.map ({edge with pos := edge.pos + ·})
  let _ <- adj.traverse mergeEdges
  pure $ .some edge

def numSides (edges: List Edge): Nat := Id.run do
  let canonEdges <- (edges.traverse mergeEdges).run' $ HashSet.ofList edges
  canonEdges.catOption.length

-- TODO Also just cata so should not be partial
partial def Tree.getEdges (t: Tree α): List Edge :=
  t.edges ++ t.others.flatMap getEdges

def bulkDiscount (t: Tree α) (s: Score): Score :=
  {s with perim := numSides t.getEdges}

def go2 [Nonempty α] [BEq α] (g: Grid size α): Nat := Id.run do
  let extended := g.extend treeify
  let groups <- ((sequence (extended.foldr (· :: ·) [])).run' {}).catOption
  (groups.map (fun g => (bulkDiscount g $ score g).total)).sum

def part2 (g: SomeGrid Char): Nat := go2 g.val

def day: Day := {parser, part1, part2}
