import Utils.PreludePlus
import Mathlib.Tactic.DeriveTraversable

-- This sized array might be useful in the future
structure SArray (size : Nat) (α : Type) where
  val : Array α
  val_is_size: val.size = size

def SArray.replicate (a: α) : SArray size α :=
  {val := Array.mk $ List.replicate size a, val_is_size := by simp}

def SArray.modify (arr: SArray size α) (i: Nat) (f: α → α) : SArray size α :=
  {val := arr.val.modify i f, val_is_size := by simp[arr.val_is_size]}

instance : Functor (SArray size) where
  map f 
    | {val, val_is_size} =>
      let val := val.map f
      {val, val_is_size := (by simp[val, val_is_size])}

-- TODO I know that traverse should preserve size, but I don't know how to prove
-- that. For now specialize to option and do a runtime check. The real one
-- should work for any Applicative.
def SArray.traverse (f: α → Option β) (arr: SArray size α) : Option (SArray size β) := do
  let arr <- Traversable.traverse f arr.val
  if p:arr.size = size
    then pure ⟨arr, p⟩
    else none

def SArray.fin_sarray_size (arr : SArray size α) : arr.val.size = size := by
  rw[arr.val_is_size]

instance : GetElem (SArray size α) (Fin size) α (fun _ _ => true) where
  getElem arr i _ := arr.val[i]'(by simp[arr.fin_sarray_size])

def SArray.set (i: Fin size) (a : α) : SArray size α → SArray size α
  | {val, val_is_size} =>
    let val := val.set i a (by simp[val_is_size])
    {val, val_is_size := (by simp[val, val_is_size])}

-- Dependent types are neat
def tryingSize (size : Nat) (arr: Array α) : Option $ SArray size α :=
  if proof: arr.size = size then some ⟨arr, proof⟩ else none

def SArray.of (arr: Array α) : SArray arr.size α := ⟨arr, rfl⟩

def SArray.mapFinIdx (arr : SArray size α) (f : Fin size → α → β) : SArray size β :=
  { val := arr.val.mapFinIdx fun n a => f (arr.fin_sarray_size ▸ n) a
  , val_is_size := by rw[Array.size_mapFinIdx]; exact arr.fin_sarray_size
  }

def SArray.findSomeIdx? (arr: SArray size α) (f: Fin size → α → Option β) : Option β :=
  (arr.mapFinIdx fun i a => (i, a)).val.findSome? $ Function.uncurry f

-- These are needed for Grid
structure Size where
  x : Nat
  y : Nat

structure Pos (within : Size) where
  x : Fin within.x
  y : Fin within.y
deriving BEq, Hashable

instance : ToString (Pos size) where
  toString pos := s!"({pos.x}, {pos.y})"

structure Dir where
  dx : Int
  dy : Int

instance : Neg Dir where
  neg dir := ⟨-dir.dx, -dir.dy⟩

instance : HSub (Pos size) (Pos size) Dir where
  hSub l r := ⟨l.x - r.x, l.y - r.y⟩

instance : HAdd (Pos size) Dir (Option $ Pos size) where
  hAdd l r :=
    let x := l.x + r.dx
    let y := l.y + r.dy
    Pos.mk <$> x.asFin <*> y.asFin

-- Grid will likely be useful again
structure Grid (size : Size) (α : Type) where
  rows : SArray size.y (SArray size.x α)
  focus : Pos size

-- Dependent types are neat
structure SomeGrid (α : Type) where
  size: Size
  val: Grid size α

-- Fails if all the sub-arrays aren't the same size
def SomeGrid.tryMk (rows : Array $ Array α) : Option $ SomeGrid α := do
  let x <- Array.size <$> rows[0]?
  let rows <- traverse (tryingSize x) rows
  let y := rows.size
  if p: x > 0 ∧ y > 0 then
    some { size := {x, y}
         , val := { rows := {val := rows, val_is_size := rfl}
                  , focus := ⟨Fin.mk 0 p.left, Fin.mk 0 p.right⟩
                  }
         }
  else none


-- Proofs that the focuses will always be inside the grid
def Grid.pos_y_in_bound (grid : Grid size α)
  : grid.focus.y < grid.rows.val.size := by
  rw[grid.rows.val_is_size]
  simp

def Grid.pos_x_in_bound (grid : Grid size α)
  : grid.focus.x < (grid.rows.val[grid.focus.y]'(pos_y_in_bound grid)).val.size := by
  rw[(grid.rows.val[grid.focus.y]'(pos_y_in_bound grid)).val_is_size]
  simp

def Grid.mapFinIdx (f : Pos size → α -> β) (grid : Grid size α) : Grid size β :=
  { rows := grid.rows.mapFinIdx
      fun y cols => cols.mapFinIdx
        fun x cell => f ⟨x, y⟩ cell
  , focus := grid.focus}

def Grid.map (f : α -> β) (grid : Grid size α) : Grid size β :=
  grid.mapFinIdx fun _ a => f a

def Grid.traverse (f: α → Option β) (g: Grid size α) : Option $ Grid size β :=
  g.rows.traverse (fun arr => arr.traverse f) <&> fun rows => {g with rows}

-- Grid is a Comonad, but Lean doesn't have that as a class yet
def Grid.extract (grid: Grid size α) : α :=
  (grid.rows.val[grid.focus.y]'(pos_y_in_bound grid)).val[grid.focus.x]'(pos_x_in_bound grid)

def Grid.extend (f : Grid size α → β) (grid: Grid size α) : Grid size β :=
  grid.mapFinIdx fun pos _ => f {rows := grid.rows, focus := pos}

def Grid.setFocus (g: Grid size α) (focus: Pos size) : Grid size α :=
  {g with focus}

def Grid.step : Grid size α → Dir → Option (Grid size α)
  | grid@{focus := {x, y}, ..}, {dx, dy} => do
    some {grid with focus := ⟨<- x + dx, <- y + dy⟩}

def Grid.fold (f: β → α → β) (init: β) (grid : Grid size α) : β :=
  grid.rows.val.foldl (fun accum cols => cols.val.foldl f accum) init

def Grid.sum (grid : Grid size Nat) : Nat := grid.fold HAdd.hAdd 0

def Grid.across (f : β → α → β) (initial : β) (grid: Grid size α) (dir: Dir) : Nat → Option β
  | 0 => some $ f initial grid.extract
  | n + 1 => do
    let stepped <- grid.step dir
    let accum <- stepped.across f initial dir n
    some $ f accum grid.extract

def Grid.set (a: α) : Grid size α → Grid size α
  | {rows, focus} =>
    { rows := rows.modify focus.y (·.set focus.x a), focus }
