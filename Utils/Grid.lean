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

def SArray.mapFinIdx (arr : SArray size α) (f : Fin size → α → β) : SArray size β :=
  { val := arr.val.mapFinIdx fun n a => f (arr.fin_sarray_size ▸ n) a
  , val_is_size := by rw[Array.size_mapFinIdx]; exact arr.fin_sarray_size
  }

-- These are needed for Grid
structure Size where
  x : Nat
  y : Nat

structure Pos (within : Size) where
  x : Fin within.x
  y : Fin within.y

structure Dir where
  dx : Int
  dy : Int

instance : Neg Dir where
  neg dir := ⟨-dir.dx, -dir.dy⟩

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


-- Grid is a Comonad, but Lean doesn't have that as a class yet
def Grid.extract (grid: Grid size α) : α :=
  (grid.rows.val[grid.focus.y]'(pos_y_in_bound grid)).val[grid.focus.x]'(pos_x_in_bound grid)

def Grid.extend (f : Grid size α → β) (grid: Grid size α) : Grid size β :=
  grid.mapFinIdx fun pos _ => f {rows := grid.rows, focus := pos}


def Grid.step : Grid size α → Dir → Option (Grid size α)
  | grid@{focus := {x, y}, ..}, {dx, dy} => do
    some {grid with focus := ⟨<- x + dx, <- y + dy⟩}

def Grid.sum (grid : Grid size Nat) : Nat :=
  grid.rows.val.foldl (fun sum cols => cols.val.foldl HAdd.hAdd sum) 0

def Grid.across (f : β → α → β) (initial : β) (grid: Grid size α) (dir: Dir) : Nat → Option β
  | 0 => some $ f initial grid.extract
  | n + 1 => do
    let stepped <- grid.step dir
    let accum <- stepped.across f initial dir n
    some $ f accum grid.extract



