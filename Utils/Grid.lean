import Utils.PreludePlus
import Mathlib.Tactic.DeriveTraversable

-- This sized array might be useful in the future
structure SArray (size : Nat) (α : Type) where
  val : Array α
  val_is_size: val.size = size

instance [ToString α] : ToString (SArray size α) where
  toString arr := arr.val.foldl (· ++ toString ·) ""

instance : EmptyCollection (SArray 0 α) where
  emptyCollection := {val := #[], val_is_size := rfl}

instance [Pure m] [EmptyCollection a]: EmptyCollection (m a) where
  emptyCollection := pure {}

def SArray.map (f: α → β): SArray size α → SArray size β
| {val, val_is_size} =>
  let val := val.map f
  {val, val_is_size := (by simp[val, val_is_size])}

instance : Functor (SArray size) where
  map := SArray.map

instance : LawfulFunctor (SArray size) where
  id_map := by
    simp[Functor.map, SArray.map]
  map_const := by
    simp[Functor.map, Functor.mapConst, SArray.map]
  comp_map := by
    simp[Functor.map, SArray.map]

def SArray.replicate (a: α) : SArray size α :=
  {val := Array.mk $ List.replicate size a, val_is_size := by simp}

def SArray.modify (arr: SArray size α) (i: Nat) (f: α → α) : SArray size α :=
  {val := arr.val.modify i f, val_is_size := by simp[arr.val_is_size]}

def SArray.push (arr: SArray i α) (a: α): SArray (i+1) α :=
  { val := arr.val.push a
  , val_is_size := by simp[Array.size_push, arr.val_is_size]
  }

protected def SArray.traverseHelper
  [Applicative m]
  (i_le_size: i ≤ size)
  (f: α → m β)
  (input: SArray size α)
  (output: m (SArray i β))
  : m (SArray size β) :=
  if p : size = i
    then output <&> fun output => {output with val_is_size := by simp[output.val_is_size, *]}
    else
      have := input.val_is_size
      have i_lt_size: i < size := Nat.lt_of_le_of_ne i_le_size (p ∘ Eq.symm)
      let output := push <$> output <*> f (input.val[i])
      SArray.traverseHelper i_lt_size f input output

def SArray.traverse [Applicative m] (f: α → m β) (arr: SArray size α) : m (SArray size β) :=
  arr.traverseHelper (Nat.zero_le size) f {}

instance : Traversable (SArray size) where
  traverse := SArray.traverse

theorem empty_arr (s: size = 0) (arr: SArray size α): arr = {val := #[], val_is_size := by simp[*]} := by
  induction arr
  simp[Array.size_empty]
  case mk val val_is_size =>
    rewrite [s] at val_is_size
    exact Array.eq_empty_of_size_eq_zero val_is_size

theorem arr_take_size (arr: Array α): arr.take arr.size = arr := by
  simp[Array.take, Array.take.loop]

theorem traverseHelper_id
  (arr: SArray size α)
  (ol: output.val = arr.val.take i):
  SArray.traverseHelper (i := i) (m := Id) i_le_size (fun x => x) arr output = arr := by
    rw[SArray.traverseHelper]
    split
    case isTrue th =>
      -- Simplify ol to say that arr = output
      simp[<- th, <- arr.val_is_size, arr_take_size arr.val] at ol
      -- Becase the base case just returns output, we're good
      simp[*]
    case isFalse th => 
      exact traverseHelper_id arr $ by
        simp[*, Seq.seq, SArray.push]
        -- Prove that the arrays are equal because their lists are equal
        exact Array.ext' $ by
          have lt := (Nat.lt_or_eq_of_le i_le_size).resolve_right (th ∘ Eq.symm)
          rw[<- arr.val_is_size, Array.size_eq_length_toList] at lt
          simp[*, List.take_add_one, List.getElem?_eq_getElem lt]
          rfl

instance : LawfulTraversable (SArray size) where
  id_traverse arr := by
    simp[Traversable.traverse, SArray.traverse, Pure.pure, EmptyCollection.emptyCollection]
    -- This sorry seemms like it should be easy to prove
    exact traverseHelper_id arr (by simp[*]; sorry)
  comp_traverse := by
    simp[Traversable.traverse, SArray.traverse, Functor.map, Functor.Comp.mk, *]
    sorry
  traverse_eq_map_id := sorry
  naturality := sorry

instance : GetElem (SArray size α) (Fin size) α (fun _ _ => true) where
  getElem arr i _ := arr.val[i]'(by simp[arr.val_is_size])

def SArray.set (i: Fin size) (a : α) : SArray size α → SArray size α
  | {val, val_is_size} =>
    let val := val.set i a (by simp[val_is_size])
    {val, val_is_size := (by simp[val, val_is_size])}

-- Dependent types are neat
def tryingSize (size : Nat) (arr: Array α) : Option $ SArray size α :=
  if proof: arr.size = size then some ⟨arr, proof⟩ else none

def SArray.of (arr: Array α) : SArray arr.size α := ⟨arr, rfl⟩

def SArray.mapFinIdx (arr : SArray size α) (f : Fin size → α → β) : SArray size β :=
  { val := arr.val.mapFinIdx fun n a => f (arr.val_is_size ▸ n) a
  , val_is_size := by simp[Array.size_mapFinIdx, arr.val_is_size]
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

structure AnyPos: Type where
  x : Int
  y : Int
deriving BEq, Hashable, Nonempty

def Pos.forget (pos: Pos size): AnyPos := {x := pos.x.val, y := pos.y.val}

structure Dir where
  dx : Int
  dy : Int
deriving BEq, Hashable, Nonempty
instance : ToString Dir where
  toString | {dx, dy} => s!"\{dx:={dx}, dy:={dy}}"

instance : Neg Dir where
  neg dir := ⟨-dir.dx, -dir.dy⟩

instance : HMul Dir Int Dir where
  hMul dir a := ⟨dir.dx * a, dir.dy * a⟩

instance : HMul Dir Nat Dir where
  hMul dir a := ⟨dir.dx * a, dir.dy * a⟩

instance : HAdd Dir Nat Dir where
  hAdd dir a := ⟨dir.dx + a, dir.dy + a⟩

instance : Add Dir where
  add a b := ⟨a.dx + b.dx, a.dy + b.dy⟩

instance : HSub (Pos size) (Pos size) Dir where
  hSub l r := ⟨l.x - r.x, l.y - r.y⟩

instance : HAdd (Pos size) Dir (Option $ Pos size) where
  hAdd l r :=
    let x := l.x + r.dx
    let y := l.y + r.dy
    Pos.mk <$> x.asFin <*> y.asFin

instance : HAdd AnyPos Dir AnyPos where
  hAdd l r :=
    let x := l.x + r.dx
    let y := l.y + r.dy
    {x, y}

-- Grid will likely be useful again
structure Grid (size : Size) (α : Type) where
  rows : SArray size.y (SArray size.x α)
  focus : Pos size

instance [ToString α]: ToString (Grid size α) where
  toString g := g.rows.val.foldl (· ++ toString · ++ "\n") ""

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

def Grid.get (grid: Grid size α) (pos: Pos size) : α :=
  grid.rows[pos.y][pos.x]

-- Grid is a Comonad, but Lean doesn't have that as a class yet
def Grid.extract (grid: Grid size α) : α := grid.get grid.focus

def Grid.extend (f : Grid size α → β) (grid: Grid size α) : Grid size β :=
  grid.mapFinIdx fun pos _ => f {rows := grid.rows, focus := pos}

def Grid.setFocus (g: Grid size α) (focus: Pos size) : Grid size α :=
  {g with focus}

def Grid.step : Grid size α → Dir → Option (Grid size α)
  | grid@{focus := {x, y}, ..}, {dx, dy} => do
    some {grid with focus := ⟨<- x + dx, <- y + dy⟩}

def Grid.fold (f: β → α → β) (init: β) (grid : Grid size α) : β :=
  grid.rows.val.foldl (fun accum cols => cols.val.foldl f accum) init

def Grid.foldr (f: α → β → β) (init: β) (grid : Grid size α) : β :=
  grid.fold (flip f) init

def Grid.sum (grid : Grid size Nat) : Nat := grid.fold HAdd.hAdd 0

def Grid.across (f : β → α → β) (initial : β) (grid: Grid size α) (dir: Dir) : Nat → Option β
  | 0 => some $ f initial grid.extract
  | n + 1 => do
    let stepped <- grid.step dir
    let accum <- stepped.across f initial dir n
    some $ f accum grid.extract

def Grid.setAt (pos: Pos size) (a: α) : Grid size α → Grid size α
  | {rows, focus} =>
    { rows := rows.modify pos.y (·.set pos.x a), focus }

def Grid.set (a: α) (g: Grid size α): Grid size α := g.setAt g.focus a
