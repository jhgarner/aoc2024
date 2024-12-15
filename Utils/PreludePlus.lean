import Mathlib.Control.Traversable.Basic
import Mathlib.Algebra.Group.Defs
open Std

def Option.keepIf (p: α → Bool) (opt: Option α): Option α :=
  opt.bind fun a => if p a then .some a else .none

def List.mapSplit (p: α → Sum β μ): List α → List β × List μ
| [] => ([], [])
| a::as =>
  let (ls, rs) := as.mapSplit p
  match p a with
  | .inl l => (l::ls, rs)
  | .inr r => (ls, r::rs)

def List.mapOption (p: α → Option β): List α → List β
| [] => []
| a::as =>
  let rest := as.mapOption p
  if let .some b := p a then b::rest else rest

def List.catOption: List (Option α) → List α := List.mapOption id

instance [Hashable α] [BEq α] [ToString α] : ToString (HashSet α) where
  toString := toString ∘ HashSet.toList

instance [Hashable α] [BEq α] [ToString α] [ToString β] : ToString (HashMap α β) where
  toString := toString ∘ HashMap.toList

def Array.sum [HAdd α α α] [OfNat α 0] (arr : Array α) : α :=
  arr.foldl HAdd.hAdd 0

def Array.clean (arr : Array $ Option α) : Array α :=
  arr.flatMap (·.elim #[] (#[·]))

-- Why don't they implement Traversable or Functor for Array?
instance : Traversable Array where
  map := Array.map
  traverse f arr := Array.mk <$> arr.toList.traverse f

-- Fin utilities
def Int.asFin (i : Int) : Option $ Fin n :=
  let iAsNat := i.natAbs
  if h:i >= 0 ∧ iAsNat < n then some $ Fin.mk iAsNat h.right else none

instance : HAdd (Fin n) Int (Option $ Fin n) where
  hAdd fin i := (i + fin.val).asFin
