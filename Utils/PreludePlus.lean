import Mathlib.Control.Traversable.Basic
open Std

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
