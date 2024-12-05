import Mathlib.Control.Traversable.Basic

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
