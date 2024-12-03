import Parser

export Parser.Char.ASCII (parseNat whitespace)
export Parser.Char (char)

def Array.sum [HAdd α α α] [OfNat α 0] (arr : Array α) : α :=
  arr.foldl HAdd.hAdd 0

def Array.clean (arr : Array $ Option α) : Array α :=
  arr.flatMap (·.elim #[] (#[·]))


abbrev AocParser α := SimpleParser Substring Char α

structure Day where
  Repr : Type := Unit
  parser : AocParser Repr := Parser.throwUnexpected
  part1 : Repr → Nat := Function.const Repr 0
  part2 : Repr → Nat := Function.const Repr 0

  def ignore [Functor f] (m : f a) : f Unit := Functor.mapConst () m

partial def readAll (stream : IO.FS.Stream) (accum : String) : IO String := do
  let line <- stream.getLine
  if line == "" then return accum
  readAll stream (accum ++ line)

def parse (parser : AocParser α) (input : String) : IO α := do
  match Parser.run parser input with
    | .ok _ result => pure result
    | .error _ error => do
      IO.eprintln error
      throw $ IO.userError "test"
