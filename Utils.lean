import Parser

open Parser Char ASCII

partial def readAll (stream : IO.FS.Stream) (accum : String) : IO String := do
  let line <- stream.getLine
  if line == "" then return accum
  readAll stream (accum ++ line)

