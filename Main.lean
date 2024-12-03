import Utils

import Days

def runDay (day : Day) (input : String) : IO Unit := do
  let problem <- parse day.parser input
  let answer := day.part1 problem
  let answer2 := day.part2 problem
  IO.println answer
  IO.println answer2


def main : List String → IO UInt32
  | [dayString, file] => do
    if let .some (day + 1) := dayString.toNat? then
      if h:day < 25 then
        let input <- IO.FS.readFile $ System.mkFilePath ["inputs", s!"day{dayString}", file]
        runDay days[day] input
        pure 0
      else
        IO.eprintln s!"Invalid day {dayString}"
        pure 1
    else
        IO.eprintln s!"Invalid day {dayString}"
        pure 1
  | _ => pure 1
