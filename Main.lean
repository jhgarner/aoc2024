import Days.Day2

def main : IO Unit := do
  let problem <- readInput
  let answer := part1 problem
  let answer2 := part2 problem
  IO.println answer
  IO.println answer2

