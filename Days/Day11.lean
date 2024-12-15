import Utils

open Parser
open Std

namespace Day11

structure Rock where
  n: Nat
  days: Nat
deriving BEq, Hashable


abbrev Cache := HashMap Rock Nat

def step (n: Nat) : List Nat :=
 if n = 0
  then [1]
  else
    let asStr := toString n
    let len := asStr.length
    let halved := len / 2
    if len % 2 = 0
      then [asStr.take halved, asStr.drop halved].map (·.toNat!)
      else [n * 2024]

def iter (ns: List Nat): Nat → List Nat
| 0 => ns
| n + 1 => iter (ns.flatMap step) n

def part1 (ns: Array Nat): Nat := (iter ns.toList 25).length

def parser : AocParser $ Array Nat := sepEndBy1 whitespace parseNat

def iterCached (n: Nat): Nat → StateM Cache Nat
| 0 => pure 1
| days + 1 => do
  let cache <- get
  let got <- if let .some got := cache.get? {n, days := days+1}
    then pure got
    else
      if n = 0
        then iterCached 1 days
        else
          let asStr := toString n
          let len := asStr.length
          let halved := len / 2
          if len % 2 = 0
            then do
              let rec <- (([asStr.take halved, asStr.drop halved].map (·.toNat!)).traverse (iterCached · days))
              pure rec.sum
            else iterCached (n * 2024) days
  modify (·.insert {n, days := days+1} got)
  pure got

def part2 (ns: Array Nat): Nat :=
  ((ns.toList.traverse (iterCached · 75)).run' {}).sum


def day: Day := {parser, part1, part2}

