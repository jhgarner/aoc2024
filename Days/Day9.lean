import Utils

open Parser Char ASCII

namespace Day9

structure DQueue (α: Type) where
  arr: Array α

instance [ToString α] : ToString (DQueue α) where
  toString | {arr} => s!"(arr={arr})"

def DQueue.push_back (a: α) : DQueue α → DQueue α
  | {arr} => ⟨arr.push a⟩

def DQueue.push_front (a: α) : DQueue α → DQueue α
  | {arr} => ⟨arr.insertIdx 0 a⟩

def DQueue.pop_back? : DQueue α → Option (α × DQueue α)
  | {arr} => do
    pure (<- arr.get? $ arr.size - 1, ⟨arr.pop.toSubarray⟩)

def DQueue.pop_front? : DQueue α → Option (α × DQueue α)
  | {arr} => if p:arr.size > 0
    then .some $ (arr[0], ⟨arr.eraseIdx 0⟩)
    else .none

def DQueue.of (ls: List α) : DQueue α :=
  ls.foldl (fun dq l => dq.push_back l) {arr := #[]}

structure File where
  name: Nat
  size: Nat

instance : ToString File where
  toString | {name, size} => s!"(name={name},size={size})"

inductive Section where
  | file: File → Section
  | empty: Nat → Section

instance : ToString Section where
  toString
  | .file f => toString f
  | .empty n => toString n

structure Computer where
  blocks: DQueue Section

instance : ToString (Computer) where
  toString | {blocks} => s!"(blocks={blocks})"

partial def checksum (i: Nat) (total: Nat) (c: Computer) : Nat :=
  match c.blocks.pop_front? with
  | .some (.file {name, size}, blocks) =>
    let thisPart := name * size * (2*i + size - 1) / 2
    checksum (i+size) (total+thisPart) {blocks}
  | .some (.empty space, blocks) =>
    match blocks.pop_back? with
    | .some (.file {name, size}, blocks) =>
        let toMove := space.min size
        let thisPart := name * toMove * (2*i + toMove - 1) / 2
        let blocks := if size > space
          then blocks.push_back $ .file {name, size := size - space}
          else blocks
        let blocks := if space > size
          then blocks.push_front $ .empty $ space - size
          else blocks
        checksum (i+toMove) (total+thisPart) {blocks}
    | .some (.empty _, blocks) =>
      checksum i total {blocks := blocks.push_front $ .empty space}
    | .none => total
  | .none => total

def part1 (c: Computer) : Nat := checksum 0 0 c

def handleItem : Nat × Nat → Section
  | (i, size) => if i % 2 == 0
    then .file {name := i / 2, size}
    else .empty size

def parser : AocParser Computer := do
  let nats <- Array.map (String.toNat! ∘ Char.toString) <$> takeMany numeric
  pure $ {blocks := DQueue.of $ nats.toList.enum.map handleItem}

def findFit (size: Nat) (fs: DQueue Section) (i: Nat) {p: i ≤ fs.arr.size} : Option (File × DQueue Section) :=
  match i with
  | 0 => .none
  | i + 1 =>
    if let .file f := fs.arr[i]
      then if f.size <= size ∧ f.name ≠ 0
        then .some (f, ⟨fs.arr.set i $ .file {name := 0, size := f.size}⟩)
        else findFit size fs i (p := by exact Nat.le_of_succ_le p)
      else findFit size fs i (p := by exact Nat.le_of_succ_le p)

partial def checksum2 (i: Nat) (total: Nat) (c: Computer) : Nat :=
  match c.blocks.pop_front? with
  | .some (.file {name, size}, blocks) =>
    let thisPart := name * size * (2*i + size - 1) / 2
    checksum2 (i+size) (total+thisPart) {blocks}
  | .some (.empty space, blocks) =>
    match findFit space blocks blocks.arr.size (p := by simp) with
    | .some ({name, size}, blocks) =>
        let thisPart := name * size * (2*i + size - 1) / 2
        let blocks := if space > size
          then blocks.push_front $ .empty $ space - size
          else blocks
        checksum2 (i+size) (total+thisPart) {blocks}
    | .none => checksum2 (i+space) (total) {blocks}
  | .none => total

def part2 (c: Computer) : Nat := checksum2 0 0 c

def day: Day := {parser, part1, part2}

