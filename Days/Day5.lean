import Utils

open Parser
open Std

def dbg [ToString α] (_: α) (f: Unit → β) : β :=
  f ()
  /- dbgTrace (toString a) f -/

abbrev Graph := SArray 100 $ List $ Fin 100

def Graph.empty : Graph := SArray.replicate []

def Graph.ofArray (arr: Array (Fin 100 × Fin 100)) : Graph :=
  arr.foldl (fun g (l, r) => g.modify l (r :: ·)) Graph.empty

structure Search where
  graph: Graph
  visiting: Fin 100
  visited: SArray 100 Bool

partial def visit'
  [Monad m]
  [MonadReader (List $ Fin 100) m]
  [MonadStateOf Search m]
  [Nonempty α]
  (recurse: Bool)
  (f: {m : Type -> Type} → [Monad m] → [MonadReader (List $ Fin 100) m] → Fin 100 → List α → m α)
  : m α := do
  let s@{visiting, graph, visited} <- get
  if visited[visiting] ∨ ¬recurse
    then f visiting []
    else do
      modify ({· with visited := visited.set visiting true : Search})
      let followers <- graph[visiting].mapM fun visiting => do
        modify ({· with visiting})
        ReaderT.run (visit' false f) $ visiting :: (<- read)
      f visiting followers

-- I wrote this assuming the orderings were transitive but turns out they're
-- not...
/- partial def visit' -/
/-   [Monad m] -/
/-   [MonadReader (List $ Fin 100) m] -/
/-   [MonadStateOf Search m] -/
/-   [Nonempty α] -/
/-   (f: {m : Type -> Type} → [Monad m] → [MonadReader (List $ Fin 100) m] → Fin 100 → List α → m α) -/
/-   : m α := do -/
/-   let s@{visiting, graph, visited} <- get -/
/-   if visited[visiting] -/
/-     then f visiting [] -/
/-     else do -/
/-       modify ({· with visited := visited.set visiting true : Search}) -/
/-       let followers <- graph[visiting].mapM fun visiting => do -/
/-         modify ({· with visiting}) -/
/-         ReaderT.run (visit' f) $ visiting :: (<- read) -/
/-       f visiting followers -/

def Search.visit
  [Nonempty α]
  (f: {m : Type -> Type} → [Monad m] → [MonadReader (List $ Fin 100) m] → Fin 100 → List α → m α)
  (s : Search)
  : α :=
  Id.run $ ReaderT.run (StateT.run' (visit' true f) s) [s.visiting]


/- partial def Search.follow (f: Search α → Search α) : Search α → Search α -/
/-   | s@{visiting, visited, graph} => -/
/-     if let .some result := visited[visiting] -/
/-       then s -/
/-       else -/
/-         let s := {s with visited := visited.set visiting (some $ f visiting) } -/
/-         let followers := graph.edges[visiting].map (β := Search α → Search α) -/
/-           fun visiting s => {s with visiting}.follow f -/
/-         followers.foldr (· ·) s -/

/- def Search.accumulate (f: Fin 100 → α) (accum: α → List α → α) : Search α → α -/
/-   | s@{visiting, visited, graph} => -/
/-     graph.edges[visiting].map fun i s => s.follow -/

/- def isOrderedCorrectly (g: Graph) (later: HashSet)  -/

namespace Day5


structure Update where
  unprinted: HashSet $ Fin 100
  allPages: HashSet $ Fin 100
  order: List $ Fin 100

def check
  [Monad m]
  [MonadReader (List $ Fin 100) m]
  (i: Fin 100)
  (rest: List $ Update → Bool)
  : m $ Update → Bool := do
  /- let path <- read -/
  pure fun update@{unprinted, allPages, order} =>
    if unprinted.contains i
      then false
      else
        let unprinted := if allPages.contains i
          then HashSet.ofList $ List.tail $ order.dropWhile (· != i)
          else unprinted
        (rest.map (· {update with unprinted})).and


structure Problem where
  graph: Graph
  orders: Array $ List $ Fin 100

def part1 : Problem → Nat
  | {graph, orders} => Array.sum $ orders.map fun order =>
    let alls := order.map fun visiting =>
      let update :=
        { unprinted := HashSet.empty
        , allPages := HashSet.ofList order
        , order := order
        }
      dbg s!"Running {visiting}" fun _ => {graph, visiting, visited := SArray.replicate false : Search}.visit check update
    if alls.all (· == true)
      then order[order.length / 2]!.val
      else 0

def parseFin [NeZero size] : AocParser $ Fin size :=
  Fin.ofNat' size <$> parseNat

def parsePair : AocParser $ Prod (Fin 100) (Fin 100) :=
  Prod.mk <$> parseFin <* char '|' <*> parseFin

def parseGraph : AocParser Graph := do
  let pairs <- sepEndBy Char.eol parsePair
  pure $ Graph.ofArray $ pairs.map Prod.swap

def parseUpgrade : AocParser $ List $ Fin 100 := do
  Array.toList <$> sepBy1 (char ',') parseFin
def parseUpgrades : AocParser $ Array $ List $ Fin 100 :=
  sepEndBy1 Char.eol parseUpgrade

def parser : AocParser Problem := do
  let graph <- parseGraph
  ignore Char.eol
  let orders <- parseUpgrades
  pure {graph, orders}

def sort (graph: Graph) (order : List $ Fin 100) : List $ Fin 100 :=
  order.mergeSort fun visiting b =>
    let update :=
      { unprinted := HashSet.ofList [b]
      , allPages := HashSet.ofList [visiting, b]
      , order := [visiting, b]
      }
    {graph, visiting, visited := SArray.replicate false : Search}.visit check update

def part2 : Problem → Nat
  | {graph, orders} => Array.sum $ orders.map fun order =>
    let alls := order.map fun visiting =>
      let update :=
        { unprinted := HashSet.empty
        , allPages := HashSet.ofList order
        , order := order
        }
      {graph, visiting, visited := SArray.replicate false : Search}.visit check update
    if alls.all (· == true)
      then 0
      else
        let order := dbg s!"Order: {order} to {sort graph order}" fun _ => sort graph order
        order[order.length / 2]!.val

def day: Day := {parser, part1, part2}
