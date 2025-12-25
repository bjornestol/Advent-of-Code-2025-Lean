import Aoc2025.Basic

namespace Day9

structure Point where
  X : Nat
  Y : Nat

structure Edge where
  curr : Point
  next : Point

structure PairOfEdges where
  p : Edge
  q : Edge
  area : Nat

def abs (x : Nat) (y : Nat) : Nat :=
  if x ≥ y then
    x - y
  else
    y - x

def Edge.area (p : Edge) (q : Edge) : Nat :=
  (1 + abs p.curr.X q.curr.X) * (1 + abs p.curr.Y q.curr.Y)

def lineToPoint (line : String) : Except ParseError Point :=
  let xy := line.splitOn ","
  if h : xy.length = 2 then do
    let x ← xy[0].toNat?.toExcept ⟨s!"Not a number: {xy[0]}"⟩
    let y ← xy[1].toNat?.toExcept ⟨s!"Not a number: {xy[1]}"⟩
    return ⟨x, y⟩
  else
    throw ⟨s!"Not two comma-separated numbers: {line}"⟩

def inputToPoints_aux (start : Point) : List String → Except ParseError (List Edge)
| [] => pure []
| [last] => do
  let lastPt ← lineToPoint last
  return [⟨lastPt, start⟩]
| curr :: next :: rest => do
  let currPt ← lineToPoint curr
  let nextPt ← lineToPoint next
  return ⟨currPt, nextPt⟩ :: (← inputToPoints_aux start (next :: rest))

def inputToPoints (ls : List String) : Except ParseError (List Edge) := do
  if h : ls.length < 2 then
    throw ⟨s!"Need at least two points for a polygon"⟩
  else
    match ls with 
    | [x] => by simp at h
    | x :: y :: xs =>
      let xp ← lineToPoint x
      let yp ← lineToPoint y
      return ⟨xp, yp⟩ :: (← inputToPoints_aux xp (y :: xs))


def edgeToPairs (p : Edge) : List Edge → List PairOfEdges
| [] => []
| x :: xs =>
  let pair : PairOfEdges := ⟨ p, x, p.area x ⟩
  pair :: edgeToPairs p xs

def edgesToPairs : List Edge → List PairOfEdges
| [] => []
| x :: xs =>
  let ptp := edgeToPairs x xs
  ptp ++ edgesToPairs xs

namespace Problem1

def solve (lp : List Edge) : Nat :=
  let pps := (edgesToPairs lp).map (·.area) |>.max?
  match pps with
  | some n => n
  | none => 0

end Problem1

namespace Problem2

def checkInside (p : Edge) (q : Edge) : Bool :=
  if p.curr.X < q.curr.X ∧ p.curr.Y < q.curr.Y then
    p.curr.Y ≥ p.next.Y
  else if p.curr.X > q.curr.X ∧ p.curr.Y < q.curr.Y then
    p.curr.X ≤ p.next.X
  else if p.curr.X > q.curr.X ∧ p.curr.Y > q.curr.Y then
    p.curr.Y ≤ p.next.Y
  else if p.curr.X < q.curr.X ∧ p.curr.Y > q.curr.Y then
    p.curr.X ≥ p.next.X
  else
    true

def insideBox (pp : PairOfEdges) : Bool :=
  (checkInside pp.p pp.q) ∧ (checkInside pp.q pp.p)

def minmax (n : Nat) (m : Nat) : Nat × Nat :=
  if n > m then
    (m, n)
  else
    (n, m)

def edgeCrossing (sq : PairOfEdges) (e : Edge) : Bool :=
  let (minY_edge, maxY_edge) := minmax e.curr.Y e.next.Y
  let (minY_corner, maxY_corner) := minmax sq.p.curr.Y sq.q.curr.Y
  let (minX_edge, maxX_edge) := minmax e.curr.X e.next.X
  let (minX_corner, maxX_corner) := minmax sq.p.curr.X sq.q.curr.X
  if e.curr.X = e.next.X then
    minX_corner < e.curr.X ∧ e.curr.X < maxX_corner ∧ maxY_edge > minY_corner ∧ maxY_corner > minY_edge
  else
    minY_corner < e.curr.Y ∧ e.curr.Y < maxY_corner ∧ maxX_edge > minX_corner ∧ maxX_corner > minX_edge

def largestLegal (lp : List Edge) : List PairOfEdges → Nat
| [] => 0
| pp :: ps =>
  if lp.any (edgeCrossing pp) then
    largestLegal lp ps
  else
    pp.area

def solve (lp : List Edge) : Nat :=
  let pps := (edgesToPairs lp).filter insideBox |>.mergeSort (·.area ≥ ·.area)
  largestLegal lp pps

end Problem2

def problem1 (input : String) : Except ParseError String := do
  let ptlist ← inputToPoints input.splitLines
  return (toString <| Problem1.solve ptlist)

def problem2 (input : String) : Except ParseError String := do
  let ptlist ← inputToPoints input.splitLines
  return (toString <| Problem2.solve ptlist)

end Day9

def day9 : Day := ⟨9, Day9.problem1, Day9.problem2, "50", "24"⟩
