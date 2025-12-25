import Aoc2025.Basic
import Std.Data.TreeSet

namespace Day8

structure Point where
  X : Nat
  Y : Nat
  Z : Nat
deriving Repr

structure PairOfPoints where
  p : Point
  q : Point
  dist : Nat
deriving Repr

-- Ironisk nok bedre å gange ut selv? Ellers får man problemer med om x - y er en Nat eller ei. Men dette burde funke.
def absDist (x : Nat) (y : Nat) : Nat :=
  x^2 + y^2 - 2*x*y

def Point.sqDist (p : Point) (q : Point) : Nat :=
  (absDist p.X q.X) + (absDist p.Y q.Y) + (absDist p.Z q.Z)

def inputToPoints : (List String) → Except ParseError (List Point)
| [] => pure []
| l :: ls => do
  let xyz := l.splitOn ","
  if h : xyz.length = 3 then
    let x ← xyz[0].toNat?.toExcept ⟨s!"Not a number: {xyz[0]}"⟩
    let y ← xyz[1].toNat?.toExcept ⟨s!"Not a number: {xyz[1]}"⟩
    let z ← xyz[2].toNat?.toExcept ⟨s!"Not a number: {xyz[2]}"⟩
    return ({ X := x, Y := y, Z := z : Point} :: (← inputToPoints ls))
  else
    throw ⟨s!"Not three numbers in line {l}"⟩

def pointToPairs (p : Point) : List Point → List PairOfPoints
| [] => []
| x :: xs =>
  let pair : PairOfPoints := ⟨ p, x, p.sqDist x ⟩
  pair :: pointToPairs p xs

def pointsToPairs : List Point → List PairOfPoints
| [] => []
| x :: xs =>
  let ptp := pointToPairs x xs
  ptp ++ pointsToPairs xs

def Point.cmp (p : Point) (q : Point) : Ordering :=
  if Ord.compare p.X q.X = .eq then
    if Ord.compare p.Y q.Y = .eq then
      Ord.compare p.Z q.Z
    else
      Ord.compare p.Y q.Y
  else
    Ord.compare p.X q.X

structure Connections where
  connections : Std.TreeMap Point Nat Point.cmp
  points : Std.TreeMap Nat (List Point)
  first_avail : Nat
deriving Repr

def updateMaps (p : Point) (q : Point) (conn : Connections) : Connections :=
  if h : conn.connections.contains p then
    let pVal := conn.connections.get p h
    let qVal := conn.connections.getD q conn.first_avail
    if pVal = qVal then
      conn
    else
      let qConn := conn.points.getD qVal [q]
      let newConn := conn.connections.insertMany (qConn.map (λ qv ↦ (qv, pVal)))
      let newPts := (conn.points.erase qVal).modify pVal (qConn ++ ·)
      ⟨newConn, newPts, conn.first_avail⟩
  else
    if h : conn.connections.contains q then
      let qVal := conn.connections.get q h
      let newConn := conn.connections.insert p qVal
      let newPts := conn.points.modify qVal (p :: ·)
      ⟨newConn, newPts, conn.first_avail⟩
    else
      let newConn := (conn.connections.insert p conn.first_avail).insert q conn.first_avail
      let newPts := conn.points.insert conn.first_avail [p, q]
      ⟨newConn, newPts, conn.first_avail + 1⟩

namespace Problem1

def solve_aux (conn : Connections) : List PairOfPoints → Connections
| [] => conn
| x :: xs =>
  solve_aux (updateMaps x.p x.q conn) xs

def solve (lp : List Point) (n : Nat) : Nat :=
  let pp := pointsToPairs lp
  let shortests := (pp.mergeSort (·.dist ≤ ·.dist)).take n
  let connections := solve_aux ⟨∅, ∅, 0⟩ shortests
  let sorted := connections.points.toList.mergeSort (·.snd.length ≥ ·.snd.length) |>.take 3
  sorted.foldr (·.snd.length * ·) 1

end Problem1

namespace Problem2

def solve_aux (conn : Connections) (n : Nat) : List PairOfPoints → Nat
| [] => 0
| x :: xs =>
  let newConn := updateMaps x.p x.q conn
  if h : newConn.points.toList.length = 1 then
    let l := newConn.points.toList[0].snd.length
    if l = n then
      x.p.X * x.q.X
    else
      solve_aux newConn n xs
  else
    solve_aux newConn n xs

def solve (lp : List Point) : Nat :=
  let n := lp.length
  let pp := (pointsToPairs lp).mergeSort (·.dist ≤ ·.dist)
  solve_aux ⟨∅, ∅, 0⟩ n pp

end Problem2

def problem1 (input : String) : Except ParseError String := do
  let n := if input.startsWith "162" then 10 else 1000
  let pts ← inputToPoints (input.splitLines)
  return (toString (Problem1.solve pts n))

def problem2 (input : String) : Except ParseError String := do
  let pts ← inputToPoints (input.splitLines)
  return (toString (Problem2.solve pts))

end Day8

def day8 : Day := ⟨8, Day8.problem1, Day8.problem2, "40", "25272"⟩
