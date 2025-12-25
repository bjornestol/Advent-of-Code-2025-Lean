import Aoc2025.Basic
import Aoc2025.Map
import Std.Data.TreeMap

def Array.findAllIdx (p : α → Bool) (arr : Array α) (n : Nat := 0) : List (Fin arr.size) :=
  if ns : n ≥ arr.size then
    []
  else
    have : n < arr.size := by omega
    if p arr[n] then
      ⟨n, this⟩ :: arr.findAllIdx p (n+1)
    else
      arr.findAllIdx p (n+1)

namespace Day7

def neighbors (i : Fin n) : List (Fin n) :=
  Fin.foldr n (λ x xs ↦ if x.val = i.val - 1 ∨ x.val = i.val + 1 then x :: xs else xs) []

def incMap (i : Fin n) : List (Fin n) → Std.TreeMap (Fin n) Nat → Std.TreeMap (Fin n) Nat
| [], s => s
| x :: xs, s =>
  incMap i xs <| s.insert x ((s.getD x 0) + (s.getD i 0))

def updateMap : List (Fin n) → Std.TreeMap (Fin n) Nat → Std.TreeMap (Fin n) Nat
| [], s => s
| x :: xs, s =>
  let nbhs := neighbors x
  updateMap xs <| (incMap x nbhs s).insert x 0

def splitBeam (m : Map Char) (n : Nat) : StateM (Std.TreeMap (Fin m.cols) Nat) Nat := 
  if nb : n ≥ m.rows then
    return 0
  else
    have : n < m.inner.size := Index.fst_fin ⟨n, by omega⟩
    let line := m.inner[n]
    have linen : line = m.inner[n] := by rfl
    have linesize : line.size = m.cols := by
      rw [← m.colsCorrect m.inner[n], linen]
      exact Array.getElem_mem this
    if nn : n = 0 then do
      let start := line.findIdx (· = 'S')
      if h : start < line.size then
        have : start < m.cols := by
          rw [← m.colsCorrect m.inner[n]]
          · rw [← linen]
            exact h
          · exact Array.getElem_mem this
        let empty : Std.TreeMap (Fin m.cols) Nat := ∅
        set (empty.insert ⟨start, this⟩ 1)
      splitBeam m (n+1)
    else do
      have : List (Fin line.size) = List (Fin m.cols) := by
        rw [linesize]
      let splits : List (Fin m.cols) := cast this <| line.findAllIdx (· = '^')
      let state ← get
      let splits_filtered := splits.filter (λ i ↦ state.getD i 0 > 0)
      modify (updateMap splits_filtered)
      return splits_filtered.length + (← splitBeam m (n+1))

namespace Problem1

def solve (m : Map Char) : Nat :=
  (splitBeam m 0).run' ∅

end Problem1

namespace Problem2

def solve (m : Map Char) : Nat :=
  (splitBeam m 0).run ∅ |>.snd |>.foldr (λ _ v s ↦ v + s) 0

end Problem2

def problem1 (input : String) : Except ParseError String := do
  let map ← inputToMap input
  return (toString <| Problem1.solve map)

def problem2 (input : String) : Except ParseError String := do
  let map ← inputToMap input
  return (toString <| Problem2.solve map)

end Day7

def day7 : Day := ⟨7, Day7.problem1, Day7.problem2, "21", "40"⟩
