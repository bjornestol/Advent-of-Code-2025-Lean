import Aoc2025.Basic
import Aoc2025.Map

def Index.isRoll (ind : @Index Char map) : Nat :=
  have := Index.fst_ind ind
  have := Index.snd_ind ind
  match map.inner[ind.fst][ind.snd] with
  | '@' => 1
  | _ => 0

def Neighbors.rolls (nbhs : Neighbors Char) : Nat :=
  match h :  nbhs.inner with
  | [] => 0
  | x :: xs =>
    have : xs.length < nbhs.inner.length := by
      rw [h]
      exact Nat.lt_add_one xs.length
    x.isRoll + {nbhs with inner := xs}.rolls
  termination_by nbhs.inner.length

namespace Day4

-- This is not imperative. I promise. Super functional. No mutation here, no sir.
def accessibleRolls (map : Map Char) : List (Index map) := Id.run do
  let mut accRolls := []
  for ih : i in [0 : map.rows] do
    for jh : j in [0 : map.cols] do
      let ind : Index map := (⟨i, Membership.get_elem_helper ih rfl⟩, ⟨j, Membership.get_elem_helper jh rfl⟩)
      if ind.isRoll = 1 ∧ (ind.neighbors.rolls < 4) then
        accRolls := ind :: accRolls
  return accRolls

namespace Problem1

def solve (map: Map Char) : Nat :=
  accessibleRolls map |>.length

end Problem1

namespace Problem2

theorem Array.all_indices_all_values (xs : Array α) (p : α → Prop) : (∀ i : Fin xs.size, p xs[i]) ↔ (∀ x, x ∈ xs → p x) := by
  constructor
  · intro fai x xins
    have := Array.mem_iff_getElem.mp xins
    rcases this with ⟨i, h, xeq⟩
    let i_fin : Fin xs.size := ⟨i, h⟩
    have := fai i_fin
    rw [← xeq]
    exact this
  · intro fax i
    have := Array.mem_of_getElem (a := xs[i]) rfl
    exact fax xs[i] this

theorem Array.set_retains_property 
    (xs : Array α) 
    (p : α → Prop) 
    (h : ∀ x, x ∈ xs → p x) 
    (i : Nat)
    (hi : i < xs.size)
    (v : α)
    (hv : p v)
  : ∀ x, x ∈ xs.set i v → p x := by
    have indices := (Array.all_indices_all_values xs p).mpr h
    intro x xins
    have := Array.mem_iff_getElem.mp xins
    rcases this with ⟨j, hj, xeq⟩
    have : i = j ∨ i ≠ j := Decidable.em _
    rcases this with iej | inej
    · conv at xeq in j =>
        rw [←iej]
      have : v = x := by
        rw [Array.getElem_set_self hi] at xeq
        exact xeq
      rw [← this]
      exact hv
    · have hjj : j < xs.size := by
        rw [Array.size_set hi] at hj
        exact hj
      have : xs[j] = x := by
        rw [Array.getElem_set_ne hi hjj inej] at xeq
        exact xeq
      rw [← this]
      exact indices ⟨j, hjj⟩

def removeRoll (ind : @Index Char map) : Map Char :=
  have fig := Index.fst_ind ind
  have sig := Index.snd_ind ind
  let newInnerArray := map.inner[ind.fst].set ind.snd '.'
  let newArray := map.inner.set ind.fst newInnerArray
  have nias : newInnerArray.size = map.cols := by
    rw [Array.size_set]
    apply map.colsCorrect map.inner[ind.fst]
    exact Array.mem_of_getElem rfl
  have nas : newArray.size = map.rows := by
    rw [← map.rowsCorrect]
    exact Array.size_set fig
  have cols : ∀ x : Array Char, x ∈ newArray → x.size = map.cols := by
    apply Array.set_retains_property
    · exact map.colsCorrect
    · exact nias
  ⟨newArray, map.rows, map.cols, nas, cols, map.nonEmpty⟩

theorem size_removeRoll (ind : Index map) : map.same_size (removeRoll ind) := by
  simp [Map.same_size, removeRoll]

def rolls (map : Map Char) : Nat :=
  let arr := map.inner
  arr.map (λ xs ↦ xs.count '@') |>.sum

def removeRolls : List (Index map) → (currMap : Map Char) → map.same_size currMap → Map Char
  | [], currMap, h => currMap
  | x :: xs, currMap, h =>
    let ind := x.toNewMap currMap h
    let newMap := removeRoll ind
    have : currMap.same_size newMap := by
      exact size_removeRoll ind
    have : map.same_size newMap := by
      simp [Map.same_size] at *
      trivial
    removeRolls xs newMap this

partial def removeAllRolls (map : Map Char) : Nat :=
  let rolls := accessibleRolls map
  if rolls.length = 0 then
    0
  else
    let newMap := removeRolls rolls map (Map.ss_rfl map)
    rolls.length + removeAllRolls newMap

end Problem2

def problem1 (input : String) : Except ParseError String := do
  let mml ← inputToMap input
  let ans := Problem1.solve mml
  return (toString ans)

def problem2 (input : String) : Except ParseError String := do
  let map ← inputToMap input
  let ans := Problem2.removeAllRolls map
  return (toString ans)

end Day4

def day4 : Day := ⟨4, Day4.problem1, Day4.problem2, "13", "43"⟩
