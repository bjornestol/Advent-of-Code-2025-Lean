import Aoc2025.Basic

structure Map (α : Type) where
  inner : Array (Array α)
  rows : Nat
  cols : Nat
  rowsCorrect : inner.size = rows
  colsCorrect : ∀ x : Array α, x ∈ inner → x.size = cols
  nonEmpty : 0 < rows ∧ 0 < cols
deriving Repr

instance [BEq α] : BEq (Map α) where
  beq m1 m2 := m1.inner == m2.inner

namespace Map

def same_size (m1 : Map α) (m2 : Map α) : Prop :=
  m1.rows = m2.rows ∧ m1.cols = m2.cols

theorem ss_rfl (m : Map α) : m.same_size m := by
  simp [Map.same_size]

def all_cols_same_size : List (Array α) → Nat → Bool
  | [], _ => true
  | x :: xs, n =>
    x.size = n ∧ all_cols_same_size xs n

def all_cols_same_size_arr (arr :Array (Array α)) (n : Nat) : Bool :=
  all_cols_same_size (arr.toList) n

theorem colscheck (xs : List (Array α)) (cols : Nat) : all_cols_same_size xs cols = true → ∀ x : Array α, x ∈ xs → x.size = cols := by
  induction xs
  case nil =>
    intro h x xins
    contradiction
  case cons x' xs' ih =>
    intro h y yins
    simp [all_cols_same_size] at h
    have : (y = x') ∨ y ∈ xs' := by
      exact List.eq_or_mem_of_mem_cons yins
    rcases this with l | r
    · rw [← l] at h
      exact h.left
    · exact ih h.right y r

theorem colscheck_arr (xs : Array (Array α)) (cols : Nat) : all_cols_same_size_arr xs cols = true → ∀ x : Array α, x ∈ xs → x.size = cols := by
  intro h x xins
  simp [all_cols_same_size_arr] at h
  have : x ∈ xs.toList := by
    exact xins.val
  exact colscheck xs.toList cols h x this

end Map

def inputToMap (input : String) : Except ParseError (Map Char) :=
  let map := (((input.splitLines).map String.toList).map List.toArray).toArray
  let rows := map.size
  if row_nonempty : rows = 0 then
    throw ⟨s!"Input is empty!"⟩
  else
    let cols := (map[0]).size
    if col_nonempty : cols = 0 then 
      throw ⟨s!"Input is empty"⟩
    else if h : Map.all_cols_same_size_arr map cols then 
      pure ⟨map, rows, cols, rfl, Map.colscheck_arr map cols h, by omega⟩
    else 
      throw ⟨s!"Input-columns have differing width"⟩

def Index (map : Map α) := Fin map.rows × Fin map.cols

instance : BEq (Index map) where
  beq ind1 ind2 := ind1.fst == ind2.fst ∧ ind1.snd == ind2.snd

namespace Index

def toIndex (i : Fin map.rows) (j : Fin map.cols) : Index map :=
  (i, j)

def toNewMap (i : Index m1) (m2 : Map Char) (h : m1.same_size m2) : Index m2 :=
  have r : m1.rows = m2.rows := h.left
  have c : m1.cols = m2.cols := h.right
  (i.fst.cast r, i.snd.cast c)

theorem fst_fin {map : Map α} (ind : Fin map.rows) : ind < map.inner.size := by
  rw [map.rowsCorrect]
  exact ind.isLt

theorem fst_ind (ind : Index map) : ind.fst < map.inner.size := by
  exact fst_fin ind.fst

theorem snd_ind (ind : Index map) : ind.snd < (map.inner[ind.fst]'(fst_ind ind) |>.size) := by
  have := fst_ind ind
  rw [map.colsCorrect map.inner[ind.fst]]
  · omega
  · exact Array.mem_of_getElem rfl

end Index

structure Neighbors α where
  map : Map α
  loc : Index map
  inner : List (Index map)

namespace Neighbors

def asAboveSoBelow (i : Fin n) (f : Fin n) (xs : List (Fin n)) : List (Fin n) :=
  if (f.val = i ∨ f.val - 1 = i ∨ f.val + 1 = i) then
    f :: xs
  else
    xs

def nbhd_interval (i : Fin n) : List (Fin n) :=
  Fin.foldr n (asAboveSoBelow i) []

def cartesian : List (Fin m.rows) → List (Fin m.cols) → List (Index m)
  | [], _ => []
  | x :: xs, ys =>
    (ys.map (λ y ↦ Index.toIndex x y)) ++ cartesian xs ys

end Neighbors

def Index.neighbors (ind : @Index α m) : Neighbors α :=
  let i_nbhd := Neighbors.nbhd_interval ind.fst
  let j_nbhd := Neighbors.nbhd_interval ind.snd
  ⟨m, ind, Neighbors.cartesian i_nbhd j_nbhd |>.filter (· != ind)⟩
