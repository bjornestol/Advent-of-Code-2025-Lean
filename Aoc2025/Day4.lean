import Aoc2025.Basic

def all_cols_same_size : List (List α) → Nat → Bool
  | [], _ => true
  | x :: xs, n =>
    x.length = n ∧ all_cols_same_size xs n

theorem colscheck (xs : List (List α)) (cols : Nat) : all_cols_same_size xs cols = true → ∀ x : List α, x ∈ xs → x.length = cols := by
  induction xs
  case nil =>
    intro h x xins
    contradiction
  case cons x' xs' ih =>
    intro h y yins
    simp [all_cols_same_size] at h
    have h' : all_cols_same_size xs' cols = true := by
      exact h.right
    


structure MatrixableListOfLists α where
  ll : List (List α)
  rows : Nat
  cols : Nat
  rowsCorrect : ll.length = rows
  colscorrect : ∀ x : List α, x ∈ ll → x.length = cols

namespace Day4

namespace Problem1

end Problem1

namespace Problem2

end Problem2

def problem1 (input : String) : Except ParseError String :=
  return "0"

def problem2 (input : String) : Except ParseError String :=
  return "0"

end Day4

def day4 : Day := ⟨4, Day4.problem1, Day4.problem2, "0", "0"⟩
