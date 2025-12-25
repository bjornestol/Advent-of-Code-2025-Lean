import Aoc2025.Basic

namespace Day5

structure Interval where
  first : Nat
  last : Nat
deriving Repr

def interval_le (intr1 : Interval) (intr2 : Interval) : Bool :=
  intr1.first ≤ intr2.first

def Interval.contains (intr : Interval) (n : Nat) : Bool :=
  intr.first ≤ n ∧ n ≤ intr.last

def Interval.length (intr : Interval) : Nat :=
  intr.last - intr.first + 1

def getIngredients : List String → Except ParseError (List Nat)
  | [] => pure []
  | x :: xs => do
    let num ← x.toNat?.toExcept ⟨s!"Input {x} is not a number"⟩
    return (num :: (← getIngredients xs))

def readInput : List String → List Interval → Except ParseError ((List Interval) × (List Nat))
  | [], _ => throw ⟨s!"No ingredients!"⟩
  | x :: xs, li => do
    if x = "" then
      let ingredients ← getIngredients (xs.filter (· ≠ ""))
      return (li, ingredients)
    else 
      let fl := x.splitOn "-"
      if h : fl.length ≠ 2 then
        throw ⟨s!"Interval {x} of wrong form!"⟩
      else
        let first ← fl[0].toNat?.toExcept ⟨s!"First part of interval not a number."⟩
        let second ← fl[1].toNat?.toExcept ⟨s!"Second part of interval not a number."⟩
        readInput xs (⟨first, second⟩ :: li) 

def is_fresh : List Interval → Nat → Bool
  | [], _ => false
  | x :: xs, n =>
    if x.first > n then
      false
    else if x.contains n then
      true
    else
      is_fresh xs n

namespace Problem1

def sumIds : List Nat → List Interval → Nat
  | [], _ => 0
  | x :: xs, intrs => 
    let count := if is_fresh intrs x then 1 else 0
    count + sumIds xs intrs

def solve (intrs : List Interval) (ingrs : List Nat) : Nat :=
  let sortedIntrs := intrs.mergeSort interval_le
  sumIds ingrs sortedIntrs

end Problem1

namespace Problem2

def combineIntervals : List Interval → List Interval
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
    if x.last ≥ y.first then 
      combineIntervals (⟨x.first, max x.last y.last⟩ :: xs)
    else
      x :: combineIntervals (y :: xs)
  termination_by xs => xs.length

def solve (intrs : List Interval) : Nat :=
  let sorted := intrs.mergeSort interval_le
  let combined := combineIntervals sorted
  combined.map Interval.length |>.sum

end Problem2

def problem1 (input : String) : Except ParseError String := do
  let (intrs, ingrs) ← readInput (input.splitOn "\n") []
  let ans := Problem1.solve intrs ingrs
  return (toString ans)

def problem2 (input : String) : Except ParseError String := do
  let (intrs, _) ← readInput (input.splitOn "\n") []
  let ans := Problem2.solve intrs
  return (toString ans)

end Day5

def day5 : Day := ⟨5, Day5.problem1, Day5.problem2, "3", "14"⟩
