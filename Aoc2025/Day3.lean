import Aoc2025.Basic

def toDigitList : List Char → Except ParseError (List Nat)
  | [] => return []
  | x :: xs =>
    if x.isDigit then
      return (x.toNat - 48) :: (← toDigitList xs)
    else
      throw ⟨s!"Character {x} is not a digit."⟩


namespace Day3

def maxNotLastN (xs : List Nat) (n : Nat) : Option Nat :=
  (xs.take (xs.length - (n -1))).max?

def getRest (xs : List Nat) (n : Nat) : List Nat :=
  xs.dropWhile (· < n) |>.drop 1

def maxOfRest (xs : List Nat) (n : Nat) : Option Nat :=
  xs.dropWhile (· < n) |>.drop 1 |>.max?

def joltage (xs : List Nat) (n : Nat := 2) : Option Nat := do
  if n = 0 then 
    return (0 : Nat)
  else 
    let current ← maxNotLastN xs n
    let rest := getRest xs current
    return (10 ^ (n - 1)) * current + (← joltage rest (n - 1))

namespace Problem1

def solve : List String → Except ParseError Nat
  | [] => return 0
  | x :: xs => do
    let digits ← toDigitList x.toList
    let jolt? := joltage digits
    let jolt ← match jolt? with
      | some x => pure x
      | none => throw ⟨s!"String {x} does not consist of at least two digits."⟩
    return jolt + (← solve xs)

end Problem1

namespace Problem2

def solve : List String → Except ParseError Nat
  | [] => return 0
  | x :: xs => do
    let digits ← toDigitList x.toList
    let jolt? := joltage digits 12
    let jolt ← match jolt? with
      | some x => pure x
      | none => throw ⟨s!"String {x} does not consist of at least 12 digits."⟩
    return jolt + (← solve xs)

end Problem2

def problem1 (input : String) : Except ParseError String := do
  let ans ← Problem1.solve input.splitLines
  return (toString ans)

def problem2 (input : String) : Except ParseError String := do
  let ans ← Problem2.solve input.splitLines
  return (toString ans)

end Day3

def day3 : Day := ⟨3, Day3.problem1, Day3.problem2, "357", "3121910778619"⟩
