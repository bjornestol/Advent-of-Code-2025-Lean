import Aoc2025.Basic
import Std.Data.TreeSet

-- Antall siffer i `n` i titallsystemet
def Nat.digits_dec (n : Nat) : Nat := toString n |>.length

-- De `amt` første sifrene i `n`
def Nat.first_digits (n amt : Nat) : Nat := n / 10^(n.digits_dec - amt)

-- Repeter tallet `n` `d` ganger (halerekursivt)
def Nat.repeat_digits (n d : Nat) (cumul : Nat := 0) : Nat :=
  if d = 0 then
    cumul
  else
    n.repeat_digits (d - 1) (cumul * 10 ^ n.digits_dec + n)

namespace Day2

-- Representerer et intervall som starter i `first`, ender i `last`, hvor alle tall har `digits` sifre.
structure DigitConstInterval where
  first : Nat
  last : Nat
  digits : Nat
deriving Repr

-- Leser input, gjør om fra en lang streng til liste med par av heltall
def readInput (input : String) : Except ParseError (List (Nat × Nat)) := do
  let lines := input.splitOn "," |>.filter (· ≠ "")
  lines.mapM λ x ↦ do
    let fl := x.splitOn "-"
    if h : fl.length ≠ 2 then
      throw ⟨s!"String {x} not of form Nat-Nat"⟩
    else
      let num1 ← fl[0].toNat?.toExcept ⟨s!"Value {fl[0]} is not a Nat"⟩
      let num2 ← fl[1].toNat?.toExcept ⟨s!"Value {fl[1]} is not a Nat"⟩
      pure (num1, num2)

-- Gjør om for eksempel (95, 1013) til [(95, 99), (100, 999), (1000, 1013)]. 
def toIntervals (firstNat lastNat : Nat) : List DigitConstInterval := Id.run do
  let mut xs : List DigitConstInterval := []
  for digits in [firstNat.digits_dec : lastNat.digits_dec + 1] do
    xs := ⟨max firstNat (10^(digits-1)), min lastNat (10^digits - 1), digits⟩ :: xs 
  return xs

def invalidIds_helper (intr : DigitConstInterval) (digits first last : Nat) (set : Std.TreeSet Nat) : Std.TreeSet Nat :=
  if (first > last) then set
  else
    invalidIds_helper intr digits (first + 1) last (set.insert (first.repeat_digits (intr.digits / digits)))
  termination_by last + 1 - first

-- Finner alle ulovlige IDer i et konstant-siffer-intervall, om hvert tall skal repteres `rep` antall ganger.
-- Lagrer dem i en muligens allerede eksisterende mengde `set`
def invalidIds (intr : DigitConstInterval) (rep : Nat) (set : Std.TreeSet Nat := ∅) : Std.TreeSet Nat :=
  if intr.digits % rep ≠ 0 then
    set
  else
    let digits := intr.digits / rep
    let first? := intr.first.first_digits digits
    let first := if first?.repeat_digits rep ≥ intr.first then first? else first? + 1
    let last? := intr.last.first_digits digits
    let last := if last?.repeat_digits rep ≤ intr.last then last? else last? - 1
    invalidIds_helper intr digits first last set

-- Finner alle ulovlige IDer fra `firstNat`` til `lastNat`` hvor vi bruker `rep` repetisjoner
def allInvalidIds (firstNat lastNat rep : Nat) (set : Std.TreeSet Nat := ∅) : Std.TreeSet Nat :=
  let intrs := toIntervals firstNat lastNat
  intrs.foldr (λ i s ↦ invalidIds i rep s) set

namespace Problem1

def solve_find_set : List (Nat × Nat) → Std.TreeSet Nat → Std.TreeSet Nat
  | [], set => set
  | (firstNat, lastNat) :: xs, set =>
    let newSet := allInvalidIds firstNat lastNat 2 set
    solve_find_set xs newSet

def solve (xs : List (Nat × Nat)) : Nat :=
  (solve_find_set xs ∅).foldr (· + ·) 0

end Problem1

namespace Problem2

def all_invalid_all_rep (firstNat lastNat rep : Nat) (set : Std.TreeSet Nat := ∅) : Std.TreeSet Nat :=
  if rep > lastNat.digits_dec then
    set
  else
    let newSet := allInvalidIds firstNat lastNat rep set
    all_invalid_all_rep firstNat lastNat (rep + 1) newSet
  termination_by lastNat.digits_dec + 1 - rep

def solve_find_set : List (Nat × Nat) → Std.TreeSet Nat → Std.TreeSet Nat
  | [], set => set
  | (firstNat, lastNat) :: xs, set =>
    let newSet := all_invalid_all_rep firstNat lastNat 2 set
    solve_find_set xs newSet

def solve (xs : List (Nat × Nat)) : Nat :=
  (solve_find_set xs ∅).foldr (· + ·) 0

end Problem2

def problem1 (input : String) : Except ParseError String := do
  let pairs ← readInput (input.stripSuffix "\n")
  let ans := Problem1.solve pairs
  return (toString ans)

def problem2 (input : String) : Except ParseError String := do
  let pairs ← readInput (input.stripSuffix "\n")
  let ans := Problem2.solve pairs 
  return (toString ans)

end Day2

def day2 : Day := ⟨2, Day2.problem1, Day2.problem2, "1227775554", "4174379265"⟩
