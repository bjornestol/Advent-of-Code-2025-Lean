import Aoc2025.Basic
import Regex
import Std.Data.TreeSet
import Init.Data.Queue

namespace Day10

abbrev Button := Nat

structure Machine where
  target : Button
  buttons : List Button
  joltage : List Nat
deriving Repr

def machineRegex := re! r"\[([\.#]+)\]\s((?:\([\d,]*\)\s)*)\{([\d,]*)\}"

def targetToNat (s : String) : Nat := 
  s.toList.zipIdx.map (λ (bu, bi) ↦ 2^bi * (if bu = '#' then 1 else 0)) |>.sum

def numsToNats : List String → Except ParseError (List Nat)
| [] => pure []
| x :: xs => do
  let n ← x.toNat?.toExcept ⟨s!"Not a number: {x}"⟩
  return (n :: (← numsToNats xs))

def buttonToNat (s : String) : Except ParseError Nat := do
  let de := s.drop 1 |>.dropRight 1
  let nums ← numsToNats <| de.splitOn ","
  return (nums.map (1 <<< ·) |>.sum)

def buttonsToNats (s : String) : Except ParseError (List Nat) :=
  let buttons := s.splitOn " " |>.filter (· ≠ "")
  buttons.foldr (
    λ button ans ↦ do
    let b ← buttonToNat button
    let a ← ans
    return b :: a
  ) (pure [])

def joltageToNats (s : String) : Except ParseError (List Nat) :=
  numsToNats (s.splitOn ",")

def inputToMachines : List String → Except ParseError (List Machine)
| [] => pure []
| x :: xs => do
  let captures ← (machineRegex.capture x).toExcept ⟨s!"Could not match machine in line {x}"⟩
  let target ← captures.get 1 |>.toExcept ⟨s!"Could not find target state in line {x}"⟩
  let buttons ← captures.get 2 |>.toExcept ⟨s!"Could not find buttons in line {x}"⟩
  let joltage ← captures.get 3 |>.toExcept ⟨s!"Could not find joltages in line {x}"⟩
  return (⟨targetToNat target.copy, (← buttonsToNats buttons.copy), (← joltageToNats joltage.copy)⟩ :: (← inputToMachines xs))

namespace Problem1

structure State where
  target : Nat
  current : Nat
  steps : Nat
  visited : Std.TreeSet Nat
  queue : Std.Queue (Button × Nat)


def pushButtons : List Button → StateM State (Option Nat)
| [] => return none
| x :: xs => do
  let state ← get
  let newButton := state.current ^^^ x
  if newButton = state.target then
    pure <| some (state.steps + 1)
  else if state.visited.contains newButton then
    pushButtons xs
  else
    let newV := state.visited.insert newButton
    let newQ := state.queue.enqueue (newButton, state.steps + 1)
    set { state with visited := newV, queue := newQ}
    pushButtons xs

partial def nextStep (machine : Machine) : StateM State Nat := do
  let state ← get
  match state.queue.dequeue? with
  | none => pure 0
  | some ((btn, s), q) =>
    set {state with steps := s, current := btn, queue := q}
    match (← pushButtons machine.buttons) with
    | some n => pure n
    | none =>
      nextStep machine

def solve (machines : List Machine) : Nat :=
  machines.map (λ m ↦ nextStep m |>.run' ⟨m.target, 0, 0, (∅ : Std.TreeSet Nat).insert 0, (∅ : Std.Queue (Button × Nat)).enqueue (0, 0)⟩ |>.run) |>.sum

end Problem1

namespace Problem2


def allOptions_aux (amt : Nat) (sum : Nat) (xs : List Nat := []) : StateM (List (List Nat)) Unit :=
  if amt ≤ 1 then
    modify ((sum :: xs) :: ·)
  else
    for i in [0 : sum + 1] do
      allOptions_aux (amt - 1) (sum - i) (i :: xs)

def allOptions (amt : Nat) (sum : Nat) : List (List Nat) :=
  allOptions_aux amt sum |>.run [] |>.snd

def nPr (n : Nat) (r : Nat) : Nat :=
  if r = 0 then
    1
  else
    n * nPr (n - 1) ( r - 1)

def nCr (n : Nat) (r : Nat) : Nat :=
  (nPr n r) / (nPr r r)

def amtOptions (amt : Nat) (sum : Nat) : Nat :=
  nCr (sum + amt - 1) (amt - 1)

def findBestJoltage (m : Machine) (buttonsIdx : List (Button × Nat)) (alreadyPressed : Nat) (currPresses : Vector Nat m.buttons.length) : 
    List Nat → List (Nat × Nat)
| [] => []
| j :: js =>
  let remainingButtons := buttonsIdx.filter (λ x ↦ (1 <<< x.snd) &&& alreadyPressed = 0)
  let relevantButtons := remainingButtons.filter (·.fst &&& (1 <<< j) ≠ 0)
  let currSum := buttonsIdx.filter (·.fst &&& (1 <<< j) ≠ 0) |>.map (currPresses[·.snd]!) |>.sum
  (j, amtOptions (relevantButtons.length) (m.joltage[j]! - currSum)) :: findBestJoltage m buttonsIdx alreadyPressed currPresses js

partial def pressButtons (m : Machine) (jUnchecked : List Nat := [: m.joltage.length].toList)
  (alreadyPressed : Nat := 0) (currPresses : Vector Nat m.buttons.length := Vector.replicate m.buttons.length 0) 
  : StateM (List (Vector Nat m.buttons.length)) Unit :=
  if jLegal : jUnchecked = []then
    modify (currPresses :: ·)
  else
  let buttonsIdx := m.buttons.zipIdx
  let remainingButtons := buttonsIdx.filter (λ x ↦ (1 <<< x.snd) &&& alreadyPressed = 0)
  let joltages := findBestJoltage m buttonsIdx alreadyPressed currPresses jUnchecked |>.mergeSort (·.snd ≤ ·.snd)
  have : joltages.length = jUnchecked.length  := by
    unfold joltages
    induction jUnchecked with
    | nil => 
      unfold findBestJoltage
      simp
    | cons x xs ih => 
      unfold findBestJoltage
      simp
      simp at ih
      sorry
   have : joltages ≠ [] := by
     refine List.ne_nil_of_length_pos ?_
     rw [this]
     exact List.length_pos_iff.mpr jLegal
  let jNo := joltages.head this |>.fst
  let newUnchecked := jUnchecked.filter (· ≠ jNo)
  let relevantButtons := remainingButtons.filter (·.fst &&& (1 <<< jNo) ≠ 0)
  let currSum := buttonsIdx.filter (·.fst &&& (1 <<< jNo) ≠ 0) |>.map (currPresses[·.snd]!) |>.sum
  if currSum > m.joltage[jNo]! then
    pure ()
  else
  let pressed := alreadyPressed ||| (relevantButtons.map (1 <<< ·.snd) |>.foldr (· ||| ·) 0)
  let options := allOptions (relevantButtons.length) (m.joltage[jNo]! - currSum)
  for optn in options do
    let bop := relevantButtons.map (λ x ↦ x.snd) |>.zip optn
    let newPresses := bop.foldr (λ btn vec ↦ vec.setIfInBounds btn.fst btn.snd  ) currPresses
    pressButtons m newUnchecked pressed newPresses

def solve : (List Machine) → Option Nat
| [] => some 0
| m :: ms => do
  let n ← pressButtons m |>.run [] |>.snd |>.map (·.sum) |>.min?
  pure (n + (← solve ms))

end Problem2

def problem1 (input : String) : Except ParseError String := do
  let m ← inputToMachines input.splitLines
  return (toString (Problem1.solve m))

def problem2 (input : String) : Except ParseError String := do
  let m ← inputToMachines input.splitLines
  match Problem2.solve m with
  | none => throw ⟨s!"Unreachable joltage for some machine"⟩
  | some n => return (toString n)

end Day10

def day10 : Day := ⟨10, Day10.problem1, Day10.problem2, "7", "33"⟩
