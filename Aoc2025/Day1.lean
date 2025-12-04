import Aoc2025.Basic

namespace Day1

inductive Instruction where
  | left (x : Fin 100) (loops : Nat)
  | right (x : Fin 100) (loops : Nat)

def toInstruction (instr : String) : Except ParseError Instruction := do
    let num? := (instr.drop 1).toNat?
    let num ← match num? with
    | some n => pure n
    | none => throw ⟨s!"Element '{instr.drop 1}' is not a number."⟩
    let rem := num % 100
    let loops := num / 100
    have h : rem < 100 := by
      simp [rem]
      exact Nat.mod_lt num (by omega)
    if (instr.startsWith "L") then
      return Instruction.left ⟨rem, h⟩ loops
    else if (instr.startsWith "R") then
      return Instruction.right ⟨rem, h⟩ loops
    else
      throw ⟨s!"Instruction does not start with L or R."⟩

def toInstructions : List String → Except ParseError (List Instruction)
  | [] => return []
  | x :: xs => do
    let rest ← toInstructions xs
    return (← toInstruction x) :: rest

namespace Problem1
def newState : Instruction → Fin 100 → Fin 100
  | .left x _, state => (state - x : Fin 100)
  | .right x _, state => state + x

def solve (instructions : List Instruction) (answer : Nat := 0) (state : Fin 100 := 50) : Nat :=
  match instructions with
  | [] => answer
  | instr :: rest =>
    let nState := newState instr state
    solve rest (answer + if nState = 0 then 1 else 0) nState
end Problem1

namespace Problem2
def newState : Instruction → Fin 100 → Fin 100 × Nat
  | .left x loops, state =>
    (state - x, loops + if x ≥ state ∧ state ≠ 0 then 1 else 0)
  | .right x loops, state =>
    (state + x, loops + if x ≥ 100 - state ∧ state ≠ 0 then 1 else 0)

def solve (instructions : List Instruction) (answer : Nat := 0) (state : Fin 100 := 50) : Nat :=
  match instructions with
  | [] => answer
  | instr :: rest =>
    let (nState, inc) := newState instr state
    solve rest (answer + inc) nState
end Problem2

def problem1 (input : String) : Except ParseError String := do
  let ans := Problem1.solve (← toInstructions input.splitLines)
  return (toString ans)

def problem2 (input : String) : Except ParseError String := do
  let ans := Problem2.solve (← toInstructions input.splitLines)
  return (toString ans)

end Day1

def day1 : Day := ⟨1, Day1.problem1, Day1.problem2, "3", "6"⟩
