import Aoc2025.Basic

namespace Day6

abbrev Operation := Nat → Nat → Nat

structure MathProblem where
  operation : Operation
  unit : Nat
  numbers : List Nat

def MathProblem.solve (mp : MathProblem) :=
  mp.numbers.foldr mp.operation mp.unit

def MathProblem.empty : MathProblem := ⟨(λ _ _ ↦ 0), 0, []⟩

def MathProblem.addVal (mp : MathProblem) (n : Nat) : MathProblem :=
  { mp with numbers := (n :: mp.numbers) }

def opToMath (op : String) (nums : List Nat) : Except ParseError MathProblem := do
  if op = "*" then
    pure ⟨(· * ·), 1, nums⟩
  else if op = "+" then
    pure ⟨(· + ·), 0, nums⟩
  else
    throw ⟨s!"Symbol {op} is not a known math operation"⟩

def addRow {arr : Array (List Nat)} {xs : List Nat} (h : xs.length ≤ arr.size)  :=
  match xs with
  | [] => arr
  | y :: ys =>
    let i := arr.size - (y :: ys).length
    have : i < arr.size := by
      simp [i]
      exact Nat.sub_lt 
        (by simp at h; omega) 
        (by omega)
    let newArr := arr.set i (y :: arr[i])
    have : ys.length ≤ newArr.size := by
      rw [Array.size_set]
      simp at h
      omega
    addRow this

def toNats : List String → Except ParseError (List Nat)
  | [] => pure []
  | x :: xs => do
    let num : Nat ← x.toNat?.toExcept ⟨s!"Value {x} is not a number."⟩
    pure (num :: (← toNats xs))


namespace Problem1

def readInput_helper (xs : List String) (arr : Array (List Nat)) : Except ParseError (Array (List Nat)) :=
  match xs with
  | [] => pure arr
  | y :: ys => do
    let yNat ← toNats <| (y.splitOn " ").filter (· ≠ "")
    if h : yNat.length = arr.size then
      have : yNat.length ≤ arr.size := by omega
      let newArr := addRow this
      pure (← readInput_helper ys newArr)
    else
      throw ⟨s!"Row {y} has wrong length: {yNat.length} vs {arr.size}"⟩

def toOp (s : String) : Except ParseError (Operation × Nat) :=
  if s = "*" then
    pure ((· * ·), 1)
  else if s = "+" then
    pure ((· + ·), 0)
  else
    throw ⟨s!"Operation {s} is not a known operation"⟩

def toOps : List String → Except ParseError (List (Operation × Nat))
  | [] => pure []
  | x :: xs => do
    let y ← toOp x
    pure <| y :: (← toOps xs)

def readInput (input : List String) : Except ParseError (Array MathProblem) := do
  let (nums, ops) := input.splitAt (input.length - 1)
  if h : ops.length ≠ 1 then
    throw ⟨"Empty input!"⟩
  else
    let opsList := ops[0].splitOn " " |>.filter (· ≠ "")
    let numsArray ← readInput_helper nums (Array.replicate opsList.length [])
    let ops' ← toOps <| opsList
    let zipped := numsArray.zip ops'.toArray
    pure <| zipped.map (λ (nl, (op, unit)) ↦ MathProblem.mk op unit nl)

def solve (input : Array MathProblem) : Nat :=
  input.map (·.solve) |>.sum

end Problem1

namespace Problem2

def firstRest (xs : List (List Char)) : (List (List Char)) × (List (List Char)) :=
  (xs.map (·.take 1), xs.map (·.drop 1))

def addNumToProblem : Nat → List MathProblem → List MathProblem
  | _, [] => []
  | n, x :: xs =>
    x.addVal n :: xs

def toMathProblems {xs : List (List Char)} {n : Nat} (h : ∀ i, i ∈ xs → i.length = n) : EStateM ParseError (List MathProblem) (List (List Char)) := 
  if n_zero : n = 0 then
    pure xs
  else do
    let fr := firstRest xs
    have len_one : ∀ j, j ∈ fr.fst → j.length = 1 := by
      intro j jinx
      simp [fr, firstRest] at jinx
      rcases jinx with ⟨i, inx, ihead⟩
      have : i.length = n := h i inx
      rw [← ihead]
      have : 1 ≤ i.length := by
        rw [this]
        omega
      exact List.length_take_of_le this
    have next : ∀ j, j ∈ fr.snd → j.length = (n - 1) := by
      intro j jinx
      simp [fr, firstRest] at jinx
      rcases jinx with ⟨i, inx, itail⟩
      have : i.length = n := h i inx
      rw [← this, ← itail]
      exact List.length_tail
    if fr.fst.any (· ≠ [' ']) then
      let split := fr.fst.splitAt (fr.fst.length - 1)
      let num ← match (String.ofList (split.fst.flatten) |>.trim.toNat?.toExcept ⟨s!"Not a number: {String.ofList split.fst.flatten |>.trim}"⟩) with
    |   .ok n => pure n
    |   .error e => throw e
      if opL_zero : split.snd.length = 0 then
        throw ⟨"Something has gone wrong somewhere"⟩
      else
        have : split.snd[0].length = 1 := by
          exact len_one split.snd[0] (by simp [split])
        let op := split.snd[0][0]
        if op = ' ' then
          modify (addNumToProblem num)
        else
          let (op, unit) ← match Problem1.toOp (op.toString) with
          | .ok p => pure p
          | .error e => throw e
          let problem : MathProblem := ⟨op, unit, [num]⟩
          modify (λ xs ↦ problem :: xs)
    toMathProblems next

def formatInput (input : String) : List (List Char) :=
  input.splitLines.map (·.toList)

def solve (input : String) : Except ParseError Nat :=
  let formatted := formatInput input
  if fl : formatted.length = 0 then
    throw ⟨"Input is empty"⟩
  else do
    let n := formatted[0].length
    if correct_length : formatted.all (·.length = n) then
      have : ∀ i, i ∈ formatted → i.length = n := by
        simp at correct_length
        omega
      let probs ← match EStateM.run (toMathProblems this) [] with
      | .ok _ p => pure p
      | .error e _ => throw e
      return (probs.map (·.solve)).sum
    else
      throw ⟨"Input consists of lines of differing length"⟩

end Problem2

def problem1 (input : String) : Except ParseError String := do
  let probs ← Problem1.readInput <| input.splitLines
  let ans := Problem1.solve probs
  return (toString ans)

def problem2 (input : String) : Except ParseError String := do
  let ans ← Problem2.solve input
  return (toString ans)

end Day6

def day6 : Day := ⟨6, Day6.problem1, Day6.problem2, "4277556", "3263827"⟩
