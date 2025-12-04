structure ParseError where
  message : String
deriving Repr

def ParseError.getMessage (pErr : ParseError) : String :=
  s!"ParseError on line {pErr.message}"

def Option.toExcept (val? : Option α) (e : ParseError) : Except ParseError α :=
  match val? with
  | some x => pure x
  | none => throw e

def String.splitLines (s : String) : List String :=
  s.splitOn "\n" |>.filter (· ≠ "")


structure Day where
  i : Nat 
  problem1 : String → Except ParseError String
  problem2 : String → Except ParseError String
  test1Result : String
  test2Result : String

def get_test_one (day : Day) : IO String := do
  let filename := s!"data/test/day{day.i}-1.txt"
  let file : System.FilePath := filename
  IO.FS.readFile file

def get_test_two (day : Day) : IO String := do
  let filename := s!"data/test/day{day.i}-2.txt"
  let file : System.FilePath := filename
  IO.FS.readFile file

def Day.runTest (day : Day) : IO Unit := do
  let serr ← IO.getStderr
  let test_data_one ← get_test_one day
  let test_data_two ← get_test_two day
  let problem1Result := match (day.problem1 test_data_one) with
  | .ok result => result
  | .error pError => pError.getMessage
  let problem2Result := match (day.problem2 test_data_two) with
  | .ok result => result
  | .error pError => pError.getMessage
  if problem1Result ≠ day.test1Result then
    serr.putStrLn s!"Day {day.i} Problem 1 gives wrong test result. Expected: {day.test1Result} Actual: {problem1Result}."
  if problem2Result ≠ day.test2Result then
    serr.putStrLn s!"Day {day.i} Problem 2 gives wrong test result. Expected: {day.test2Result} Actual: {problem2Result}."

def getReal (day : Day) : IO String := do
  let filename := s!"data/real/day{day.i}.txt"
  let file : System.FilePath := filename
  IO.FS.readFile file

def Day.runReal (day : Day) : IO Unit := do
  let sout ← IO.getStdout
  let realData ← getReal day
  let day1Result := match (day.problem1 realData) with
  | .ok result => result
  | .error pError => pError.getMessage
  let day2Result := match (day.problem2 realData) with
  | .ok result => result
  | .error pError => pError.getMessage
  sout.putStrLn s!"Day {day.i} real - Problem 1: {day1Result} Problem 2: {day2Result}"

def Day.run (day : Day) : IO Unit := do
  day.runTest
  day.runReal
