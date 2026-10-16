import lean.CoverRegression
import Cover.CompilerTaskDegree

namespace Cover.A06ModelRegression

/-- Fixed finite compiler-only fixture: 3 groups, rank 2, binary outputs, one edge.
No scalar evaluation, Stage traversal or search for a numerical Delta is performed.
The execution budget is exactly 200000 task transitions, under the build's 4096 MiB cap. -/
def runCompilerFuelRegression : IO Unit := do
  let task := CompilerTasks.compileTask input.design input_valid.1
  if (FinTask.run 0 task).isSome || (FinTask.run 1 task).isSome then
    throw (IO.userError "Compiler interruption regression failed")
  match FinTask.run 200000 task with
  | none => throw (IO.userError "Compiler-only regression exhausted its fixed 200000-fuel budget; no larger retry is implied")
  | some data =>
      if data.n == 14 && data.constraintCount == 48 && data.objective.variableDegree ≤ 8 then
        IO.println "PASS stepped compiler-only regression: n=14, constraints=48, objective degree<=8; zero/one fuel interrupted; no Stage or Delta search"
      else throw (IO.userError "Compiler-only regression returned unexpected finite syntax metadata")

#eval runCompilerFuelRegression

end Cover.A06ModelRegression
