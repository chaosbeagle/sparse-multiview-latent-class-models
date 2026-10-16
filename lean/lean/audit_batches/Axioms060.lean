import Cover.ConstraintCompiler
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.header.moduleNames
  let target := names.map (· == `Cover.ConstraintCompiler)
  for (n, idx) in env.const2ModIdx do
    if target[idx.toNat]! then
      if (env.find? n).isSome then
        elabCommand (← `(#print axioms $(mkIdent n)))
