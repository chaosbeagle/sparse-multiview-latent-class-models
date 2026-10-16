import lean.ComputabilityAudit
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `lean.ComputabilityAudit
  let mut kernel := 0
  let mut codegen := 0
  for (n, i) in env.const2ModIdx do
    if env.header.moduleNames[i.toNat]! == target then
      if (env.find? n).isSome then kernel := kernel+1 else codegen := codegen+1
  liftIO (IO.println s!"COMPUTABILITY_INSTRUMENTATION_OWNERSHIP kernel={kernel} codegen={codegen}")
