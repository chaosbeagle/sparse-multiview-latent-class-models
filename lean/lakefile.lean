import Lake
open Lake DSL
package «a06_generalization» where
/-- Compile every own source and audit from scratch against the pinned read-only runtime.
    A custom target avoids Lake mutating shared dependency build metadata. -/
@[default_target]
target checkedProofs pkg : Unit := do
  Job.async do
    let result ← IO.Process.output {
      cmd := "python3", args := #["build_project.py"], cwd := some pkg.dir}
    if result.exitCode != 0 then error (result.stdout ++ result.stderr)
    logInfo result.stdout
