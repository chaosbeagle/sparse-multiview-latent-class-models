import Cover.A06RawValidation
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let rec nameExpr : Name → String
    | .anonymous => "Lean.Name.anonymous"
    | .str p s => "(Lean.Name.str " ++ nameExpr p ++ " " ++ reprStr s ++ ")"
    | .num p n => "(Lean.Name.num " ++ nameExpr p ++ " " ++ reprStr n ++ ")"
  let env ← getEnv
  let names := env.header.moduleNames
  let target := names.map (· == `Cover.A06RawValidation)
  let owners := env.const2ModIdx
  for (n,idx) in owners do
    if target[idx.toNat]! then
      match env.find? n with
      | some ci =>
        let kind := if ci.isTheorem then "theorem" else "constant"
        liftIO (IO.println s!"OWNED_DECL Cover.A06RawValidation {kind} {n}")
        liftIO (IO.println s!"OWNED_EXPR {n} {nameExpr n}")
      | none => liftIO (IO.println s!"OWNED_CODEGEN Cover.A06RawValidation {n}")
