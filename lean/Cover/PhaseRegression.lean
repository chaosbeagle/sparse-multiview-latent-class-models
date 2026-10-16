import Cover.A06Capped
import Cover.ByteRegression
import Cover.BoxRegression

namespace Cover.Regression

def positiveExpr : PolyExpr 1 0 := .mul (.rat 1) (.rat 1)

def phaseChecks : List Bool := [
  decide (FinTask.run 1 (intervalTask (coeff 0) (unitBox 1) positiveExpr) = none),
  decide (FinTask.run 3 (intervalTask (coeff 0) (unitBox 1) positiveExpr) = none),
  decide (FinTask.run 20 (intervalTask (coeff 0) (unitBox 1) positiveExpr) = some (⟨1,1⟩:QInterval)),
  decide (FinTask.run 1 (serializeTreeTask sampleTree) = none),
  decide (FinTask.run 3 (serializeTreeTask sampleTree) = none),
  decide (FinTask.run 100 (serializeTreeTask sampleTree) = some (serializeTree sampleTree)),
  decide (FinTask.run 1 (Bytes.serializeEvidenceBytesTask evidenceSample) = none),
  decide (FinTask.run 20 (Bytes.serializeEvidenceBytesTask evidenceSample) = none),
  decide (FinTask.run 50000 (Bytes.serializeEvidenceBytesTask evidenceSample) = some (Bytes.serializeEvidenceBytes evidenceSample)),
  decide (FinTask.run 1 (Bytes.parseEvidenceBytesTask 1 1 (Bytes.serializeEvidenceBytes evidenceSample)) = none),
  decide (FinTask.run 20 (Bytes.parseEvidenceBytesTask 1 1 (Bytes.serializeEvidenceBytes evidenceSample)) = none),
  decide (FinTask.run 50000 (Bytes.parseEvidenceBytesTask 1 1 (Bytes.serializeEvidenceBytes evidenceSample)) = some evidenceSample),
  decide (FinTask.run 1 (checkTreeStoredTask (coeff 1) constraint objective 1 .unit sampleTree) = none),
  decide (FinTask.run 3 (checkTreeStoredTask (coeff 1) constraint objective 1 .unit sampleTree) = none),
  decide (FinTask.run 1000 (checkTreeStoredTask (coeff 1) constraint objective 1 .unit sampleTree) = some true),
  decide (FinTask.run 3 (checkTreeStoredTask (coeff 0) constraint positiveExpr 0 .unit (.leaf .gap)) = none),
  decide (FinTask.run 20 (checkTreeStoredTask (coeff 0) constraint positiveExpr 0 .unit (.leaf .gap)) = some true)]

def runPhaseRegressions : IO Unit := do
  if phaseChecks.all id then IO.println "All 17 positive-fuel synthetic interval/serialization/parser/replay phase regressions passed."
  else throw (IO.userError "Synthetic capped phase regression failed.")

#eval runPhaseRegressions

end Cover.Regression
