import Cover.A06Capped

namespace Cover.A06.CappedRegression

/-- Diagnostic encoding only; no admitted A06 pilot or numerical certificate is run. -/
def status : CappedResult → Nat
  | .unknownResource => 0
  | .invalidInput => 1
  | .implementationError => 2
  | .certificate _ => 3

def badMarginInput : Input := {
  design := { groups := 3, rankPred := 1, outputPred := fun _ => 1, edges := [Finset.univ] }
  weight := .rat 0
  sigma := .rat 1 }

def checks : List Bool := [
  decide (status (runCoverCapped ByteArray.empty 0) = 0),
  decide (status (runCoverCapped ByteArray.empty 1) = 0),
  decide (status (runCoverCapped ByteArray.empty 2) = 1),
  decide (status (runCoverCapped ⟨#[1]⟩ 2) = 0),
  decide (status (runCoverCapped ⟨#[1]⟩ 100) = 1),
  decide (status (runCoverCapped ⟨#[255]⟩ 3) = 1),
  decide (status (runCoverCapped ⟨(List.replicate 50 (1:UInt8)).toArray⟩ 10) = 0),
  decide (status (runCoverCapped ⟨(List.replicate 50 (1:UInt8)).toArray⟩ 500) = 1),
  decide (status (runCoverCapped (serializeInputBytes badMarginInput) 0) = 0),
  decide (status (runCoverCapped (serializeInputBytes badMarginInput) 10000) = 1)]

def runMalformedInputRegressions : IO Unit := do
  if checks.all id then IO.println "All 10 malformed-input/interruption capped regressions passed; no admitted pilot run."
  else throw (IO.userError "A06 capped malformed-input regression failed.")

#eval runMalformedInputRegressions

end Cover.A06.CappedRegression
