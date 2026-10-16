import Cover.Search
import Cover.EvidenceCertificate

namespace Cover.Regression

def coeff : Nat → Fin 0 → QInterval := fun _ => Fin.elim0

def constraint : Fin 1 → PolyExpr 1 0 := fun _ => .add (.var 0) (.rat (-3/4))
def objective : PolyExpr 1 0 := .mul (.var 0) (.var 0)
def prepare : Nat → FinTask (Fin 0 → QInterval) := fun _ => .done Fin.elim0

def sampleTree : CoverTree 1 1 := .split 0 (.leaf (.exclude 0)) (.leaf .gap)
def sampleCert : CoverCertificate 1 1 := makeCertificate [7, 11] 1 sampleTree

def gotCertificate : CappedOutcome n j → Bool
  | .certificate _ _ => true
  | _ => false

def checks : List Bool := [
  decide (checkLeaf (coeff 1) constraint objective 1 (fun _ => ⟨1/2, 1⟩) .gap = true),
  decide (checkLeaf (coeff 1) (fun _ : Fin 1 => (.rat 0 : PolyExpr 1 0)) objective 1 (unitBox 1) (.exclude 0) = false),
  decide (coverStage coeff constraint objective (by decide) 0 = .inconclusive),
  decide (coverStage coeff constraint objective (by decide) 1 = .success sampleTree),
  decide ((visit (coeff 1) constraint objective 1 (by decide) 1 0 (unitBox 1)).1 = 3),
  decide (verifyCoverCertificate [7, 11] coeff constraint objective sampleCert = true),
  decide (verifyCoverCertificate [7, 12] coeff constraint objective sampleCert = false),
  decide (verifyCoverCertificate [7, 11] coeff constraint objective { sampleCert with formatVersion := 2 } = false),
  decide (parseTree 1 1 5 [.split 0, .gap] = none),
  decide (parseTree 1 1 5 [.split 1, .gap, .gap] = none),
  decide (parseTree 1 1 5 [.exclude 1] = none),
  decide (parseCertificate 1 1 (serializeCertificate sampleCert ++ [.gap]) = none),
  decide (runCoverFuel [7, 11] (.step fun _ => .done false) prepare constraint objective (by decide) 1 = .unknownResource),
  decide (runCoverFuel [7, 11] (.step fun _ => .done false) prepare constraint objective (by decide) 2 = .invalidInput),
  decide (gotCertificate (runCoverFuel [7, 11] (.done true) prepare constraint objective (by decide) 200) = true)]

#eval do
  if checks.all id then IO.println "All 15 synthetic finite-cover regressions passed."
  else throw (IO.userError "Synthetic finite-cover regression failed.")

#eval runCoverFuel [7, 11] (.done true) prepare constraint objective (by decide) 200
#eval parseEvidenceCertificate 1 1 (serializeEvidenceCertificate ⟨sampleCert, [1, 2, 3], [4, 5, 6]⟩)

end Cover.Regression
