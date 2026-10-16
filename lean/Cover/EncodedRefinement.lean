import Cover.AlgebraicCodec
import Cover.AlgebraicEvidenceExecution

namespace Cover.AlgCode

/-- Reject malformed/noncanonical finite scalar evidence before semantic verification. -/
def verifyEncodedRefinement (original : AlgCode) (tokens : List ℕ) (h : ℚ) (positive : Bool) : Bool :=
  match AlgCodec.parseCanonical tokens with
  | none => false
  | some candidate => verifyRefinement original candidate h positive

 theorem verifyEncodedRefinement_sound {original : AlgCode} {tokens : List ℕ}
    {h : ℚ} {positive : Bool} {x : ℝ} (hx : original.denotes x)
    (hv : verifyEncodedRefinement original tokens h positive = true) :
    ∃ candidate : AlgCode, AlgCodec.parseCanonical tokens = some candidate ∧
      AlgCodec.serialize candidate = tokens ∧ original.valid ∧ candidate.valid ∧
      candidate.denotes x ∧ candidate.interval.width ≤ h ∧
      (positive = true → 0 < candidate.interval.lower) := by
  unfold verifyEncodedRefinement at hv
  cases hp : AlgCodec.parseCanonical tokens with
  | none => simp [hp] at hv
  | some candidate =>
    simp only [hp] at hv
    exact ⟨candidate, rfl, (AlgCodec.parseCanonical_sound hp).2, verifyRefinement_sound hx hv⟩

 theorem prepareMargin_encoded_verified {c : AlgCode} (hv : c.valid)
    (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    verifyEncodedRefinement c (AlgCodec.serialize (prepareMargin c hv hp s)) (marginMesh s) true = true := by
  obtain ⟨x, hx, _⟩ := validAlgBracket_denotes_unique c hv
  have hd := (prepareMargin_sound hv hx hp s).1
  simp only [verifyEncodedRefinement, AlgCodec.parseCanonical_roundtrip hd]
  exact prepareMargin_verified hv hp s

end Cover.AlgCode
