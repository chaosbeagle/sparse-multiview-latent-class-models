import Cover.Certificate

namespace Cover

/-- Final-facing payload. The refinement lists contain the actual finite scalar
    codes, to be decoded and checked against the original input by the A06 checker. -/
structure EvidenceCertificate (n j : Nat) where
  base : CoverCertificate n j
  weightRefinement : List Nat
  sigmaRefinement : List Nat
  deriving DecidableEq, Repr

inductive EvidenceToken where
  | refinements (weight sigma : List Nat)
  | base (token : CoverToken)
  | unknown (tag : Nat)
  deriving DecidableEq, Repr

def serializeEvidenceCertificate (c : EvidenceCertificate n j) : List EvidenceToken :=
  .refinements c.weightRefinement c.sigmaRefinement :: (serializeCertificate c.base).map .base

def unwrapBaseTokens : List EvidenceToken → Option (List CoverToken)
  | [] => some []
  | .base t :: ts => (unwrapBaseTokens ts).map (t :: ·)
  | _ => none

theorem unwrapBaseTokens_map (tokens : List CoverToken) :
    unwrapBaseTokens (tokens.map .base) = some tokens := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih => simp [unwrapBaseTokens, ih]

theorem unwrapBaseTokens_sound (tokens : List EvidenceToken) (base : List CoverToken)
    (h : unwrapBaseTokens tokens = some base) : base.map .base = tokens := by
  induction tokens generalizing base with
  | nil => cases h; rfl
  | cons token tokens ih =>
    cases token with
    | refinements weight sigma => contradiction
    | unknown tag => contradiction
    | base t =>
      cases hu : unwrapBaseTokens tokens with
      | none => simp [unwrapBaseTokens, hu] at h
      | some ts =>
        simp only [unwrapBaseTokens, hu, Option.map_some, Option.some.injEq] at h
        subst base
        simp [ih ts hu]

def parseEvidenceCertificate (n j : Nat) : List EvidenceToken → Option (EvidenceCertificate n j)
  | .refinements weight sigma :: rest => do
      let tokens ← unwrapBaseTokens rest
      let base ← parseCertificate n j tokens
      some ⟨base, weight, sigma⟩
  | _ => none

theorem parseEvidenceCertificate_serialize (c : EvidenceCertificate n j) :
    parseEvidenceCertificate n j (serializeEvidenceCertificate c) = some c := by
  simp [parseEvidenceCertificate, serializeEvidenceCertificate, unwrapBaseTokens_map,
    parseCertificate_serialize]

theorem parseEvidenceCertificate_sound (tokens : List EvidenceToken) (c : EvidenceCertificate n j)
    (h : parseEvidenceCertificate n j tokens = some c) : serializeEvidenceCertificate c = tokens := by
  cases tokens with
  | nil => contradiction
  | cons token tokens =>
    cases token with
    | base t => contradiction
    | unknown tag => contradiction
    | refinements weight sigma =>
      simp only [parseEvidenceCertificate] at h
      cases hu : unwrapBaseTokens tokens with
      | none => simp [hu] at h
      | some ts =>
        rw [hu] at h
        dsimp only [Bind.bind, Option.bind] at h
        cases hb : parseCertificate n j ts with
        | none => simp [hb] at h
        | some base =>
          rw [hb] at h
          dsimp only [Bind.bind, Option.bind] at h
          cases h
          simp only [serializeEvidenceCertificate, parseCertificate_sound n j ts base hb,
            unwrapBaseTokens_sound tokens ts hu]

/-- Binding lives in the base certificate and survives the evidence wrapper. -/
theorem evidence_exact_input_binding (c : EvidenceCertificate n j) (input : List Nat)
    (cs : Nat → Fin a → QInterval) (gs : Fin j → PolyExpr n a) (H : PolyExpr n a)
    (h : verifyCoverCertificate input cs gs H c.base = true) :
    c.base.input = input ∧ c.base.formatVersion = formatVersion ∧
      c.base.generatorVersion = generatorVersion :=
  verifyCoverCertificate_binding input cs gs H c.base h

end Cover
