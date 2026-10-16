import Cover.A06CachedDriver

namespace Cover.A06

 theorem parseRaw_design_valid {raw : List Nat} {I : Input}
    (hp : A06InputCodec.parseRaw raw = some I) : FiniteDesign.Valid I.design := by
  unfold A06InputCodec.parseRaw at hp
  cases hf : A06InputCodec.readFrames raw with
  | none => simp [hf] at hp
  | some frames =>
    rcases frames with ⟨d,w,s⟩
    rw [hf] at hp
    dsimp only at hp
    unfold A06InputCodec.parseParts at hp
    cases hd : DesignCodec.parse d with
    | none => simp [hd] at hp
    | some design =>
      rw [hd] at hp
      dsimp only at hp
      cases hw : AlgCodec.parseCanonical w with
      | none => simp [hw] at hp
      | some weight =>
        rw [hw] at hp
        dsimp only at hp
        cases hs : AlgCodec.parseCanonical s with
        | none => simp [hs] at hp
        | some sigma =>
          rw [hs] at hp
          cases hp
          exact DesignCodec.parse_some_valid hd

structure AdmittedTokens (raw : List Nat) where
  input : Input
  valid : Valid input
  binding : A06InputCodec.serialize input = raw

 def Returned.BoundToTokens (raw : List Nat) (r : Returned) : Prop :=
  A06InputCodec.serialize r.input = raw

 theorem stageAction_bound (I : Input) (h : Valid I) (raw : List Nat)
    (hraw : A06InputCodec.serialize I = raw) (s : Nat) :
    Capped.ActionChecked (fun r => r.Checked ∧ r.BoundToTokens raw) (stageAction I h s) := by
  unfold stageAction
  split
  · trivial
  · trivial
  · rename_i tree hs
    exact ⟨⟨Bytes.parseEvidenceByteArray_serialize _, successfulStage_certificate_verified I h s tree hs⟩,hraw⟩

end Cover.A06
