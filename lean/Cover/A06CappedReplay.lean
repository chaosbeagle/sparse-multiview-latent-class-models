import Cover.A06CappedCore
import Cover.ScalarTasks
import Cover.AlgebraicCodecTasks
import Cover.A06EdgeListsTask
import Cover.BoxTasks

namespace Cover.A06
open FinTask

abbrev ConstraintArray (I : Input) (h : Valid I) :=
  Fin (constraintCount I h) → PolyExpr (pairDimension I h) 3
abbrev Objective (I : Input) (h : Valid I) := PolyExpr (pairDimension I h) 3

/-- Full independent final checker replay against cached, exactly compiled expressions.
    Input equality, both canonical scalar decoders, both original-code refinement
    checks, every scalar operation, and every tree interval operation are stepped. -/
def verifyCertificateTask (I : Input) (h : Valid I) (raw : List Nat)
    (gs : ConstraintArray I h) (H : Objective I h) (c : Certificate I h) : FinTask Bool := do
  let inputMatch ← equalListTask c.base.input raw
  let versions ← .step fun _ => .done (decide (c.base.formatVersion = Cover.formatVersion ∧
    c.base.generatorVersion = Cover.generatorVersion))
  if inputMatch && versions then do
    let wp ← AlgCodec.parseCanonicalTask c.weightRefinement
    let sp ← AlgCodec.parseCanonicalTask c.sigmaRefinement
    match wp, sp with
    | some wr, some sr => do
      let mesh ← AlgCode.marginMeshTask c.base.precision
      let hw ← AlgCode.verifyRefinementTask I.weight wr mesh true
      let hs ← AlgCode.verifyRefinementTask I.sigma sr mesh true
      if hw && hs then do
        let edges ← edgeListsTask I
        let cs ← Literal.coefficientBoundsTask (alphabetSizes I) edges c.base.precision wr.interval sr.interval
        checkTreeStoredTask cs gs H c.base.k .unit c.base.tree
      else .done false
    | _, _ => .done false
  else .done false

theorem verifyCertificateTask_result (I : Input) (h : Valid I) (raw : List Nat)
    (hraw : raw = A06InputCodec.serialize I)
    (gs : ConstraintArray I h) (H : Objective I h)
    (hgs : gs = ProjectSemantics.constraintArray I.design h.1)
    (hH : H = ConcreteCompiler.objective I.design h.1) (c : Certificate I h) :
    (verifyCertificateTask I h raw gs H c).result = verifyCertificate I h c := by
  subst raw; subst gs; subst H
  have result_if {α : Type} (p : Prop) [Decidable p] (a b : FinTask α) :
      (if p then a else b).result = if p then a.result else b.result := by split <;> rfl
  by_cases hm : certificateMetadata I h c
  · have hi := hm.1
    have hf := hm.2.1
    have hg := hm.2.2
    cases hw : AlgCodec.parseCanonical c.weightRefinement with
    | none => simp [verifyCertificateTask, verifyCertificate, certificateMetadata, hi,hf,hg,
        equalListTask_result, AlgCodec.parseCanonicalTask_result, hw, result_if]
    | some wr =>
      cases hs : AlgCodec.parseCanonical c.sigmaRefinement with
      | none => simp [verifyCertificateTask, verifyCertificate, certificateMetadata, hi,hf,hg,
          equalListTask_result, AlgCodec.parseCanonicalTask_result, hw,hs, result_if]
      | some sr =>
        simp only [verifyCertificateTask, FinTask.result_bindM, equalListTask_result,
          FinTask.result_step, FinTask.result_done, result_if, hi,hf,hg, decide_true,
          Bool.true_and, ite_true, AlgCodec.parseCanonicalTask_result, hw,hs,
          AlgCode.marginMeshTask_result, marginMesh_eq, AlgCode.verifyRefinementTask_result,
          edgeListsTask_result, Literal.coefficientBoundsTask_result, checkTreeStoredTask_result, StoredBox.view,
          verifyCertificate, if_pos hm]
        split <;> simp_all [pairDimension] <;> rfl
  · have hbool : (decide (c.base.input = A06InputCodec.serialize I) &&
        decide (c.base.formatVersion = Cover.formatVersion ∧ c.base.generatorVersion = Cover.generatorVersion)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      unfold certificateMetadata at hm
      tauto
    simp only [certificateMetadata] at hm
    simp [verifyCertificateTask, verifyCertificate, certificateMetadata, equalListTask_result, hm]

/-- Native byte output is retained only after complete serialization, raw-byte parse,
    reserialization identity, and the full final certificate checker. -/
def packageCertificateTask (I : Input) (h : Valid I) (raw : List Nat)
    (gs : ConstraintArray I h) (H : Objective I h) (c : Certificate I h) : FinTask CappedResult := do
  let bytes ← Bytes.serializeEvidenceBytesTask c
  let parsed ← Bytes.parseEvidenceBytesTask (pairDimension I h) (constraintCount I h) bytes
  match parsed with
  | none => .done .implementationError
  | some d => do
      let replayBytes ← Bytes.serializeEvidenceBytesTask d
      let identical ← equalListTask bytes replayBytes
      if identical then do
        let checked ← verifyCertificateTask I h raw gs H d
        .step fun _ => .done (if checked then .certificate ⟨I,h,d,⟨bytes.toArray⟩⟩ else .implementationError)
      else .done .implementationError

theorem packageCertificateTask_result (I : Input) (h : Valid I) (raw : List Nat)
    (hraw : raw = A06InputCodec.serialize I)
    (gs : ConstraintArray I h) (H : Objective I h)
    (hgs : gs = ProjectSemantics.constraintArray I.design h.1)
    (hH : H = ConcreteCompiler.objective I.design h.1) (c : Certificate I h)
    (hc : verifyCertificate I h c = true) :
    (packageCertificateTask I h raw gs H c).result =
      .certificate ⟨I,h,c,Bytes.serializeEvidenceByteArray c⟩ := by
  simp [packageCertificateTask, Bytes.serializeEvidenceBytesTask_result,
    Bytes.parseEvidenceBytesTask_result, Bytes.parseEvidenceBytes_serialize, equalListTask_result,
    verifyCertificateTask_result I h raw hraw gs H hgs hH c, hc, Bytes.serializeEvidenceByteArray]

/-- Retains actual prepared codes, rather than submitting only endpoint claims. -/
def candidateCertificateTask (I : Input) (h : Valid I) (raw : List Nat) (s : Nat)
    (wr sr : AlgCode) (t : CoverTree (pairDimension I h) (constraintCount I h)) : FinTask (Certificate I h) := do
  let weight ← AlgCodec.serializeTask wr
  let sigma ← AlgCodec.serializeTask sr
  .step fun _ => .done ⟨makeCertificate raw s t,weight,sigma⟩

theorem candidateCertificateTask_result (I : Input) (h : Valid I) (s : Nat)
    (t : CoverTree (pairDimension I h) (constraintCount I h)) :
    (candidateCertificateTask I h (A06InputCodec.serialize I) s
      (preparedWeight I h s) (preparedSigma I h s) t).result = certificateAt I h s t := by
  simp [candidateCertificateTask, AlgCodec.serializeTask_result, certificateAt]

end Cover.A06

namespace Cover.A06
open FinTask

/-- The admitted-stage body consumes cached compiler data and retains the exact
    prepared codes used for the coefficients in the emitted evidence certificate. -/
def admittedStageCoreTask (I : Input) (h : Valid I) (raw : List Nat)
    (gs : ConstraintArray I h) (H : Objective I h) (s : Nat) : FinTask CappedAction := .step fun _ => do
  let margins ← preparedMarginsTask I h s
  let edges ← edgeListsTask I
  let coeff ← Literal.coefficientBoundsTask (alphabetSizes I) edges s
    margins.1.interval margins.2.interval
  let generated ← stageStoredTask coeff gs H (ConcreteCompiler.pairDimension_pos I.design h.1) s
  match generated with
  | .inconclusive => .done (.again (s+1))
  | .implementationError => .done (.stop .implementationError)
  | .success tree => do
      let candidate ← candidateCertificateTask I h raw s margins.1 margins.2 tree
      let packed ← packageCertificateTask I h raw gs H candidate
      .done (.stop packed)

def stageAction (I : Input) (h : Valid I) (s : Nat) : CappedAction :=
  match stage I h s with
  | .inconclusive => .again (s+1)
  | .implementationError => .stop .implementationError
  | .success tree => .stop (.certificate ⟨I,h,certificateAt I h s tree,
      Bytes.serializeEvidenceByteArray (certificateAt I h s tree)⟩)

theorem admittedStageCoreTask_result (I : Input) (h : Valid I) (raw : List Nat)
    (hraw : raw = A06InputCodec.serialize I) (gs : ConstraintArray I h) (H : Objective I h)
    (hgs : gs = ProjectSemantics.constraintArray I.design h.1)
    (hH : H = ConcreteCompiler.objective I.design h.1) (s : Nat) :
    (admittedStageCoreTask I h raw gs H s).result = stageAction I h s := by
  subst raw; subst gs; subst H
  simp only [admittedStageCoreTask, FinTask.result_step, FinTask.result_bindM,
    preparedMarginsTask_result, edgeListsTask_result, Literal.coefficientBoundsTask_result, prepared_coefficients, stageStoredTask_result_eq]
  rw [stageTask_result (coefficients I h)]
  rw [← stage]
  cases hs : stage I h s with
  | inconclusive => simp [stageAction, hs]
  | implementationError => simp [stageAction, hs]
  | success tree =>
    simp only [FinTask.result_bindM, candidateCertificateTask_result]
    rw [packageCertificateTask_result I h _ rfl _ _ rfl rfl _
      (successfulStage_certificate_verified I h s tree hs)]
    simp [stageAction,hs]

theorem stageAction_shape (I : Input) (h : Valid I) (s : Nat) :
    stageAction I h s = .again (s+1) ∨ ∃ result, stageAction I h s = .stop (.certificate result) := by
  cases hs : stage I h s with
  | inconclusive => exact Or.inl (by simp [stageAction,hs])
  | success tree => exact Or.inr ⟨⟨I,h,certificateAt I h s tree, Bytes.serializeEvidenceByteArray (certificateAt I h s tree)⟩,by simp [stageAction,hs]⟩
  | implementationError => exact False.elim (coverStage_no_implementationError _ _ _ _ _ hs)

theorem stageAction_checked (I : Input) (h : Valid I) (s : Nat) :
    Capped.ActionChecked Returned.Checked (stageAction I h s) := by
  unfold stageAction
  split
  · trivial
  · trivial
  · rename_i tree hs
    exact ⟨Bytes.parseEvidenceByteArray_serialize _, successfulStage_certificate_verified I h s tree hs⟩

end Cover.A06
