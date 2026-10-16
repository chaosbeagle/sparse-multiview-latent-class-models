import Cover.A06CappedReplay

namespace Cover.A06.Runtime
open FinTask

/-- Equality transports are proof-erased. Cached runtime n/j are used by every
    parser/generator; original dimension/count expressions occur only in types/proofs. -/
def alignCertificate (I : Input) (h : Valid I) {n j : Nat}
    (hn : n = pairDimension I h) (hj : j = constraintCount I h)
    (c : EvidenceCertificate n j) : Certificate I h := cast (by rw [hn,hj]) c

def verifyTask (I : Input) (raw : List Nat) (n j : Nat)
    (gs : Fin j → PolyExpr n 3) (H : PolyExpr n 3) (c : EvidenceCertificate n j) : FinTask Bool := do
  let inputMatch ← equalListTask c.base.input raw
  let versions ← .step fun _ => .done (decide (c.base.formatVersion = Cover.formatVersion ∧
    c.base.generatorVersion = Cover.generatorVersion))
  if inputMatch && versions then do
    let wp ← AlgCodec.parseCanonicalTask c.weightRefinement
    let sp ← AlgCodec.parseCanonicalTask c.sigmaRefinement
    match wp,sp with
    | some wr,some sr => do
        let mesh ← AlgCode.marginMeshTask c.base.precision
        let hw ← AlgCode.verifyRefinementTask I.weight wr mesh true
        let hs ← AlgCode.verifyRefinementTask I.sigma sr mesh true
        if hw && hs then do
          let edges ← edgeListsTask I
          let cs ← Literal.coefficientBoundsTask (alphabetSizes I) edges
            c.base.precision wr.interval sr.interval
          checkTreeStoredTask (n:=n) (j:=j) cs gs H c.base.k .unit c.base.tree
        else .done false
    | _,_ => .done false
  else .done false

 theorem verifyTask_actual (I : Input) (h : Valid I) (raw : List Nat)
    (gs : ConstraintArray I h) (H : Objective I h) (c : Certificate I h) :
    verifyTask I raw (pairDimension I h) (constraintCount I h) gs H c =
      verifyCertificateTask I h raw gs H c := rfl

 def packageTask (I : Input) (h : Valid I) (raw : List Nat) (n j : Nat)
    (hn : n = pairDimension I h) (hj : j = constraintCount I h)
    (gs : Fin j → PolyExpr n 3) (H : PolyExpr n 3) (c : EvidenceCertificate n j) : FinTask CappedResult := do
  let bytes ← Bytes.serializeEvidenceBytesTask c
  let parsed ← Bytes.parseEvidenceBytesTask n j bytes
  match parsed with
  | none => .done .implementationError
  | some d => do
      let replay ← Bytes.serializeEvidenceBytesTask d
      let identical ← equalListTask bytes replay
      if identical then do
        let checked ← verifyTask I raw n j gs H d
        .step fun _ => .done (if checked then .certificate ⟨I,h,alignCertificate I h hn hj d,⟨bytes.toArray⟩⟩ else .implementationError)
      else .done .implementationError

 theorem packageTask_actual (I : Input) (h : Valid I) (raw : List Nat)
    (gs : ConstraintArray I h) (H : Objective I h) (c : Certificate I h) :
    (packageTask I h raw (pairDimension I h) (constraintCount I h) rfl rfl gs H c).result =
      (packageCertificateTask I h raw gs H c).result := by
  simp [packageTask, packageCertificateTask, Bytes.serializeEvidenceBytesTask_result,
    Bytes.parseEvidenceBytesTask_result, Bytes.parseEvidenceBytes_serialize, equalListTask_result,
    verifyTask_actual, alignCertificate]

 def candidateTask (raw : List Nat) (s : Nat) (wr sr : AlgCode) (tree : CoverTree n j) :
    FinTask (EvidenceCertificate n j) := do
  let weight ← AlgCodec.serializeTask wr
  let sigma ← AlgCodec.serializeTask sr
  .step fun _ => .done ⟨makeCertificate raw s tree,weight,sigma⟩

 def stageCoreTask (I : Input) (h : Valid I) (raw : List Nat) (n j : Nat)
    (hn : n = pairDimension I h) (hj : j = constraintCount I h)
    (gs : Fin j → PolyExpr n 3) (H : PolyExpr n 3) (s : Nat) : FinTask CappedAction := .step fun _ => do
  let margins ← preparedMarginsTask I h s
  let edges ← edgeListsTask I
  let coeff ← Literal.coefficientBoundsTask (alphabetSizes I) edges s margins.1.interval margins.2.interval
  let generated ← stageStoredTask (n:=n) (j:=j) coeff gs H (by rw [hn]; exact ConcreteCompiler.pairDimension_pos I.design h.1) s
  match generated with
  | .inconclusive => .done (.again (s+1))
  | .implementationError => .done (.stop .implementationError)
  | .success tree => do
      let c ← candidateTask raw s margins.1 margins.2 tree
      let packed ← packageTask I h raw n j hn hj gs H c
      .done (.stop packed)

 theorem stageCoreTask_actual (I : Input) (h : Valid I) (raw : List Nat)
    (gs : ConstraintArray I h) (H : Objective I h) (s : Nat) :
    (stageCoreTask I h raw (pairDimension I h) (constraintCount I h) rfl rfl gs H s).result =
      (admittedStageCoreTask I h raw gs H s).result := by
  simp only [stageCoreTask, admittedStageCoreTask, FinTask.result_step, FinTask.result_bindM]
  split
  · simp_all
  · simp_all
  · simp_all only
    simp only [FinTask.result_bindM, candidateTask, candidateCertificateTask,
      AlgCodec.serializeTask_result, FinTask.result_step, FinTask.result_done]
    rw [packageTask_actual]

end Cover.A06.Runtime
