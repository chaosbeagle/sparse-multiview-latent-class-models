import Cover.A06Rates
import Cover.A06InputCodec
import Cover.AlgebraicEvidenceExecution
import Cover.EvidenceCertificate

namespace Cover.A06

abbrev Certificate (I : Input) (h : Valid I) :=
  EvidenceCertificate (pairDimension I h) (constraintCount I h)

def certificateMetadata (I : Input) (h : Valid I) (c : Certificate I h) : Prop :=
  c.base.input = A06InputCodec.serialize I ∧ c.base.formatVersion = Cover.formatVersion ∧
    c.base.generatorVersion = Cover.generatorVersion
instance (I : Input) (h : Valid I) (c : Certificate I h) : Decidable (certificateMetadata I h c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Full finite-data checker: exact input/version binding, canonical evidence decode,
original-polynomial refinement verification, regenerated literals/compiler, all-box replay. -/
def verifyCertificate (I : Input) (h : Valid I) (c : Certificate I h) : Bool :=
  if certificateMetadata I h c then
    match AlgCodec.parseCanonical c.weightRefinement, AlgCodec.parseCanonical c.sigmaRefinement with
    | some wr, some sr =>
      AlgCode.verifyRefinement I.weight wr (DyadicSqrt.mesh c.base.precision) true &&
      AlgCode.verifyRefinement I.sigma sr (DyadicSqrt.mesh c.base.precision) true &&
      checkTree (Literal.coefficientBounds (alphabetSizes I) (edgeLists I) c.base.precision wr.interval sr.interval)
        (ProjectSemantics.constraintArray I.design h.1) (ConcreteCompiler.objective I.design h.1)
        c.base.k (unitBox _) c.base.tree
    | _, _ => false
  else false

lemma verifyCertificate_details (I : Input) (h : Valid I) (c : Certificate I h)
    (hc : verifyCertificate I h c = true) :
    certificateMetadata I h c ∧ ∃ wr sr,
      AlgCodec.parseCanonical c.weightRefinement = some wr ∧
      AlgCodec.parseCanonical c.sigmaRefinement = some sr ∧
      AlgCode.verifyRefinement I.weight wr (DyadicSqrt.mesh c.base.precision) true = true ∧
      AlgCode.verifyRefinement I.sigma sr (DyadicSqrt.mesh c.base.precision) true = true ∧
      checkTree (Literal.coefficientBounds (alphabetSizes I) (edgeLists I) c.base.precision wr.interval sr.interval)
        (ProjectSemantics.constraintArray I.design h.1) (ConcreteCompiler.objective I.design h.1)
        c.base.k (unitBox _) c.base.tree = true := by
  unfold verifyCertificate at hc
  split at hc
  · rename_i hm
    cases hw : AlgCodec.parseCanonical c.weightRefinement with
    | none => simp [hw] at hc
    | some wr =>
      cases hs : AlgCodec.parseCanonical c.sigmaRefinement with
      | none => simp [hw,hs] at hc
      | some sr =>
        simp only [hw,hs,Bool.and_eq_true] at hc
        exact ⟨hm,wr,sr,rfl,rfl,hc.1.1,hc.1.2,hc.2⟩
  · contradiction

lemma verifiedRefinements_coefficients_sound (I : Input) (h : Valid I)
    {w σ : ℝ} (hwd : I.weight.denotes w) (hσd : I.sigma.denotes σ)
    (s : Nat) (wr sr : AlgCode)
    (hwr : AlgCode.verifyRefinement I.weight wr (DyadicSqrt.mesh s) true = true)
    (hsr : AlgCode.verifyRefinement I.sigma sr (DyadicSqrt.mesh s) true = true)
    (i : Fin 3) :
    (Literal.coefficientBounds (alphabetSizes I) (edgeLists I) s wr.interval sr.interval i).contains
      (SquaredCompiler.coefficients w σ ((Literal.R (alphabetSizes I) (edgeLists I)).eval w σ) i) := by
  have hw := AlgCode.verifyRefinement_sound hwd hwr
  have hs := AlgCode.verifyRefinement_sound hσd hsr
  have hdef := Literal.coefficientBounds_defined (alphabetSizes I) (alphabetSizes_pos I)
    (edgeLists_nonempty I h) s wr.interval sr.interval (AlgCode.valid_interval hw.2.1)
    (AlgCode.valid_interval hs.2.1) (hw.2.2.2.2 rfl) (hs.2.2.2.2 rfl)
    (AlgCode.denotes_contains hs.2.2.1) (Margins.sigma_le_one_of_denotes h.2 hσd)
    hs.2.2.2.1 i
  have hsound := (Literal.coefficientSyntax (alphabetSizes I) (edgeLists I) i).evalScalarBounds_sound
    (AlgCode.denotes_contains hw.2.2.1) (AlgCode.denotes_contains hs.2.2.1) hdef
  have he := congrFun (Literal.coefficientSyntax_eval (alphabetSizes I) (edgeLists I) w σ) i
  rw [he] at hsound
  exact hsound

/-- Acceptance alone proves full-real separation. No generator correctness,
project injectivity, compactness or termination premise occurs in this theorem. -/
theorem verifyCoverCertificate_sound (I : Input) (h : Valid I) (c : Certificate I h)
    (hc : verifyCertificate I h c = true)
    {w σ : ℝ} (hwd : I.weight.denotes w) (hσd : I.sigma.denotes σ) :
    (0 < dyadic c.base.k) ∧
    ∀ θ ∈ Gen.Conditioned.K (FiniteDesign.toBaseline I.design h.1)
      (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ,
    ∀ η ∈ Gen.Conditioned.K (FiniteDesign.toBaseline I.design h.1)
      (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ,
    (Literal.R (alphabetSizes I) (edgeLists I)).eval w σ ≤
      Gen.ConditionedRates.distance (FiniteDesign.toBaseline I.design h.1)
        (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ η →
    (dyadic c.base.k : ℝ) ≤
      ‖Gen.Geometry.observation (FiniteDesign.toBaseline I.design h.1)
        (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ -
       Gen.Geometry.observation (FiniteDesign.toBaseline I.design h.1)
        (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) η‖ := by
  obtain ⟨hm,wr,sr,hwp,hsp,hwr,hsr,hcheck⟩ := verifyCertificate_details I h c hc
  have hb := valid_denotes_bounds I h hwd hσd
  have hR := (Literal.exactR_properties (alphabetSizes I) (alphabetSizes_pos I)
    (edgeLists_nonempty I h) hb.1 hb.2.2.1).1
  refine ⟨dyadic_pos _, ?_⟩
  intro θ hθ η hη hfar
  exact ProjectSemantics.compiledCertificate_separates I.design h.1 hb.1.le hR.le _
    (verifiedRefinements_coefficients_sound I h hwd hσd c.base.precision wr sr hwr hsr)
    c.base.k c.base.tree hcheck θ η hθ hη hfar

/-- Actual prepared code, retained in the exported certificate as independently
checkable refinement evidence rather than only as claimed endpoints. -/
def preparedWeight (I : Input) (h : Valid I) (s : Nat) : AlgCode :=
  AlgCode.prepareMargin I.weight (Margins.valid_codes h.2).1 (Margins.valid_positive_comparisons h.2).1 s

def preparedSigma (I : Input) (h : Valid I) (s : Nat) : AlgCode :=
  AlgCode.prepareMargin I.sigma (Margins.valid_codes h.2).2 (Margins.valid_positive_comparisons h.2).2 s

lemma marginMesh_eq (s : Nat) : AlgCode.marginMesh s = DyadicSqrt.mesh s := by
  simp [AlgCode.marginMesh,DyadicSqrt.mesh,DyadicSqrt.scale,one_div]

lemma preparedWeight_valid (I : Input) (h : Valid I) (s : Nat) : (preparedWeight I h s).valid := by
  obtain ⟨w,hw,_⟩ := AlgCode.validAlgBracket_denotes_unique I.weight (Margins.valid_codes h.2).1
  exact (AlgCode.prepareMargin_sound (Margins.valid_codes h.2).1 hw _ s).1
lemma preparedSigma_valid (I : Input) (h : Valid I) (s : Nat) : (preparedSigma I h s).valid := by
  obtain ⟨σ,hσ,_⟩ := AlgCode.validAlgBracket_denotes_unique I.sigma (Margins.valid_codes h.2).2
  exact (AlgCode.prepareMargin_sound (Margins.valid_codes h.2).2 hσ _ s).1

lemma prepared_coefficients (I : Input) (h : Valid I) (s : Nat) :
    Literal.coefficientBounds (alphabetSizes I) (edgeLists I) s
      (preparedWeight I h s).interval (preparedSigma I h s).interval = coefficients I h s := by
  simp only [preparedWeight,preparedSigma,AlgCode.prepareMargin,coefficients,
    validatedScalarCoefficients,scalarCoefficients,AlgCode.preparedBracket,marginMesh_eq]

/-- Concrete certificate generated at a successful stage. -/
def certificateAt (I : Input) (h : Valid I) (s : Nat)
    (t : CoverTree (pairDimension I h) (constraintCount I h)) : Certificate I h :=
  ⟨makeCertificate (A06InputCodec.serialize I) s t,
    AlgCodec.serialize (preparedWeight I h s), AlgCodec.serialize (preparedSigma I h s)⟩

theorem successfulStage_certificate_verified (I : Input) (h : Valid I) (s : Nat)
    (t : CoverTree (pairDimension I h) (constraintCount I h)) (hs : stage I h s = .success t) :
    verifyCertificate I h (certificateAt I h s t) = true := by
  have hw := AlgCode.prepareMargin_verified (Margins.valid_codes h.2).1 (Margins.valid_positive_comparisons h.2).1 s
  have hσ := AlgCode.prepareMargin_verified (Margins.valid_codes h.2).2 (Margins.valid_positive_comparisons h.2).2 s
  rw [marginMesh_eq] at hw hσ
  have hc := coverStage_success_checked _ _ _ _ _ _ hs
  simp only [verifyCertificate,certificateAt,certificateMetadata,makeCertificate, and_self,↓reduceIte,
    AlgCodec.parseCanonical_roundtrip (preparedWeight_valid I h s),
    AlgCodec.parseCanonical_roundtrip (preparedSigma_valid I h s)]
  have hwp : AlgCode.verifyRefinement I.weight (preparedWeight I h s) (DyadicSqrt.mesh s) true = true := hw
  have hsp : AlgCode.verifyRefinement I.sigma (preparedSigma I h s) (DyadicSqrt.mesh s) true = true := hσ
  rw [hwp,hsp,prepared_coefficients]
  exact hc

def computedCertificate (I : Input) (h : Valid I) : Certificate I h :=
  certificateAt I h (firstSuccessfulStage I h) (returnedTree I h)

theorem computedCertificate_verified (I : Input) (h : Valid I) :
    verifyCertificate I h (computedCertificate I h) = true :=
  successfulStage_certificate_verified I h _ _ (returnedTree_is_actual_output I h)

end Cover.A06
