import Cover.A06Input
import Cover.ProjectSemantics
import Cover.ScalarCoefficients

namespace Cover.A06


def pairDimension (I : Input) (h : Valid I) : Nat :=
  ConcreteCompiler.dimension I.design h.1 + ConcreteCompiler.dimension I.design h.1

def constraintCount (I : Input) (h : Valid I) : Nat := (ConcreteCompiler.constraints I.design h.1).length

def coefficients (I : Input) (h : Valid I) : Nat → Fin 3 → QInterval :=
  validatedScalarCoefficients (alphabetSizes I) (edgeLists I)
    (I.design.rankPred+1) I.weight I.sigma h.2

/-- Exact prescribed stage: k=s, coefficient precision=s, depth=N*s, fixed tests,
cyclic splitting, complete children, and mandatory replay. -/
def stage (I : Input) (h : Valid I) (s : Nat) : StageResult (pairDimension I h) (constraintCount I h) :=
  coverStage (coefficients I h) (ProjectSemantics.constraintArray I.design h.1)
    (ConcreteCompiler.objective I.design h.1) (ConcreteCompiler.pairDimension_pos I.design h.1) s

/-- Universal A06 actual-stage success. Input hypotheses are exactly the finite
validated design and encoded margins; every gap/compactness/compiler/scalar fact
is derived rather than accepted as a runtime or theorem input. -/
theorem coverStage_eventually_succeeds (I : Input) (h : Valid I) :
    ∃ s₀ : Nat, ∀ s ≥ s₀, ∃ t, stage I h s = .success t := by
  obtain ⟨hwc,hσc,w,σ,hwd,hσd,hw,hwu,hσ,hσu⟩ := Margins.valid_iff.mp h.2
  have hR := (Literal.exactR_properties (alphabetSizes I) (alphabetSizes_pos I)
    (edgeLists_nonempty I h) hw hσ).1
  apply ProjectSemantics.actualStages_eventually_succeed I.design h.1 hw hσ hR
    (coefficients I h)
  · intro s i
    exact validatedScalarCoefficients_sound (alphabetSizes I) (alphabetSizes_pos I)
      (edgeLists_nonempty I h) _ I.weight I.sigma h.2 hwd hσd s i
  · exact validatedScalarCoefficients_widths_refine (alphabetSizes I) (alphabetSizes_pos I)
      (edgeLists_nonempty I h) _ I.weight I.sigma h.2

/-- A finite rational test of the actual Stage result. -/
def stageSucceeded (I : Input) (h : Valid I) (s : Nat) : Bool :=
  match stage I h s with
  | .success _ => true
  | _ => false

theorem exists_successful_stage (I : Input) (h : Valid I) :
    ∃ s, stageSucceeded I h s = true := by
  obtain ⟨s₀,hs₀⟩ := coverStage_eventually_succeeds I h
  obtain ⟨t,ht⟩ := hs₀ s₀ le_rfl
  exact ⟨s₀, by simp [stageSucceeded, ht]⟩

/-- Executable unbounded enumeration of natural stages. Nat.find evaluates the
finite decidable stage predicate; it does not choose a semantic certificate. -/
def firstSuccessfulStage (I : Input) (h : Valid I) : Nat :=
  Nat.find (exists_successful_stage I h)

 theorem stage_no_implementationError (I : Input) (h : Valid I) (s : Nat) :
    stage I h s ≠ .implementationError :=
  coverStage_no_implementationError _ _ _ _ _

 theorem firstSuccessfulStage_minimal (I : Input) (h : Valid I) (s : Nat)
    (hs : s < firstSuccessfulStage I h) : stage I h s = .inconclusive := by
  cases ho : stage I h s with
  | inconclusive => rfl
  | implementationError => exact False.elim (stage_no_implementationError I h s ho)
  | success t =>
    have hc : stageSucceeded I h s = true := by simp [stageSucceeded, ho]
    have hm : firstSuccessfulStage I h ≤ s := Nat.find_min' (exists_successful_stage I h) hc
    omega


def returnedTree (I : Input) (h : Valid I) :
    CoverTree (pairDimension I h) (constraintCount I h) :=
  match hs : stage I h (firstSuccessfulStage I h) with
  | .success t => t
  | .inconclusive => False.elim (by
      have hf : stageSucceeded I h (firstSuccessfulStage I h) = true :=
        Nat.find_spec (exists_successful_stage I h)
      simp [stageSucceeded, hs] at hf)
  | .implementationError => False.elim (by
      have hf : stageSucceeded I h (firstSuccessfulStage I h) = true :=
        Nat.find_spec (exists_successful_stage I h)
      simp [stageSucceeded, hs] at hf)

 theorem returnedTree_is_actual_output (I : Input) (h : Valid I) :
    stage I h (firstSuccessfulStage I h) = .success (returnedTree I h) := by
  unfold returnedTree
  split
  · assumption
  · have hf : stageSucceeded I h (firstSuccessfulStage I h) = true :=
      Nat.find_spec (exists_successful_stage I h)
    simp_all [stageSucceeded]
  · have hf : stageSucceeded I h (firstSuccessfulStage I h) = true :=
      Nat.find_spec (exists_successful_stage I h)
    simp_all [stageSucceeded]

 theorem returnedTree_replays (I : Input) (h : Valid I) :
    checkTree (coefficients I h (firstSuccessfulStage I h))
      (ProjectSemantics.constraintArray I.design h.1) (ConcreteCompiler.objective I.design h.1)
      (firstSuccessfulStage I h) (unitBox _) (returnedTree I h) = true :=
  coverStage_success_checked _ _ _ _ _ _ (returnedTree_is_actual_output I h)

def computedCoverDelta (I : Input) (h : Valid I) : ℚ := dyadic (firstSuccessfulStage I h)

theorem computedCoverDelta_pos (I : Input) (h : Valid I) : 0 < computedCoverDelta I h :=
  dyadic_pos _

/-- The number is returned by the rational search, and separates every real K pair.
No exact minimum, minimizer, maximal dyadic, or emptiness decision is claimed. -/
theorem computedCoverDelta_separates (I : Input) (h : Valid I)
    {w σ : ℝ} (hwd : I.weight.denotes w) (hσd : I.sigma.denotes σ)
    (θ η : Normalization.Full (FiniteDesign.toBaseline I.design h.1) I.design.outputPred I.design.rankPred)
    (hθ : θ ∈ Gen.Conditioned.K (FiniteDesign.toBaseline I.design h.1)
      (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ)
    (hη : η ∈ Gen.Conditioned.K (FiniteDesign.toBaseline I.design h.1)
      (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ)
    (hfar : (Literal.R (alphabetSizes I) (edgeLists I)).eval w σ ≤
      Gen.ConditionedRates.distance (FiniteDesign.toBaseline I.design h.1)
        (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ η) :
    (computedCoverDelta I h : ℝ) ≤
      ‖Gen.Geometry.observation (FiniteDesign.toBaseline I.design h.1)
        (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ -
       Gen.Geometry.observation (FiniteDesign.toBaseline I.design h.1)
        (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) η‖ := by
  obtain ⟨hwc,hσc,w',σ',hwd',hσd',hw,hwu,hσ,hσu⟩ := Margins.valid_iff.mp h.2
  have hew : w = w' := (AlgCode.validAlgBracket_denotes_unique I.weight hwc).unique hwd hwd'
  have heσ : σ = σ' := (AlgCode.validAlgBracket_denotes_unique I.sigma hσc).unique hσd hσd'
  subst w'; subst σ'
  have hR := (Literal.exactR_properties (alphabetSizes I) (alphabetSizes_pos I)
    (edgeLists_nonempty I h) hw hσ).1
  exact ProjectSemantics.compiledCertificate_separates I.design h.1 hw.le hR.le
    (coefficients I h (firstSuccessfulStage I h))
    (fun i => validatedScalarCoefficients_sound (alphabetSizes I) (alphabetSizes_pos I)
      (edgeLists_nonempty I h) _ I.weight I.sigma h.2 hwd hσd _ i)
    (firstSuccessfulStage I h) (returnedTree I h) (returnedTree_replays I h) θ η hθ hη hfar

end Cover.A06
