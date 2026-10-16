import Cover.FullRealBridge
import Cover.CompletenessBridge
import Gen.ConditionedRates

open scoped Classical
namespace Cover.ProjectSemantics
open Cover.FiniteDesign Cover.ConcreteCompiler

/-- Finite ordered constraint indexing, with no unchecked omission. -/
def constraintArray (I : Syntax) (h : Valid I) :
    Fin (ConcreteCompiler.constraints I h).length → PolyExpr (dimension I h + dimension I h) 3 :=
  (ConcreteCompiler.constraints I h).get

lemma constraintArray_nonnegative_iff (I : Syntax) (h : Valid I)
    (cs : Fin 3 → ℝ) (x : Fin (dimension I h + dimension I h) → ℝ) :
    (∀ i, 0 ≤ (constraintArray I h i).eval cs x) ↔
      Compiler.nonnegative (ConcreteCompiler.constraints I h) cs x := by
  constructor
  · intro hall p hp
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    simpa only [constraintArray, hi] using hall i
  · intro hall i
    exact hall _ (List.get_mem _ _)

/-- The actual A06 observation objective is strictly positive on every encoded
far point, from the accepted full-rank uniqueness theorem and exact positive R.
No supplied gap, minimizer, injectivity premise, or successful stage is used. -/
theorem objective_positive_on_feasible (I : Syntax) (h : Valid I)
    {w σ R : ℝ} (hw : 0 < w) (hσ : 0 < σ) (hR : 0 < R)
    (x : Fin (dimension I h + dimension I h) → ℝ)
    (hx : ∀ i, 0 ≤ (constraintArray I h i).eval (SquaredCompiler.coefficients w σ R) x) :
    0 < (objective I h).eval (SquaredCompiler.coefficients w σ R) x := by
  have he := (FullRealBridge.concrete_coverEncoding_iff_fullDistance I h w σ R hR.le x).mp
    ((constraintArray_nonnegative_iff I h _ x).mp hx)
  rw [coverObjective_eval]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  apply sub_ne_zero.mpr
  intro hobs
  have hz := (Gen.ConditionedRates.observation_eq_iff_distance_zero
    (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)
    hw hσ (Nat.succ_pos _) (expandLeft I h x) (expandRight I h x) he.1 he.2.1).mp hobs
  have hf := he.2.2
  change Gen.Rates.orbitDist (Γ := Gen.W (toBaseline I h) (I.rankPred+1))
    (expandLeft I h x) (expandRight I h x) = 0 at hz
  rw [hz] at hf
  exact not_le_of_gt hR hf

/-- Full-real checker soundness for the concrete compiler. Its proof does not use
project uniqueness, compactness, positive separation, or generator termination. -/
theorem compiledCertificate_separates (I : Syntax) (h : Valid I)
    {w σ R : ℝ} (hw : 0 ≤ w) (hR : 0 ≤ R)
    (cs : Fin 3 → QInterval)
    (hcs : ∀ i, (cs i).contains (SquaredCompiler.coefficients w σ R i))
    (k : Nat) (t : CoverTree (dimension I h + dimension I h) (ConcreteCompiler.constraints I h).length)
    (hc : checkTree cs (constraintArray I h) (objective I h) k (unitBox _) t = true)
    (θ η : Normalization.Full (toBaseline I h) I.outputPred I.rankPred)
    (hθ : θ ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ)
    (hη : η ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ)
    (hfar : R ≤ Gen.Rates.orbitDist (Γ := Gen.W (toBaseline I h) (I.rankPred+1)) θ η) :
    (dyadic k : ℝ) ≤
      ‖Gen.Geometry.observation (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) θ -
        Gen.Geometry.observation (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) η‖ := by
  let x := projectPair I h θ η
  have hx : (unitBox (dimension I h + dimension I h)).Contains x := by
    intro i
    simpa only [QInterval.contains, unitBox, Rat.cast_zero, Rat.cast_one, x, Set.mem_Icc] using
      projectPair_mem_unitBox I h hw θ η hθ hη i
  have hfeas : ∀ i, 0 ≤ (constraintArray I h i).eval (SquaredCompiler.coefficients w σ R) x := by
    rw [constraintArray_nonnegative_iff, FullRealBridge.concrete_coverEncoding_iff_fullDistance I h w σ R hR]
    simpa only [x, expandLeft_project I h θ η hθ.1, expandRight_project I h θ η hη.1] using
      And.intro hθ (And.intro hη hfar)
  have hsq := verifyCoverTree_sound cs (SquaredCompiler.coefficients w σ R)
    (constraintArray I h) (objective I h) k hcs t hc x hx hfeas
  rw [coverObjective_eval, show expandLeft I h x = θ from expandLeft_project I h θ η hθ.1,
    show expandRight I h x = η from expandRight_project I h θ η hη.1] at hsq
  have hd : (dyadic (2*k) : ℝ) = (dyadic k : ℝ)^2 := by
    simp only [dyadic, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]
    rw [mul_comm 2 k, pow_mul]
  rw [hd] at hsq
  exact (sq_le_sq₀ (by exact_mod_cast (dyadic_pos k).le) (norm_nonneg _)).mp hsq

/-- Every actual stage eventually succeeds once the concrete scalar preparation
is supplied. The only visible hypotheses are its true enclosure and convergence;
A06 positivity is proved above instead of assumed. -/
theorem actualStages_eventually_succeed (I : Syntax) (h : Valid I)
    {w σ R : ℝ} (hw : 0 < w) (hσ : 0 < σ) (hR : 0 < R)
    (cs : Nat → Fin 3 → QInterval)
    (hcs : ∀ s i, (cs s i).contains (SquaredCompiler.coefficients w σ R i))
    (hcw : ∀ δ : ℚ, 0 < δ → ∃ s₀ : Nat, ∀ s ≥ s₀, ∀ i, (cs s i).width ≤ δ) :
    ∃ s₀ : Nat, ∀ s ≥ s₀, ∃ t,
      coverStage cs (constraintArray I h) (objective I h) (pairDimension_pos I h) s = .success t := by
  apply coverStage_eventually_succeeds_of_refining_coefficients cs
    (SquaredCompiler.coefficients w σ R) (constraintArray I h) (objective I h)
    (pairDimension_pos I h) hcs hcw
  intro x hx hfeas
  exact objective_positive_on_feasible I h hw hσ hR x hfeas

end Cover.ProjectSemantics
