import Cover.A06Program
import Cover.ScalarBaselineBridge

open scoped Classical
namespace Cover.A06
open Gen.Conditioned Gen.Geometry Gen.ConditionedRates

lemma valid_denotes_bounds (I : Input) (h : Valid I) {w σ : ℝ}
    (hwd : I.weight.denotes w) (hσd : I.sigma.denotes σ) :
    0 < w ∧ w ≤ 1/(I.design.rankPred+1 : ℝ) ∧ 0 < σ ∧ σ ≤ 1 := by
  obtain ⟨hwc,hσc,w',σ',hwd',hσd',hw,hwu,hσ,hσu⟩ := Margins.valid_iff.mp h.2
  have hew := (AlgCode.validAlgBracket_denotes_unique I.weight hwc).unique hwd hwd'
  have heσ := (AlgCode.validAlgBracket_denotes_unique I.sigma hσc).unique hσd hσd'
  subst w'; subst σ'
  exact ⟨hw, by simpa using hwu, hσ, hσu⟩

lemma radius_eq_baseline (I : Input) (h : Valid I) (w σ : ℝ) :
    (Literal.R (alphabetSizes I) (edgeLists I)).eval w σ =
    radius (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1))
      (kappa (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) w σ) :=
  ScalarBaselineBridge.R_eq I.design h.1 w σ

lemma computed_separation_baseline (I : Input) (h : Valid I) {w σ : ℝ}
    (hwd : I.weight.denotes w) (hσd : I.sigma.denotes σ) :
    ∀ θ ∈ K (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ,
    ∀ η ∈ K (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ,
    radius (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1))
      (kappa (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) w σ) ≤
      distance (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ η →
    (computedCoverDelta I h : ℝ) ≤
      ‖observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ -
       observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) η‖ := by
  intro θ hθ η hη hf
  apply computedCoverDelta_separates I h hwd hσd θ η hθ hη
  rw [radius_eq_baseline I h]
  exact hf

/-- Literal global inverse using the actually computed positive cover threshold. -/
theorem conditioned_global_inverse_of_cover (I : Input) (h : Valid I) {w σ : ℝ}
    (hwd : I.weight.denotes w) (hσd : I.sigma.denotes σ)
    (θ η : Normalization.Full (FiniteDesign.toBaseline I.design h.1) I.design.outputPred I.design.rankPred)
    (hθ : θ ∈ K (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ)
    (hη : η ∈ K (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ) :
    distance (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ η ≤
    max (2 / kappa (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) w σ)
      (Gen.Constants.diameter (Fintype.card (FiniteDesign.toBaseline I.design h.1).Component)
        (I.design.rankPred+1) I.design.groups / (computedCoverDelta I h : ℝ)) *
      ‖observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ -
       observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) η‖ := by
  have hb := valid_denotes_bounds I h hwd hσd
  have hd : (0 : ℝ) < computedCoverDelta I h := by exact_mod_cast computedCoverDelta_pos I h
  simpa only [Fintype.card_fin] using literal_global_inverse
    (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1)
    hb.1 hb.2.2.1 hd (computed_separation_baseline I h hwd hσd) θ η hθ hη

/-- Strict output-gap localization keeps the sharper coefficient 2/κ. -/
theorem conditioned_strict_inverse_of_cover (I : Input) (h : Valid I) {w σ : ℝ}
    (hwd : I.weight.denotes w) (hσd : I.sigma.denotes σ)
    (θ η : Normalization.Full (FiniteDesign.toBaseline I.design h.1) I.design.outputPred I.design.rankPred)
    (hθ : θ ∈ K (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ)
    (hη : η ∈ K (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ)
    (hsmall : ‖observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ -
       observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) η‖ <
      (computedCoverDelta I h : ℝ)) :
    distance (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ η ≤
      (2 / kappa (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) w σ) *
      ‖observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ -
       observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) η‖ := by
  have hb := valid_denotes_bounds I h hwd hσd
  apply literal_local_inverse (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1))
    (I.design.rankPred+1) hb.1 hb.2.2.1 η θ hη hθ
  exact (Gen.Rates.strict_localization (computed_separation_baseline I h hwd hσd θ hθ η hη) hsmall).le

end Cover.A06
