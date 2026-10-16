import Cover.A06Rates

open scoped Classical
namespace Cover.A06
open Gen.Conditioned Gen.Geometry Gen.ConditionedRates

variable (I : Input) (h : Valid I)

/-- Conditional statistical transfer with the actual computed cover threshold.
The full original block-product marginal laws, all-outcome/all-competitor fit
comparison, fixed target and deterministic errors remain explicit premises. -/
theorem conditioned_rate_stat_of_cover {w σ : ℝ}
    (hwd : I.weight.denotes w) (hσd : I.sigma.denotes σ)
    {Ω : Type*} [Fintype Ω] (O : Ext.ObservationExperiment (FiniteDesign.toBaseline I.design h.1).Edge ((FiniteDesign.toBaseline I.design h.1).Outcome (fun g => Fin (I.design.outputPred g+1))))
    (μ : Ext.FiniteLaw Ω) (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (θ : Ambient (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1)) (fit : Ω → Ambient (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1))
    (hθ : θ ∈ K (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ) (hfit : ∀ ω, fit ω ∈ K (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ)
    {δ τ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmiss : ‖Gen.Rates.stack (fun e => (O.law e).mass) - observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ‖ ≤ τ)
    (hopt : ∀ ω, ∀ ζ ∈ K (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) w σ,
      ‖observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) (fit ω) - Gen.Rates.stack (O.empirical (obs ω))‖ ≤
        ‖observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) ζ - Gen.Rates.stack (O.empirical (obs ω))‖ + ε) :
    1 - δ ≤ μ.prob (fun ω =>
      ‖observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) (fit ω) - observation (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) θ‖ ≤
        2 * (τ + Gen.Rates.samplingRadius O δ) + ε ∧
      distance (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) (fit ω) θ ≤ min (Gen.Constants.diameter (Fintype.card (FiniteDesign.toBaseline I.design h.1).Component) (I.design.rankPred+1) I.design.groups)
        (max (2 / kappa (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) w σ)
          (Gen.Constants.diameter (Fintype.card (FiniteDesign.toBaseline I.design h.1).Component) (I.design.rankPred+1) I.design.groups / (computedCoverDelta I h : ℝ)) *
            (2 * (τ + Gen.Rates.samplingRadius O δ) + ε)) ∧
      (2 * (τ + Gen.Rates.samplingRadius O δ) + ε < (computedCoverDelta I h : ℝ) →
        distance (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) (fit ω) θ ≤ min (Gen.Constants.diameter (Fintype.card (FiniteDesign.toBaseline I.design h.1).Component) (I.design.rankPred+1) I.design.groups)
          ((2 / kappa (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) w σ) * (2 * (τ + Gen.Rates.samplingRadius O δ) + ε)))) := by
  have hb := valid_denotes_bounds I h hwd hσd
  have hd : (0 : ℝ) < computedCoverDelta I h := by exact_mod_cast computedCoverDelta_pos I h
  simpa only [Fintype.card_fin] using literal_rate_stat (FiniteDesign.toBaseline I.design h.1) (fun g => Fin (I.design.outputPred g+1)) (I.design.rankPred+1) hb.1 hb.2.2.1 hd
    (computed_separation_baseline I h hwd hσd) O μ obs hIID θ fit hθ hfit hδ hδ1 hmiss hopt

end Cover.A06
