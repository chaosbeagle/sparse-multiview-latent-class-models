import Ext.Experiments
import Ext.ObservationBounds

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open scoped BigOperators Classical
noncomputable section
namespace Ext

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)]
variable {A : Type*} [Fintype A]
local instance : DecidableEq D.Edge := Classical.decEq _

def confidenceDataOfSample (B : Misspecification2 D Y) (anchors : A → Anchor2 Y)
    (nO : D.Edge → ℕ) (hnO : ∀ e, 0 < nO e)
    (nG : A → Bool → ℕ) (hnG : ∀ a t, 0 < nG a t)
    (ω : GoldSpace (modelGoldExperiment D Y B.truth anchors nG hnG) ×
      ObservationSpace (B.observationExperiment nO hnO)) : ConfidenceData2 D Y B anchors where
  obsN := nO
  obsN_pos := hnO
  goldN := nG
  goldN_pos := hnG
  observations := ω.2
  gold := ω.1

/-- B-T2: actual IID gold/observation blocks imply full-real confidence-set coverage.
    Cross-block and gold/observation coupling are completely unrestricted. -/
theorem truth_in_confidence_set [Nonempty A]
    (B : Misspecification2 D Y) (anchors : A → Anchor2 Y)
    (nO : D.Edge → ℕ) (hnO : ∀ e, 0 < nO e)
    (nG : A → Bool → ℕ) (hnG : ∀ a t, 0 < nG a t)
    (μ : JointSampleLaw (modelGoldExperiment D Y B.truth anchors nG hnG)
      (B.observationExperiment nO hnO))
    {δO δG : ℝ} (hδO : 0 < δO) (hδO1 : δO < 1)
    (hδG : 0 < δG) (hδG1 : δG < 1) (hδsum : δO + δG < 1) :
    1 - δO - δG ≤ μ.law.prob (fun ω => B.truth ∈
      (confidenceDataOfSample D Y B anchors nO hnO nG hnG ω).confidenceSet δO δG) := by
  letI : Nonempty D.Edge := D.edge_nonempty
  let data := confidenceDataOfSample D Y B anchors nO hnO nG hnG
  have ho : 1 - δO ≤ μ.law.prob (fun ω => (data ω).observationGood δO) := by
    simpa only [data, confidenceDataOfSample, ConfidenceData2.observationGood,
      ConfidenceData2.empirical, ConfidenceData2.observationRadius, ConfidenceData2.cellRadius,
      ConfidenceData2.totalCells, ObservationExperiment.tvRadius, ObservationExperiment.cellRadius,
      ObservationExperiment.totalCells, Misspecification2.observationExperiment] using
      edge_tv_family_bound (B.observationExperiment nO hnO) μ.law Prod.snd
        μ.observation_iid hδO hδO1
  have hg : 1 - δG ≤ μ.law.prob (fun ω => (data ω).goldGood δG) := by
    simpa only [data, confidenceDataOfSample, ConfidenceData2.goldGood,
      ConfidenceData2.estimate, ConfidenceData2.goldRadius, confidenceRadius,
      GoldExperiment.varianceProxy, GoldExperiment.direction, modelGoldExperiment,
      Anchor2.direction] using
      gold_difference_band (modelGoldExperiment D Y B.truth anchors nG hnG) μ.law
        Prod.fst μ.gold_iid hδG hδG1
  have hinter := μ.law.prob_inter_ge
    (fun ω => (data ω).observationGood δO) (fun ω => (data ω).goldGood δG)
  have hgood : 1 - δO - δG ≤ μ.law.prob (fun ω =>
      (data ω).observationGood δO ∧ (data ω).goldGood δG) := by linarith
  exact hgood.trans (μ.law.prob_mono (fun ω hω =>
    (data ω).truth_mem_of_good δO δG hω.1 hω.2))

/-- The same parameter-in-set event covers every predeclared probability functional.
    Infima and suprema are over the full real parameter space, without attainment. -/
theorem functional_interval_coverage [Nonempty A]
    (B : Misspecification2 D Y) (anchors : A → Anchor2 Y)
    (nO : D.Edge → ℕ) (hnO : ∀ e, 0 < nO e)
    (nG : A → Bool → ℕ) (hnG : ∀ a t, 0 < nG a t)
    (μ : JointSampleLaw (modelGoldExperiment D Y B.truth anchors nG hnG)
      (B.observationExperiment nO hnO))
    {δO δG : ℝ} (hδO : 0 < δO) (hδO1 : δO < 1)
    (hδG : 0 < δG) (hδG1 : δG < 1) (hδsum : δO + δG < 1)
    {I : Type*} [Fintype I] (f : I → ProbabilityFunctional (Theta2 D Y)) :
    1 - δO - δG ≤ μ.law.prob (fun ω => ∀ i,
      (f i).lower ((confidenceDataOfSample D Y B anchors nO hnO nG hnG ω).confidenceSet δO δG) ≤
        (f i).value B.truth ∧ (f i).value B.truth ≤
      (f i).upper ((confidenceDataOfSample D Y B anchors nO hnO nG hnG ω).confidenceSet δO δG)) := by
  apply (truth_in_confidence_set D Y B anchors nO hnO nG hnG μ
    hδO hδO1 hδG hδG1 hδsum).trans (μ.law.prob_mono ?_)
  intro ω hω
  exact ProbabilityFunctional.simultaneous_intervals f _ hω

/-- A separately certified outer interval is valid only when it encloses every feasible real point. -/
theorem functional_outer_coverage [Nonempty A]
    (B : Misspecification2 D Y) (anchors : A → Anchor2 Y)
    (nO : D.Edge → ℕ) (hnO : ∀ e, 0 < nO e)
    (nG : A → Bool → ℕ) (hnG : ∀ a t, 0 < nG a t)
    (μ : JointSampleLaw (modelGoldExperiment D Y B.truth anchors nG hnG)
      (B.observationExperiment nO hnO))
    {δO δG : ℝ} (hδO : 0 < δO) (hδO1 : δO < 1)
    (hδG : 0 < δG) (hδG1 : δG < 1) (hδsum : δO + δG < 1)
    {I : Type*} [Fintype I] (f : I → ProbabilityFunctional (Theta2 D Y))
    (L U : I → (GoldSpace (modelGoldExperiment D Y B.truth anchors nG hnG) ×
      ObservationSpace (B.observationExperiment nO hnO)) → ℝ)
    (hcert : ∀ i ω θ,
      θ ∈ (confidenceDataOfSample D Y B anchors nO hnO nG hnG ω).confidenceSet δO δG →
        L i ω ≤ (f i).value θ ∧ (f i).value θ ≤ U i ω) :
    1 - δO - δG ≤ μ.law.prob (fun ω => ∀ i, L i ω ≤ (f i).value B.truth ∧
      (f i).value B.truth ≤ U i ω) := by
  apply (truth_in_confidence_set D Y B anchors nO hnO nG hnG μ
    hδO hδO1 hδG hδG1 hδsum).trans (μ.law.prob_mono ?_)
  intro ω hω i
  exact hcert i ω B.truth hω

end Ext
