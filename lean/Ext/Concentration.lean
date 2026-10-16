import Ext.Core
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory
noncomputable section
namespace Ext
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def asPMF (μ : FiniteLaw Ω) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (μ.mass ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => μ.nonneg ω), μ.total]
    simp)

@[simp] lemma asPMF_apply (μ : FiniteLaw Ω) (ω : Ω) :
    μ.asPMF ω = ENNReal.ofReal (μ.mass ω) := rfl

def asMeasure [MeasurableSpace Ω] (μ : FiniteLaw Ω) : Measure Ω := μ.asPMF.toMeasure

instance asMeasure_probability [MeasurableSpace Ω] (μ : FiniteLaw Ω) :
    IsProbabilityMeasure μ.asMeasure := PMF.toMeasure.isProbabilityMeasure _

lemma asMeasure_apply [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : FiniteLaw Ω) (S : Set Ω) :
    μ.asMeasure S = ENNReal.ofReal (μ.prob (fun ω => ω ∈ S)) := by
  classical
  rw [asMeasure, PMF.toMeasure_apply_fintype, prob,
    ENNReal.ofReal_sum_of_nonneg (by intro ω _; split_ifs; exact μ.nonneg ω; exact le_rfl)]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω ∈ S <;> simp [Set.indicator_apply, h]

lemma asMeasure_real [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : FiniteLaw Ω) (S : Set Ω) :
    μ.asMeasure.real S = μ.prob (fun ω => ω ∈ S) := by
  rw [measureReal_def, asMeasure_apply, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg (by intro ω _; split_ifs; exact μ.nonneg ω; exact le_rfl)

@[simp] lemma asMeasure_singleton [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : FiniteLaw Ω) (ω : Ω) :
    μ.asMeasure {ω} = ENNReal.ofReal (μ.mass ω) := by
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

lemma integral_asMeasure [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : FiniteLaw Ω) (f : Ω → ℝ) : ∫ ω, f ω ∂μ.asMeasure = μ.mean f := by
  rw [integral_fintype .of_finite]
  simp [mean, measureReal_def, ENNReal.toReal_ofReal, μ.nonneg]
end FiniteLaw

section ProductBridge
variable {Ω I : Type*} [Fintype Ω] [Fintype I]
  {X : I → Type*} [∀ i, Fintype (X i)]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
  {μ : FiniteLaw Ω} {sample : Ω → ∀ i, X i} {P : ∀ i, FiniteLaw (X i)}

/-- The exact full-string premise determines the genuine product measure. -/
theorem ProductBlockIID.map_eq_pi (h : ProductBlockIID μ sample P) :
    μ.asMeasure.map sample = Measure.pi (fun i => (P i).asMeasure) := by
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_finite sample) (measurableSet_singleton _),
    FiniteLaw.asMeasure_apply, Measure.pi_singleton]
  simp only [FiniteLaw.asMeasure_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (P i).nonneg (z i))]
  exact congrArg ENNReal.ofReal (h z)

/-- Event probabilities are transported without assuming any tail estimate. -/
theorem ProductBlockIID.prob_eq_pi (h : ProductBlockIID μ sample P) (S : Set (∀ i, X i)) :
    μ.prob (fun ω => sample ω ∈ S) =
      (Measure.pi (fun i => (P i).asMeasure)).real S := by
  rw [← h.map_eq_pi, measureReal_def,
    Measure.map_apply (measurable_of_finite sample) (Set.toFinite S).measurableSet,
    ← measureReal_def, FiniteLaw.asMeasure_real]
  rfl
end ProductBridge

/-- Weighted Hoeffding for arbitrary real bounded coordinate functions and an exact
finite product marginal. Signed weights may be incorporated in the coordinate functions. -/
theorem weighted_product_hoeffding_upper
    {Ω I : Type*} [Fintype Ω] [Fintype I]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (μ : FiniteLaw Ω) (sample : Ω → ∀ i, X i) (P : ∀ i, FiniteLaw (X i))
    (h : ProductBlockIID μ sample P) (f : ∀ i, X i → ℝ) (a b : I → ℝ)
    (hb : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (u : ℝ) (hu : 0 ≤ u) :
    μ.prob (fun ω => u ≤ (∑ i, f i (sample ω i)) - ∑ i, (P i).mean (f i)) ≤
      Real.exp (-2 * u ^ 2 / ∑ i, (b i - a i) ^ 2) := by
  classical
  letI : MeasurableSpace Ω := ⊤
  letI : ∀ i, MeasurableSpace (X i) := fun _ => ⊤
  let ν : Measure (∀ i, X i) := Measure.pi (fun i => (P i).asMeasure)
  have hmean (i : I) : (∫ z, f i (z i) ∂ν) = (P i).mean (f i) := by
    rw [integral_comp_eval (measurable_of_finite (f i)).aestronglyMeasurable,
      FiniteLaw.integral_asMeasure]
  have hind : iIndepFun (fun i z => f i (z i) - (P i).mean (f i)) ν :=
    iIndepFun_pi (μ := fun i => (P i).asMeasure)
      (X := fun i x => f i x - (P i).mean (f i))
      (fun i => (measurable_of_finite _).aemeasurable)
  have hsub (i : I) : HasSubgaussianMGF
      (fun z => f i (z i) - (P i).mean (f i)) ((‖b i - a i‖₊ / 2) ^ 2) ν := by
    rw [← hmean i]
    exact hasSubgaussianMGF_of_mem_Icc (measurable_of_finite _).aemeasurable
      (ae_of_all _ (fun z => hb i (z i)))
  have ht := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (fun i _ => hsub i) hu
  have hp := h.prob_eq_pi {z | u ≤ (∑ i, f i (z i)) - ∑ i, (P i).mean (f i)}
  simp only [Set.mem_setOf_eq] at hp
  rw [hp]
  change ν.real _ ≤ _
  simpa only [Finset.sum_sub_distrib, NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs, div_pow, sq_abs,
    ← Finset.sum_div, show (2 : ℝ) ^ 2 = 4 by norm_num,
    show ∀ x : ℝ, 2 * (x / 4) = x / 2 by intro x; ring,
    div_div_eq_mul_div, neg_mul, mul_comm (u ^ 2) 2] using ht

theorem weighted_product_hoeffding_lower
    {Ω I : Type*} [Fintype Ω] [Fintype I]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (μ : FiniteLaw Ω) (sample : Ω → ∀ i, X i) (P : ∀ i, FiniteLaw (X i))
    (h : ProductBlockIID μ sample P) (f : ∀ i, X i → ℝ) (a b : I → ℝ)
    (hb : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) (u : ℝ) (hu : 0 ≤ u) :
    μ.prob (fun ω => (∑ i, f i (sample ω i)) - ∑ i, (P i).mean (f i) ≤ -u) ≤
      Real.exp (-2 * u ^ 2 / ∑ i, (b i - a i) ^ 2) := by
  have ht := weighted_product_hoeffding_upper μ sample P h (fun i x => -f i x)
    (fun i => -b i) (fun i => -a i)
    (fun i x => ⟨neg_le_neg (hb i x).2, neg_le_neg (hb i x).1⟩) u hu
  have hm (i : I) : (P i).mean (fun x => -f i x) = -(P i).mean (f i) := by
    simp [FiniteLaw.mean, Finset.sum_neg_distrib]
  simp only [hm, Finset.sum_neg_distrib, neg_sub_neg] at ht
  convert ht using 1
  congr 1
  funext ω
  apply propext
  constructor <;> intro hω <;> linarith

namespace GoldExperiment
variable {A : Type*} [Fintype A]

def coordWeight (G : GoldExperiment A) (a : A)
    (j : (t : Bool) × Fin (G.n a t)) : ℝ :=
  G.sign a * (if j.1 then (G.n a true : ℝ)⁻¹ else -(G.n a false : ℝ)⁻¹)

def coordValue (G : GoldExperiment A) (a : A)
    (j : (t : Bool) × Fin (G.n a t)) (x : Bool) : ℝ :=
  G.coordWeight a j * (if x then 1 else 0)

lemma coordValue_bounds (G : GoldExperiment A) (a : A)
    (j : (t : Bool) × Fin (G.n a t)) (x : Bool) :
    G.coordValue a j x ∈ Set.Icc (min 0 (G.coordWeight a j)) (max 0 (G.coordWeight a j)) := by
  cases x <;> simp [coordValue, min_le_left, min_le_right, le_max_left, le_max_right]

lemma sum_coordValue (G : GoldExperiment A) (a : A) (ω : GoldSpace G) :
    (∑ j : (t : Bool) × Fin (G.n a t), G.coordValue a j (ω a j.1 j.2)) =
      G.estimate ω a := by
  simp only [coordValue, coordWeight, estimate, Fintype.sum_sigma, Fintype.sum_bool,
    Bool.false_eq_true, if_false, if_true]
  simp_rw [← Finset.mul_sum]
  ring

lemma sum_coordMean (G : GoldExperiment A) (a : A) :
    (∑ j : (t : Bool) × Fin (G.n a t),
      (bernoulliLaw (G.p a j.1) (G.p_nonneg a j.1) (G.p_le_one a j.1)).mean
        (G.coordValue a j)) = G.direction a := by
  have hn (t : Bool) : (G.n a t : ℝ) ≠ 0 := by exact_mod_cast (G.n_pos a t).ne'
  simp [FiniteLaw.mean, bernoulliLaw, bernMass, coordValue, coordWeight, direction,
    Fintype.sum_sigma, Fintype.sum_bool]
  field_simp [hn true, hn false]
  <;> ring

lemma sum_coordWidth (G : GoldExperiment A) (a : A) :
    (∑ j : (t : Bool) × Fin (G.n a t),
      (max 0 (G.coordWeight a j) - min 0 (G.coordWeight a j)) ^ 2) =
        G.varianceProxy a := by
  have hw (w : ℝ) : (max 0 w - min 0 w) ^ 2 = w ^ 2 := by
    rcases le_total 0 w with hw | hw
    · rw [max_eq_right hw, min_eq_left hw, sub_zero]
    · rw [max_eq_left hw, min_eq_right hw, zero_sub, neg_sq]
  simp_rw [hw]
  have hn (t : Bool) : (G.n a t : ℝ) ≠ 0 := by exact_mod_cast (G.n_pos a t).ne'
  rcases G.sign_valid a with hs | hs <;>
    simp [coordWeight, varianceProxy, Fintype.sum_sigma, Fintype.sum_bool, hs]
  all_goals field_simp
  all_goals ring
end GoldExperiment

theorem gold_weighted_hoeffding_upper
    {Ω A : Type*} [Fintype Ω] [Fintype A]
    (G : GoldExperiment A) (μ : FiniteLaw Ω) (gold : Ω → GoldSpace G)
    (hIID : G.IID μ gold) (a : A) {u : ℝ} (hu : 0 ≤ u) :
    μ.prob (fun ω => u ≤ G.estimate (gold ω) a - G.direction a) ≤
      Real.exp (-2 * u ^ 2 / G.varianceProxy a) := by
  have ht := weighted_product_hoeffding_upper μ
    (fun ω (j : (t : Bool) × Fin (G.n a t)) => gold ω a j.1 j.2)
    (fun j => bernoulliLaw (G.p a j.1) (G.p_nonneg a j.1) (G.p_le_one a j.1))
    (hIID a) (G.coordValue a) (fun j => min 0 (G.coordWeight a j))
    (fun j => max 0 (G.coordWeight a j)) (G.coordValue_bounds a) u hu
  simpa only [G.sum_coordValue, G.sum_coordMean, G.sum_coordWidth] using ht

theorem gold_weighted_hoeffding_lower
    {Ω A : Type*} [Fintype Ω] [Fintype A]
    (G : GoldExperiment A) (μ : FiniteLaw Ω) (gold : Ω → GoldSpace G)
    (hIID : G.IID μ gold) (a : A) {u : ℝ} (hu : 0 ≤ u) :
    μ.prob (fun ω => G.estimate (gold ω) a - G.direction a ≤ -u) ≤
      Real.exp (-2 * u ^ 2 / G.varianceProxy a) := by
  have ht := weighted_product_hoeffding_lower μ
    (fun ω (j : (t : Bool) × Fin (G.n a t)) => gold ω a j.1 j.2)
    (fun j => bernoulliLaw (G.p a j.1) (G.p_nonneg a j.1) (G.p_le_one a j.1))
    (hIID a) (G.coordValue a) (fun j => min 0 (G.coordWeight a j))
    (fun j => max 0 (G.coordWeight a j)) (G.coordValue_bounds a) u hu
  simpa only [G.sum_coordValue, G.sum_coordMean, G.sum_coordWidth] using ht

namespace ObservationExperiment
variable {E : Type*} [Fintype E] {X : E → Type*} [∀ e, Fintype (X e)]

def coordValue (O : ObservationExperiment E X) (e : E) (x y : X e) : ℝ := by
  classical
  exact (O.n e : ℝ)⁻¹ * if y = x then 1 else 0

lemma coordValue_bounds (O : ObservationExperiment E X) (e : E) (x y : X e) :
    O.coordValue e x y ∈ Set.Icc 0 (O.n e : ℝ)⁻¹ := by
  classical
  have hn : 0 ≤ (O.n e : ℝ)⁻¹ := by positivity
  by_cases h : y = x <;> simp [coordValue, h, hn]

lemma sum_coordValue (O : ObservationExperiment E X) (e : E) (x : X e)
    (ω : ObservationSpace O) :
    (∑ i : Fin (O.n e), O.coordValue e x (ω e i)) = O.empirical ω e x := by
  simp only [coordValue, empirical, Finset.mul_sum]

lemma mean_coordValue (O : ObservationExperiment E X) (e : E) (x : X e) :
    (O.law e).mean (O.coordValue e x) = (O.n e : ℝ)⁻¹ * (O.law e).mass x := by
  classical
  simp [coordValue, FiniteLaw.mean, mul_ite, mul_comm]

lemma sum_coordMean (O : ObservationExperiment E X) (e : E) (x : X e) :
    (∑ _i : Fin (O.n e), (O.law e).mean (O.coordValue e x)) = (O.law e).mass x := by
  have hn : (O.n e : ℝ) ≠ 0 := by exact_mod_cast (O.n_pos e).ne'
  simp [mean_coordValue, ← mul_assoc, hn]

lemma sum_coordWidth (O : ObservationExperiment E X) (e : E) :
    (∑ _i : Fin (O.n e), ((O.n e : ℝ)⁻¹ - 0) ^ 2) = (O.n e : ℝ)⁻¹ := by
  have hn : (O.n e : ℝ) ≠ 0 := by exact_mod_cast (O.n_pos e).ne'
  simp only [sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
end ObservationExperiment

theorem edge_cell_hoeffding_upper
    {Ω E : Type*} [Fintype Ω] [Fintype E] {X : E → Type*} [∀ e, Fintype (X e)]
    (O : ObservationExperiment E X) (μ : FiniteLaw Ω) (obs : Ω → ObservationSpace O)
    (hIID : O.IID μ obs) (e : E) (x : X e) {u : ℝ} (hu : 0 ≤ u) :
    μ.prob (fun ω => u ≤ O.empirical (obs ω) e x - (O.law e).mass x) ≤
      Real.exp (-2 * (O.n e : ℝ) * u ^ 2) := by
  have ht := weighted_product_hoeffding_upper μ (fun ω => obs ω e) (fun _ => O.law e)
    (hIID e) (fun _ => O.coordValue e x) (fun _ => 0) (fun _ => (O.n e : ℝ)⁻¹)
    (fun _ y => O.coordValue_bounds e x y) u hu
  simp only [O.sum_coordValue, O.sum_coordMean, O.sum_coordWidth, div_inv_eq_mul] at ht
  convert ht using 1
  congr 1
  ring

theorem edge_cell_hoeffding_lower
    {Ω E : Type*} [Fintype Ω] [Fintype E] {X : E → Type*} [∀ e, Fintype (X e)]
    (O : ObservationExperiment E X) (μ : FiniteLaw Ω) (obs : Ω → ObservationSpace O)
    (hIID : O.IID μ obs) (e : E) (x : X e) {u : ℝ} (hu : 0 ≤ u) :
    μ.prob (fun ω => O.empirical (obs ω) e x - (O.law e).mass x ≤ -u) ≤
      Real.exp (-2 * (O.n e : ℝ) * u ^ 2) := by
  have ht := weighted_product_hoeffding_lower μ (fun ω => obs ω e) (fun _ => O.law e)
    (hIID e) (fun _ => O.coordValue e x) (fun _ => 0) (fun _ => (O.n e : ℝ)⁻¹)
    (fun _ y => O.coordValue_bounds e x y) u hu
  simp only [O.sum_coordValue, O.sum_coordMean, O.sum_coordWidth, div_inv_eq_mul] at ht
  convert ht using 1
  congr 1
  ring

end Ext
