import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators Classical
noncomputable section
namespace Ext

/-- A real-valued probability mass on an arbitrary finite space. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
def prob (μ : FiniteLaw Ω) (A : Ω → Prop) : ℝ :=
  ∑ ω, if A ω then μ.mass ω else 0

def mean (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.mass ω * f ω

lemma prob_nonneg (μ : FiniteLaw Ω) (A : Ω → Prop) : 0 ≤ μ.prob A := by
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp_all [μ.nonneg]

lemma prob_le_one (μ : FiniteLaw Ω) (A : Ω → Prop) : μ.prob A ≤ 1 := by
  calc
    μ.prob A ≤ ∑ ω, μ.mass ω := by
      apply Finset.sum_le_sum
      intro ω _
      split_ifs <;> simp_all [μ.nonneg]
    _ = 1 := μ.total

lemma prob_mono (μ : FiniteLaw Ω) {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) :
    μ.prob A ≤ μ.prob B := by
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with hA hB hB <;> simp_all [μ.nonneg]

@[simp] lemma prob_true (μ : FiniteLaw Ω) : μ.prob (fun _ => True) = 1 := by
  simpa [prob] using μ.total

@[simp] lemma prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

lemma prob_compl (μ : FiniteLaw Ω) (A : Ω → Prop) :
    μ.prob (fun ω => ¬ A ω) = 1 - μ.prob A := by
  have h : μ.prob A + μ.prob (fun ω => ¬ A ω) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib]
    convert μ.total using 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : A ω <;> simp [hω]
  linarith

lemma prob_union_le (μ : FiniteLaw Ω) (A B : Ω → Prop) :
    μ.prob (fun ω => A ω ∨ B ω) ≤ μ.prob A + μ.prob B := by
  rw [prob, prob, prob, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB, μ.nonneg]

lemma prob_exists_le {I : Type*} [Fintype I] (μ : FiniteLaw Ω) (A : I → Ω → Prop) :
    μ.prob (fun ω => ∃ i, A i ω) ≤ ∑ i, μ.prob (A i) := by
  unfold prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ i, A i ω
  · obtain ⟨i, hi⟩ := h
    rw [if_pos (show ∃ j, A j ω from ⟨i, hi⟩)]
    have hsum := Finset.single_le_sum
      (s := Finset.univ) (f := fun i => if A i ω then μ.mass ω else 0)
      (fun j _ => by split_ifs <;> simp_all [μ.nonneg]) (Finset.mem_univ i)
    simpa [hi] using hsum
  · simp only [if_neg h]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp_all [μ.nonneg]

lemma prob_inter_ge (μ : FiniteLaw Ω) (A B : Ω → Prop) :
    μ.prob A + μ.prob B - 1 ≤ μ.prob (fun ω => A ω ∧ B ω) := by
  have h := μ.prob_union_le (fun ω => ¬ A ω) (fun ω => ¬ B ω)
  have he : (fun ω => ¬ A ω ∨ ¬ B ω) = (fun ω => ¬ (A ω ∧ B ω)) := by
    funext ω
    exact propext (not_and_or.symm)
  rw [he, prob_compl, prob_compl, prob_compl] at h
  linarith

lemma prob_map_event {X : Type*} [Fintype X] (μ : FiniteLaw Ω) (F : Ω → X)
    (U : X → Prop) :
    μ.prob (fun ω => U (F ω)) = ∑ x, if U x then μ.prob (fun ω => F ω = x) else 0 := by
  unfold prob
  calc
    (∑ ω, if U (F ω) then μ.mass ω else 0) =
        ∑ ω, ∑ x, if F ω = x ∧ U x then μ.mass ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.sum_eq_single (F ω)]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    _ = ∑ x, ∑ ω, if F ω = x ∧ U x then μ.mass ω else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : U x <;> simp [hx]

end FiniteLaw

/-- Exact full-string marginal, not a concentration assumption. -/
def ProductBlockIID {Ω I : Type*} [Fintype Ω] [Fintype I]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (μ : FiniteLaw Ω) (sample : Ω → ∀ i, X i) (P : ∀ i, FiniteLaw (X i)) : Prop :=
  ∀ z, μ.prob (fun ω => sample ω = z) = ∏ i, (P i).mass (z i)

def bernMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def bernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw Bool where
  mass := bernMass p
  nonneg := by intro b; cases b <;> simp [bernMass] <;> linarith
  total := by simp [Fintype.sum_bool, bernMass]

/-- Arbitrarily coupled gold blocks; each block is internally a Bernoulli product. -/
structure GoldExperiment (A : Type*) [Fintype A] where
  n : A → Bool → ℕ
  n_pos : ∀ a t, 0 < n a t
  p : A → Bool → ℝ
  p_nonneg : ∀ a t, 0 ≤ p a t
  p_le_one : ∀ a t, p a t ≤ 1
  sign : A → ℝ
  sign_valid : ∀ a, sign a = -1 ∨ sign a = 1

abbrev GoldSpace {A : Type*} [Fintype A] (G : GoldExperiment A) :=
  ∀ a, ∀ t, Fin (G.n a t) → Bool

namespace GoldExperiment
variable {A : Type*} [Fintype A]
def direction (G : GoldExperiment A) (a : A) : ℝ :=
  G.sign a * (G.p a true - G.p a false)
def varianceProxy (G : GoldExperiment A) (a : A) : ℝ :=
  (G.n a true : ℝ)⁻¹ + (G.n a false : ℝ)⁻¹
def estimate (G : GoldExperiment A) (ω : GoldSpace G) (a : A) : ℝ :=
  G.sign a * ((G.n a true : ℝ)⁻¹ * ∑ i, (if ω a true i then 1 else 0) -
    (G.n a false : ℝ)⁻¹ * ∑ i, (if ω a false i then 1 else 0))
def IID {Ω : Type*} [Fintype Ω] (G : GoldExperiment A)
    (μ : FiniteLaw Ω) (gold : Ω → GoldSpace G) : Prop :=
  ∀ a, ProductBlockIID μ (fun ω (j : (t : Bool) × Fin (G.n a t)) => gold ω a j.1 j.2)
    (fun j => bernoulliLaw (G.p a j.1) (G.p_nonneg a j.1) (G.p_le_one a j.1))
end GoldExperiment

structure ObservationExperiment (E : Type*) [Fintype E] (X : E → Type*)
    [∀ e, Fintype (X e)] where
  n : E → ℕ
  n_pos : ∀ e, 0 < n e
  law : ∀ e, FiniteLaw (X e)

abbrev ObservationSpace {E : Type*} [Fintype E] {X : E → Type*}
    [∀ e, Fintype (X e)] (O : ObservationExperiment E X) :=
  ∀ e, Fin (O.n e) → X e

namespace ObservationExperiment
variable {E : Type*} [Fintype E] {X : E → Type*} [∀ e, Fintype (X e)]
def IID {Ω : Type*} [Fintype Ω] (O : ObservationExperiment E X)
    (μ : FiniteLaw Ω) (obs : Ω → ObservationSpace O) : Prop :=
  ∀ e, ProductBlockIID μ (fun ω => obs ω e) (fun _ => O.law e)
def empirical (O : ObservationExperiment E X) (ω : ObservationSpace O) (e : E) (x : X e) : ℝ :=
  (O.n e : ℝ)⁻¹ * ∑ i, if ω e i = x then 1 else 0
end ObservationExperiment

end Ext
