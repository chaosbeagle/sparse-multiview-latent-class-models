import Ext.Concentration
import Ext.Planning

open scoped BigOperators Classical
noncomputable section
namespace Ext

namespace GoldExperiment
lemma varianceProxy_pos {A : Type*} [Fintype A] (G : GoldExperiment A) (a : A) :
    0 < G.varianceProxy a := by
  have h0 : (0 : ℝ) < G.n a false := by exact_mod_cast G.n_pos a false
  have h1 : (0 : ℝ) < G.n a true := by exact_mod_cast G.n_pos a true
  exact add_pos (inv_pos.2 h1) (inv_pos.2 h0)

lemma varianceProxy_equal {A : Type*} [Fintype A] (G : GoldExperiment A) {n : ℕ}
    (heq : ∀ a t, G.n a t = n) (a : A) : G.varianceProxy a = 2 / (n : ℝ) := by
  simp [varianceProxy, heq]
  ring
end GoldExperiment

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

/-- A-T2: simultaneous sign error; all ties are failures. -/
theorem gold_sign_family_bound (G : GoldExperiment A) (μ : FiniteLaw Ω)
    (gold : Ω → GoldSpace G) (hIID : G.IID μ gold)
    (γ : A → ℝ) (hγ : ∀ a, 0 < γ a) (hγ1 : ∀ a, γ a ≤ 1)
    (hmargin : ∀ a, γ a ≤ G.direction a) :
    μ.prob (fun ω => ∃ a, G.estimate (gold ω) a ≤ 0) ≤
      min 1 (∑ a, Real.exp (-2 * (γ a) ^ 2 / G.varianceProxy a)) := by
  apply le_min (μ.prob_le_one _)
  calc
    μ.prob (fun ω => ∃ a, G.estimate (gold ω) a ≤ 0) ≤
        ∑ a, μ.prob (fun ω => G.estimate (gold ω) a ≤ 0) := μ.prob_exists_le _
    _ ≤ ∑ a, Real.exp (-2 * (γ a) ^ 2 / G.varianceProxy a) := by
      apply Finset.sum_le_sum
      intro a _
      exact (μ.prob_mono (fun ω hω => by linarith [hmargin a])).trans
        (gold_weighted_hoeffding_lower G μ gold hIID a (hγ a).le)

lemma equal_sample_tail {n : ℕ} (hn : 0 < n) (γ : ℝ) :
    Real.exp (-2 * γ ^ 2 / (2 / (n : ℝ))) = Real.exp (-(n : ℝ) * γ ^ 2) := by
  congr 1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  <;> ring

/-- Common-n form of A-T2. -/
theorem gold_sign_equal_sample_bound (G : GoldExperiment A) (μ : FiniteLaw Ω)
    (gold : Ω → GoldSpace G) (hIID : G.IID μ gold)
    {n : ℕ} (hn : 0 < n) (heq : ∀ a t, G.n a t = n)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hmargin : ∀ a, γ ≤ G.direction a) :
    μ.prob (fun ω => ∃ a, G.estimate (gold ω) a ≤ 0) ≤
      min 1 ((Fintype.card A : ℝ) * Real.exp (-(n : ℝ) * γ ^ 2)) := by
  have h := gold_sign_family_bound G μ gold hIID (fun _ => γ)
    (fun _ => hγ) (fun _ => hγ1) hmargin
  simp only [G.varianceProxy_equal heq] at h
  simp_rw [equal_sample_tail hn] at h
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

/-- A-T2 planning. The maximum enforces positive per-stratum draw counts. -/
theorem gold_sign_sample_size [Nonempty A] (G : GoldExperiment A) (μ : FiniteLaw Ω)
    (gold : Ω → GoldSpace G) (hIID : G.IID μ gold)
    {n : ℕ} (heq : ∀ a t, G.n a t = n)
    {α γ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hmargin : ∀ a, γ ≤ G.direction a)
    (hplan : max 1 (Nat.ceil (Real.log ((Fintype.card A : ℝ) / α) / γ ^ 2)) ≤ n) :
    μ.prob (fun ω => ∃ a, G.estimate (gold ω) a ≤ 0) ≤ α := by
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_left _ _).trans hplan)
  have h := gold_sign_equal_sample_bound G μ gold hIID hn heq hγ hγ1 hmargin
  exact h.trans ((min_le_right _ _).trans
    (sign_planning_exponential Fintype.card_pos hα hγ ((le_max_right _ _).trans hplan)))

lemma sum_card_div [Nonempty A] (δ : ℝ) :
    (∑ _a : A, δ / (Fintype.card A : ℝ)) = δ := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := ne_of_gt (natural_card_pos (A := A))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- A-T3: simultaneous failure of the one-sided lower confidence endpoints. -/
theorem gold_lower_endpoint_failure [Nonempty A] (G : GoldExperiment A) (μ : FiniteLaw Ω)
    (gold : Ω → GoldSpace G) (hIID : G.IID μ gold)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    μ.prob (fun ω => ∃ a, G.direction a < G.estimate (gold ω) a -
      confidenceRadius (G.varianceProxy a) (Fintype.card A) α) ≤ α := by
  have hαm : α ≤ (Fintype.card A : ℝ) := hα1.le.trans natural_card_one_le
  calc
    μ.prob (fun ω => ∃ a, G.direction a < G.estimate (gold ω) a -
        confidenceRadius (G.varianceProxy a) (Fintype.card A) α) ≤
        ∑ a, μ.prob (fun ω => G.direction a < G.estimate (gold ω) a -
          confidenceRadius (G.varianceProxy a) (Fintype.card A) α) := μ.prob_exists_le _
    _ ≤ ∑ _a : A, α / (Fintype.card A : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have h := gold_weighted_hoeffding_upper G μ gold hIID a
        (confidenceRadius_nonneg (G.varianceProxy a) (Fintype.card A) α)
      rw [confidenceRadius_tail (G.varianceProxy_pos a) hα hαm] at h
      exact (μ.prob_mono (fun ω hω => by linarith)).trans h
    _ = α := sum_card_div α

/-- A-T3: strict certification cannot falsely assert a positive or zero direction except at α. -/
theorem gold_false_certification [Nonempty A] (G : GoldExperiment A) (μ : FiniteLaw Ω)
    (gold : Ω → GoldSpace G) (hIID : G.IID μ gold)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    μ.prob (fun ω => ∃ a, G.direction a ≤ 0 ∧
      0 < G.estimate (gold ω) a - confidenceRadius (G.varianceProxy a) (Fintype.card A) α) ≤ α := by
  apply (μ.prob_mono ?_).trans (gold_lower_endpoint_failure G μ gold hIID hα hα1)
  intro ω ⟨a, ha, hb⟩
  exact ⟨a, lt_of_le_of_lt ha hb⟩

/-- A-T3 power uses the closed lower tail. Equality at the planning threshold is included. -/
theorem gold_certification_power [Nonempty A] (G : GoldExperiment A) (μ : FiniteLaw Ω)
    (gold : Ω → GoldSpace G) (hIID : G.IID μ gold)
    {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (γ : A → ℝ) (hmargin : ∀ a, γ a ≤ G.direction a)
    (hpower : ∀ a, confidenceRadius (G.varianceProxy a) (Fintype.card A) α +
      confidenceRadius (G.varianceProxy a) (Fintype.card A) β ≤ γ a) :
    μ.prob (fun ω => ∃ a, G.estimate (gold ω) a -
      confidenceRadius (G.varianceProxy a) (Fintype.card A) α ≤ 0) ≤ β := by
  have hβm : β ≤ (Fintype.card A : ℝ) := hβ1.le.trans natural_card_one_le
  calc
    μ.prob (fun ω => ∃ a, G.estimate (gold ω) a -
        confidenceRadius (G.varianceProxy a) (Fintype.card A) α ≤ 0) ≤
        ∑ a, μ.prob (fun ω => G.estimate (gold ω) a -
          confidenceRadius (G.varianceProxy a) (Fintype.card A) α ≤ 0) := μ.prob_exists_le _
    _ ≤ ∑ _a : A, β / (Fintype.card A : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      have h := gold_weighted_hoeffding_lower G μ gold hIID a
        (confidenceRadius_nonneg (G.varianceProxy a) (Fintype.card A) β)
      rw [confidenceRadius_tail (G.varianceProxy_pos a) hβ hβm] at h
      exact (μ.prob_mono (fun ω hω => by linarith [hmargin a, hpower a])).trans h
    _ = β := sum_card_div β

/-- A-T3 exact common-n, common-margin inclusive power plan. -/
theorem gold_power_sample_size [Nonempty A] (G : GoldExperiment A) (μ : FiniteLaw Ω)
    (gold : Ω → GoldSpace G) (hIID : G.IID μ gold)
    {n : ℕ} (heq : ∀ a t, G.n a t = n)
    {α β γ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hmargin : ∀ a, γ ≤ G.direction a)
    (hplan : max 1 (Nat.ceil ((Real.sqrt (Real.log ((Fintype.card A : ℝ) / α)) +
      Real.sqrt (Real.log ((Fintype.card A : ℝ) / β))) ^ 2 / γ ^ 2)) ≤ n) :
    μ.prob (fun ω => ∃ a, G.estimate (gold ω) a -
      confidenceRadius (G.varianceProxy a) (Fintype.card A) α ≤ 0) ≤ β := by
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_left _ _).trans hplan)
  apply gold_certification_power G μ gold hIID hα hα1 hβ hβ1 (fun _ => γ) hmargin
  intro a
  simpa only [GoldExperiment.varianceProxy, heq] using
    power_planning_radii Fintype.card_pos hn hα hα1 hβ hβ1 hγ
      ((le_max_right _ _).trans hplan)

/-- A-T4: simultaneous two-sided intervals with the exact factor 2m. -/
theorem gold_difference_band [Nonempty A] (G : GoldExperiment A) (μ : FiniteLaw Ω)
    (gold : Ω → GoldSpace G) (hIID : G.IID μ gold)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.prob (fun ω => ∀ a, |G.estimate (gold ω) a - G.direction a| ≤
      confidenceRadius (G.varianceProxy a) (2 * (Fintype.card A : ℝ)) δ) := by
  have hm : (0 : ℝ) < Fintype.card A := natural_card_pos
  have hδm : δ ≤ 2 * (Fintype.card A : ℝ) := by
    have := natural_card_one_le (A := A)
    linarith
  have failure : μ.prob (fun ω => ∃ a, confidenceRadius (G.varianceProxy a)
        (2 * (Fintype.card A : ℝ)) δ < |G.estimate (gold ω) a - G.direction a|) ≤ δ := by
    calc
      μ.prob (fun ω => ∃ a, confidenceRadius (G.varianceProxy a)
          (2 * (Fintype.card A : ℝ)) δ < |G.estimate (gold ω) a - G.direction a|) ≤
          ∑ a, μ.prob (fun ω => confidenceRadius (G.varianceProxy a)
            (2 * (Fintype.card A : ℝ)) δ < |G.estimate (gold ω) a - G.direction a|) := μ.prob_exists_le _
      _ ≤ ∑ _a : A, δ / (Fintype.card A : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        let h := confidenceRadius (G.varianceProxy a) (2 * (Fintype.card A : ℝ)) δ
        have hu := gold_weighted_hoeffding_upper G μ gold hIID a (confidenceRadius_nonneg (G.varianceProxy a) (2 * (Fintype.card A : ℝ)) δ)
        have hl := gold_weighted_hoeffding_lower G μ gold hIID a (confidenceRadius_nonneg (G.varianceProxy a) (2 * (Fintype.card A : ℝ)) δ)
        rw [confidenceRadius_tail (G.varianceProxy_pos a) hδ hδm] at hu hl
        have hevent : μ.prob (fun ω => h < |G.estimate (gold ω) a - G.direction a|) ≤
            μ.prob (fun ω => h ≤ G.estimate (gold ω) a - G.direction a) +
            μ.prob (fun ω => G.estimate (gold ω) a - G.direction a ≤ -h) := by
          apply (μ.prob_mono ?_).trans (μ.prob_union_le _ _)
          intro ω hω
          rcases (lt_abs).1 hω with hb | hb
          · exact Or.inl hb.le
          · exact Or.inr (by linarith)
        dsimp [h] at hevent
        have heq : δ / (2 * (Fintype.card A : ℝ)) + δ / (2 * (Fintype.card A : ℝ)) =
            δ / (Fintype.card A : ℝ) := by field_simp <;> ring
        linarith
      _ = δ := sum_card_div δ
  have he : (fun ω => ∃ a, confidenceRadius (G.varianceProxy a)
      (2 * (Fintype.card A : ℝ)) δ < |G.estimate (gold ω) a - G.direction a|) =
      (fun ω => ¬ ∀ a, |G.estimate (gold ω) a - G.direction a| ≤
        confidenceRadius (G.varianceProxy a) (2 * (Fintype.card A : ℝ)) δ) := by
    funext ω
    simp
  rw [he, μ.prob_compl] at failure
  linarith

end Ext
