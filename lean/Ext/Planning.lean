import Ext.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

open scoped BigOperators Classical
noncomputable section
namespace Ext

/-- One-sided confidence radius. The multiplicity is a real input to expose exact constants. -/
def confidenceRadius (v c δ : ℝ) : ℝ := Real.sqrt ((v / 2) * Real.log (c / δ))

lemma log_ratio_nonneg {c δ : ℝ} (hδ : 0 < δ) (hδc : δ ≤ c) :
    0 ≤ Real.log (c / δ) := by
  apply Real.log_nonneg
  exact (le_div_iff₀ hδ).2 (by simpa using hδc)

lemma confidenceRadius_nonneg (v c δ : ℝ) : 0 ≤ confidenceRadius v c δ :=
  Real.sqrt_nonneg _

lemma confidenceRadius_tail {v c δ : ℝ} (hv : 0 < v) (hδ : 0 < δ) (hδc : δ ≤ c) :
    Real.exp (-2 * confidenceRadius v c δ ^ 2 / v) = δ / c := by
  have hc : 0 < c := hδ.trans_le hδc
  have hlog := log_ratio_nonneg hδ hδc
  rw [confidenceRadius, Real.sq_sqrt (mul_nonneg (by positivity) hlog)]
  have he : -2 * (v / 2 * Real.log (c / δ)) / v = - Real.log (c / δ) := by
    field_simp
    <;> ring
  rw [he, Real.exp_neg, Real.exp_log (div_pos hc hδ), inv_div]

lemma natural_card_pos {A : Type*} [Fintype A] [Nonempty A] :
    (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos

lemma natural_card_one_le {A : Type*} [Fintype A] [Nonempty A] :
    (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos

/-- Inclusive natural ceiling planning: equality is allowed. -/
lemma sign_planning_exponential {m n : ℕ} {α γ : ℝ}
    (hm : 0 < m) (hα : 0 < α) (hγ : 0 < γ)
    (hn : Nat.ceil (Real.log ((m : ℝ) / α) / γ ^ 2) ≤ n) :
    (m : ℝ) * Real.exp (-(n : ℝ) * γ ^ 2) ≤ α := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : Real.log ((m : ℝ) / α) / γ ^ 2 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hprod : Real.log ((m : ℝ) / α) ≤ (n : ℝ) * γ ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hγ)).1 hnR
  calc
    (m : ℝ) * Real.exp (-(n : ℝ) * γ ^ 2) ≤
        (m : ℝ) * Real.exp (-Real.log ((m : ℝ) / α)) := by
      gcongr
      linarith
    _ = α := by
      rw [Real.exp_neg, Real.exp_log (div_pos hmR hα), inv_div]
      field_simp

/-- Equal-stratum variance proxy and exact square-root radius simplification. -/
lemma equal_radius {n : ℕ} {c δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hδc : δ ≤ c) :
    confidenceRadius ((n : ℝ)⁻¹ + (n : ℝ)⁻¹) c δ =
      Real.sqrt (Real.log (c / δ)) / Real.sqrt (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold confidenceRadius
  have hv : ((n : ℝ)⁻¹ + (n : ℝ)⁻¹) / 2 = (n : ℝ)⁻¹ := by ring
  rw [hv, inv_mul_eq_div, Real.sqrt_div (log_ratio_nonneg hδ hδc)]

/-- Inclusive power planning establishes the sum of radii, including the equality boundary. -/
lemma power_planning_radii {m n : ℕ} {α β γ : ℝ}
    (hm : 0 < m) (hn : 0 < n)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hplan : Nat.ceil ((Real.sqrt (Real.log ((m : ℝ) / α)) +
      Real.sqrt (Real.log ((m : ℝ) / β))) ^ 2 / γ ^ 2) ≤ n) :
    confidenceRadius ((n : ℝ)⁻¹ + (n : ℝ)⁻¹) m α +
      confidenceRadius ((n : ℝ)⁻¹ + (n : ℝ)⁻¹) m β ≤ γ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hαm : α ≤ (m : ℝ) := hα1.le.trans hm1
  have hβm : β ≤ (m : ℝ) := hβ1.le.trans hm1
  rw [equal_radius hn hα hαm, equal_radius hn hβ hβm, ← add_div]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hnR)).2
  have hR : (Real.sqrt (Real.log ((m : ℝ) / α)) +
      Real.sqrt (Real.log ((m : ℝ) / β))) ^ 2 / γ ^ 2 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hplan)
  have hsq := (div_le_iff₀ (sq_pos_of_pos hγ)).1 hR
  have hnSq := Real.sq_sqrt hnR.le
  have hsum : 0 ≤ Real.sqrt (Real.log ((m : ℝ) / α)) +
      Real.sqrt (Real.log ((m : ℝ) / β)) := by positivity
  have hright : 0 ≤ γ * Real.sqrt (n : ℝ) := by positivity
  nlinarith [sq_nonneg (γ * Real.sqrt (n : ℝ) -
    (Real.sqrt (Real.log ((m : ℝ) / α)) + Real.sqrt (Real.log ((m : ℝ) / β))))]

/-- Exact categorical cell radius cancellation, with every real error level in scope. -/
lemma cell_radius_tail {n : ℕ} {c δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hδc : δ ≤ c) :
    Real.exp (-2 * (n : ℝ) * (Real.sqrt (Real.log (c / δ) / (2 * (n : ℝ)))) ^ 2) =
      δ / c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := hδ.trans_le hδc
  rw [Real.sq_sqrt (div_nonneg (log_ratio_nonneg hδ hδc) (by positivity))]
  have he : -2 * (n : ℝ) * (Real.log (c / δ) / (2 * (n : ℝ))) = -Real.log (c / δ) := by
    field_simp
    <;> ring
  rw [he, Real.exp_neg, Real.exp_log (div_pos hc hδ), inv_div]

end Ext
