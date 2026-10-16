import Ext.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
noncomputable section
namespace Gen.Constants

variable {G E : Type*} [Fintype G] [Fintype E] [Nonempty E]

def a (n : G → ℕ) (w σ : ℝ) (g : G) : ℝ :=
  (1 + Real.sqrt (n g)) / (w * σ ^ 2)
def b (edge : E → Finset G) (n : G → ℕ) (w σ : ℝ) (e : E) : ℝ :=
  σ⁻¹ ^ 3 + σ⁻¹ * ∑ g ∈ edge e, a n w σ g

def B (edge : E → Finset G) (n : G → ℕ) (w σ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun e => Real.sqrt ((b edge n w σ e) ^ 2 + ∑ g ∈ edge e, (a n w σ g) ^ 2))
def kappa (edge : E → Finset G) (n : G → ℕ) (w σ : ℝ) : ℝ :=
  1 / B edge n w σ
def curvature (m : ℕ) : ℝ := 12 * Real.sqrt m
def radius (edge : E → Finset G) (n : G → ℕ) (w σ : ℝ) (m : ℕ) : ℝ :=
  min 1 (kappa edge n w σ / curvature m)
def diameter (c r g : ℕ) : ℝ := Real.sqrt (2 * ((c : ℝ) + r * g))

lemma a_pos (n : G → ℕ) {w σ : ℝ} (hw : 0 < w) (hσ : 0 < σ) (g : G) :
    0 < a n w σ g := by
  unfold a
  positivity

lemma b_pos (edge : E → Finset G) (n : G → ℕ) {w σ : ℝ}
    (hw : 0 < w) (hσ : 0 < σ) (e : E) : 0 < b edge n w σ e := by
  unfold b
  have ha : 0 ≤ ∑ g ∈ edge e, a n w σ g :=
    Finset.sum_nonneg (fun g _ => (a_pos n hw hσ g).le)
  positivity

lemma edge_bound_le_B (edge : E → Finset G) (n : G → ℕ) (w σ : ℝ) (e : E) :
    Real.sqrt ((b edge n w σ e) ^ 2 + ∑ g ∈ edge e, (a n w σ g) ^ 2) ≤
      B edge n w σ := by
  exact Finset.le_sup' (fun e => Real.sqrt ((b edge n w σ e) ^ 2 +
    ∑ g ∈ edge e, (a n w σ g) ^ 2)) (Finset.mem_univ e)

lemma B_pos (edge : E → Finset G) (n : G → ℕ) {w σ : ℝ}
    (hw : 0 < w) (hσ : 0 < σ) : 0 < B edge n w σ := by
  let e : E := Classical.choice inferInstance
  have hb := b_pos edge n hw hσ e
  have hs : 0 ≤ ∑ g ∈ edge e, (a n w σ g) ^ 2 :=
    Finset.sum_nonneg (fun g _ => sq_nonneg _)
  exact (Real.sqrt_pos.2 (by positivity)).trans_le (edge_bound_le_B edge n w σ e)

lemma kappa_pos (edge : E → Finset G) (n : G → ℕ) {w σ : ℝ}
    (hw : 0 < w) (hσ : 0 < σ) : 0 < kappa edge n w σ := by
  exact one_div_pos.mpr (B_pos edge n hw hσ)

lemma curvature_pos {m : ℕ} (hm : 0 < m) : 0 < curvature m := by
  unfold curvature
  positivity

lemma radius_properties (edge : E → Finset G) (n : G → ℕ) {w σ : ℝ} {m : ℕ}
    (hw : 0 < w) (hσ : 0 < σ) (hm : 0 < m) :
    0 < radius edge n w σ m ∧ radius edge n w σ m ≤ 1 ∧
      curvature m * radius edge n w σ m ≤ kappa edge n w σ := by
  have hk := kappa_pos edge n hw hσ
  have hM := curvature_pos hm
  refine ⟨lt_min (by norm_num) (div_pos hk hM), min_le_left _ _, ?_⟩
  have h := (le_div_iff₀ hM).mp (min_le_right 1 (kappa edge n w σ / curvature m))
  simpa only [radius, mul_comm] using h

/-- Every coordinate of a real probability vector is at most one. -/
lemma probability_coord_le_one {I : Type*} [Fintype I]
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (ht : ∑ i, x i = 1) (i : I) : x i ≤ 1 := by
  rw [← ht]
  exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)

/-- Squared entrywise Euclidean norm, without replacing it by the Pi sup norm. -/
lemma probability_square_sum_le_one {I : Type*} [Fintype I]
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (ht : ∑ i, x i = 1) :
    ∑ i, x i ^ 2 ≤ 1 := by
  rw [← ht]
  apply Finset.sum_le_sum
  intro i hi
  have hxi := probability_coord_le_one x hx ht i
  nlinarith [hx i]

lemma probability_distance_square_sum_le_two {I : Type*} [Fintype I]
    (x y : I → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (htx : ∑ i, x i = 1) (hty : ∑ i, y i = 1) :
    ∑ i, (x i - y i) ^ 2 ≤ 2 := by
  calc
    ∑ i, (x i - y i) ^ 2 ≤ ∑ i, (x i ^ 2 + y i ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [mul_nonneg (hx i) (hy i)]
    _ = (∑ i, x i ^ 2) + ∑ i, y i ^ 2 := Finset.sum_add_distrib
    _ ≤ 2 := by linarith [probability_square_sum_le_one x hx htx,
      probability_square_sum_le_one y hy hty]

/-- Repeated local blocks may be counted more than once; globally every covered block
    is counted exactly once on the left. This is the sparse-design norm direction. -/
lemma covered_sum_le_sum_sum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (S : I → Finset J) (hcover : ∀ j, ∃ i, j ∈ S i)
    (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∑ j, f j ≤ ∑ i, ∑ j ∈ S i, f j := by
  classical
  calc
    ∑ j, f j ≤ ∑ j, ∑ i, if j ∈ S i then f j else 0 := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨i, hi⟩ := hcover j
      calc
        f j = if j ∈ S i then f j else 0 := by simp [hi]
        _ ≤ ∑ i, if j ∈ S i then f j else 0 :=
          Finset.single_le_sum (f := fun i => if j ∈ S i then f j else 0)
            (fun i _ => by split_ifs; exact hf j; exact le_rfl) (Finset.mem_univ i)
    _ = ∑ i, ∑ j ∈ S i, f j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp

/-- Algebraic last step of the tangent lower bound, once the exact squared contraction
    inequalities are established. This lemma does not assume or assert those identities. -/
lemma inverse_from_squared_bound {u v C : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hC : 0 < C) (h : u ^ 2 ≤ C ^ 2 * v ^ 2) : (1 / C) * u ≤ v := by
  have huv : u ≤ C * v := by nlinarith [mul_nonneg hC.le hv]
  have hdiv : u / C ≤ v := (div_le_iff₀ hC).mpr (by simpa [mul_comm] using huv)
  simpa [div_eq_mul_inv, mul_comm] using hdiv

end Gen.Constants
