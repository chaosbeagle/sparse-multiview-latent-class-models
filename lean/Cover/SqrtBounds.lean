import Cover.Interval
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace Cover
namespace DyadicSqrt

/-- Exact positive dyadic mesh denominator. -/
def scale (s : Nat) : ℚ := 2 ^ (s + 2)
def mesh (s : Nat) : ℚ := (scale s)⁻¹
/-- Integer sqrt runs on an integer floor of a rational; no real evaluation occurs. -/
def floorSqrt (q : ℚ) : Nat := Nat.sqrt (Int.floor q).toNat

def lower (s : Nat) (q : ℚ) : ℚ :=
  (floorSqrt (q * scale s ^ 2) : ℚ) / scale s

def upper (s : Nat) (q : ℚ) : ℚ :=
  if lower s q ^ 2 = q then lower s q else lower s q + mesh s

def bounds (s : Nat) (I : QInterval) : QInterval :=
  ⟨lower s I.lower, upper s I.upper⟩

lemma scale_pos (s : Nat) : 0 < scale s := by unfold scale; positivity
lemma mesh_pos (s : Nat) : 0 < mesh s := inv_pos.mpr (scale_pos s)

lemma floorSqrt_sq_le {q : ℚ} (hq : 0 ≤ q) : (floorSqrt q : ℚ) ^ 2 ≤ q := by
  have hf : 0 ≤ Int.floor q := Int.floor_nonneg.mpr hq
  have hs := Nat.sqrt_le' (Int.floor q).toNat
  have hs' : (floorSqrt q : ℚ) ^ 2 ≤ ((Int.floor q).toNat : ℚ) := by exact_mod_cast hs
  have he : ((Int.floor q).toNat : ℚ) = (Int.floor q : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hf]
  exact hs'.trans (he ▸ Int.floor_le q)

lemma lt_succ_floorSqrt_sq {q : ℚ} (hq : 0 ≤ q) : q < ((floorSqrt q : ℚ) + 1) ^ 2 := by
  have hf : 0 ≤ Int.floor q := Int.floor_nonneg.mpr hq
  have hs := Nat.succ_le_succ_sqrt' (Int.floor q).toNat
  have hs' : ((Int.floor q).toNat : ℚ) + 1 ≤ ((floorSqrt q : ℚ) + 1) ^ 2 := by exact_mod_cast hs
  have he : ((Int.floor q).toNat : ℚ) = (Int.floor q : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hf]
  rw [he] at hs'
  have hl : q < (Int.floor q : ℚ) + 1 := Int.lt_floor_add_one q
  exact hl.trans_le hs'

lemma lower_nonneg (s : Nat) (q : ℚ) : 0 ≤ lower s q :=
  div_nonneg (Nat.cast_nonneg _) (scale_pos s).le

lemma lower_sq_le (s : Nat) {q : ℚ} (hq : 0 ≤ q) : lower s q ^ 2 ≤ q := by
  have hs := floorSqrt_sq_le (mul_nonneg hq (sq_nonneg (scale s)))
  unfold lower
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos (scale_pos s))]
  exact hs

lemma lt_lower_add_mesh_sq (s : Nat) {q : ℚ} (hq : 0 ≤ q) : q < (lower s q + mesh s) ^ 2 := by
  have hs := lt_succ_floorSqrt_sq (mul_nonneg hq (sq_nonneg (scale s)))
  have he : lower s q + mesh s = ((floorSqrt (q * scale s ^ 2) : ℚ) + 1) / scale s := by
    simp [lower, mesh, add_div, one_div]
  rw [he, div_pow, lt_div_iff₀ (sq_pos_of_pos (scale_pos s))]
  exact hs

lemma lower_le_sqrt (s : Nat) {q : ℚ} (hq : 0 ≤ q) : (lower s q : ℝ) ≤ Real.sqrt q := by
  apply (Real.le_sqrt (by exact_mod_cast lower_nonneg s q) (by exact_mod_cast hq)).mpr
  exact_mod_cast lower_sq_le s hq

lemma sqrt_lt_lower_add_mesh (s : Nat) {q : ℚ} (hq : 0 ≤ q) :
    Real.sqrt q < (lower s q : ℝ) + mesh s := by
  have hp : (0 : ℝ) < (lower s q : ℝ) + mesh s := by
    exact_mod_cast add_pos_of_nonneg_of_pos (lower_nonneg s q) (mesh_pos s)
  apply (Real.sqrt_lt' hp).mpr
  exact_mod_cast lt_lower_add_mesh_sq s hq

lemma sqrt_le_upper (s : Nat) {q : ℚ} (hq : 0 ≤ q) : Real.sqrt q ≤ (upper s q : ℝ) := by
  unfold upper
  split_ifs with h
  · have he : ((lower s q : ℝ)) ^ 2 = (q : ℝ) := by exact_mod_cast h
    rw [← he, Real.sqrt_sq (by exact_mod_cast lower_nonneg s q)]
  · simpa only [Rat.cast_add] using (sqrt_lt_lower_add_mesh s hq).le

lemma upper_le_lower_add_mesh (s : Nat) (q : ℚ) : upper s q ≤ lower s q + mesh s := by
  unfold upper
  split_ifs
  · exact le_add_of_nonneg_right (mesh_pos s).le
  · exact le_rfl

lemma lower_le_upper (s : Nat) (q : ℚ) : lower s q ≤ upper s q := by
  unfold upper
  split_ifs
  · exact le_rfl
  · exact le_add_of_nonneg_right (mesh_pos s).le

/-- Full-interval enclosure, not merely endpoint or midpoint testing. -/
theorem bounds_contains (s : Nat) {I : QInterval} (hI : 0 ≤ I.lower)
    {x : ℝ} (hx : I.contains x) : (bounds s I).contains (Real.sqrt x) := by
  constructor
  · exact (lower_le_sqrt s hI).trans (Real.sqrt_le_sqrt hx.1)
  · have hu : 0 ≤ I.upper := by exact_mod_cast (show (0 : ℝ) ≤ I.upper from
      (show (0 : ℝ) ≤ I.lower by exact_mod_cast hI).trans (hx.1.trans hx.2))
    exact (Real.sqrt_le_sqrt hx.2).trans (sqrt_le_upper s hu)

lemma bounds_valid (s : Nat) {I : QInterval} (hI : I.valid) (hl : 0 ≤ I.lower) :
    (bounds s I).valid := by
  have h := bounds_contains s hl (x := (I.lower : ℝ))
    ⟨le_rfl, by exact_mod_cast hI⟩
  exact_mod_cast h.1.trans h.2

lemma sqrt_difference_le {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) :
    Real.sqrt u - Real.sqrt l ≤ Real.sqrt (u - l) := by
  have hu : 0 ≤ u := hl.trans hlu
  have hd : 0 ≤ u - l := sub_nonneg.mpr hlu
  have hl2 := Real.sq_sqrt hl
  have hu2 := Real.sq_sqrt hu
  have hd2 := Real.sq_sqrt hd
  have hprod := mul_nonneg (Real.sqrt_nonneg l) (Real.sqrt_nonneg (u-l))
  have hsum : 0 ≤ Real.sqrt l + Real.sqrt (u-l) := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sqrt_nonneg u]

/-- Quantitative outward-rounding width, including zero and exact-square endpoints. -/
theorem bounds_width (s : Nat) {I : QInterval} (hI : I.valid) (hl : 0 ≤ I.lower) :
    ((bounds s I).width : ℝ) ≤ Real.sqrt (I.width : ℝ) + 2 * (mesh s : ℝ) := by
  have hu : 0 ≤ I.upper := hl.trans hI
  have hlow := sqrt_lt_lower_add_mesh s hl
  have hupp : (upper s I.upper : ℝ) ≤ Real.sqrt I.upper + mesh s := by
    calc
      _ ≤ (lower s I.upper : ℝ) + mesh s := by exact_mod_cast upper_le_lower_add_mesh s I.upper
      _ ≤ Real.sqrt I.upper + mesh s := by linarith [lower_le_sqrt s hu]
  have hdiff := sqrt_difference_le (show (0 : ℝ) ≤ I.lower by exact_mod_cast hl)
    (show (I.lower : ℝ) ≤ I.upper by exact_mod_cast hI)
  have hw : ((bounds s I).width : ℝ) = (upper s I.upper : ℝ) - lower s I.lower := by
    simp [QInterval.width, bounds]
  rw [hw]
  have hIw : (I.width : ℝ) = (I.upper : ℝ) - I.lower := by simp [QInterval.width]
  rw [hIw]
  linarith

@[simp] theorem lower_zero (s : Nat) : lower s 0 = 0 := by
  simp [lower, floorSqrt]
@[simp] theorem upper_zero (s : Nat) : upper s 0 = 0 := by
  simp [upper]
@[simp] theorem bounds_zero (s : Nat) : bounds s (.singleton 0) = .singleton 0 := by
  simp [bounds, QInterval.singleton]

/-- Grid-exact rational squares have no artificial outward expansion. -/
theorem exact_square (s : Nat) {q : ℚ} (hq : 0 ≤ q)
    (he : lower s q ^ 2 = q) : upper s q = lower s q := by
  simp [upper, he]

lemma nat_le_floorSqrt {j : Nat} {q : ℚ} (hq : 0 ≤ q)
    (hj : (j : ℚ) ^ 2 ≤ q) : j ≤ floorSqrt q := by
  apply Nat.le_sqrt'.mpr
  have hi : (j ^ 2 : ℤ) ≤ Int.floor q := Int.le_floor.mpr (by exact_mod_cast hj)
  have hf : 0 ≤ Int.floor q := Int.floor_nonneg.mpr hq
  exact_mod_cast (show (j ^ 2 : ℤ) ≤ ((Int.floor q).toNat : ℤ) by
    simpa only [Int.toNat_of_nonneg hf] using hi)

lemma grid_le_lower (s : Nat) (j : Nat) {q : ℚ} (hq : 0 ≤ q)
    (hj : ((j : ℚ) / scale s) ^ 2 ≤ q) : (j : ℚ) / scale s ≤ lower s q := by
  apply (div_le_div_iff_of_pos_right (scale_pos s)).mpr
  apply Nat.cast_le.mpr
  apply nat_le_floorSqrt (mul_nonneg hq (sq_nonneg _))
  exact (div_le_iff₀ (sq_pos_of_pos (scale_pos s))).mp (by simpa [div_pow] using hj)

lemma half_le_lower (s : Nat) {q : ℚ} (hq : (1 : ℚ) / 4 ≤ q) : 1 / 2 ≤ lower s q := by
  have he : ((2 ^ (s+1) : Nat) : ℚ) / scale s = 1 / 2 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, scale]
    rw [show s+2 = (s+1)+1 by omega, pow_succ]
    field_simp
    simp [pow_add, pow_succ]
    ring
  rw [← he]
  apply grid_le_lower s (2 ^ (s+1)) (by linarith)
  rw [he]
  norm_num
  exact hq

lemma one_le_lower (s : Nat) {q : ℚ} (hq : 1 ≤ q) : 1 ≤ lower s q := by
  have he : ((2 ^ (s+2) : Nat) : ℚ) / scale s = 1 := by
    simp [scale]
  rw [← he]
  apply grid_le_lower s (2 ^ (s+2)) (by linarith)
  rw [he, one_pow]
  exact hq

lemma mesh_le_quarter (s : Nat) : mesh s ≤ 1/4 := by
  have hp : (1 : ℚ) ≤ 2^s := one_le_pow₀ (by norm_num)
  have hs : (4 : ℚ) ≤ scale s := by
    unfold scale
    rw [pow_add]
    norm_num
    linarith
  calc
    mesh s ≤ (4 : ℚ)⁻¹ := (inv_le_inv₀ (scale_pos s) (by norm_num)).mpr hs
    _ = 1/4 := by norm_num

end DyadicSqrt
end Cover
