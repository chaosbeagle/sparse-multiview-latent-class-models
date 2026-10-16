import Cover.IntervalDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Cover
namespace QInterval

@[simp] theorem singleton_valid (q : ℚ) : (singleton q).valid := le_refl _
@[simp] theorem singleton_contains (q : ℚ) : (singleton q).contains (q : ℝ) := ⟨le_refl _, le_refl _⟩

theorem valid_of_contains {I : QInterval} {x : ℝ} (h : I.contains x) : I.valid := by
  exact_mod_cast h.1.trans h.2

theorem contains_lower {I : QInterval} (h : I.valid) : I.contains (I.lower : ℝ) := by
  exact ⟨le_refl _, by exact_mod_cast h⟩

theorem contains_upper {I : QInterval} (h : I.valid) : I.contains (I.upper : ℝ) := by
  exact ⟨by exact_mod_cast h, le_refl _⟩

theorem add_contains {I J : QInterval} {x y : ℝ}
    (hx : I.contains x) (hy : J.contains y) : (add I J).contains (x + y) := by
  simp only [contains, add, Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem neg_contains {I : QInterval} {x : ℝ}
    (hx : I.contains x) : (neg I).contains (-x) := by
  simpa only [contains, neg, Rat.cast_neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

private theorem linear_bounds {a b x y L U : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : L ≤ a*y ∧ a*y ≤ U) (hb : L ≤ b*y ∧ b*y ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  rcases le_total 0 y with hy | hy
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans hb.2⟩
  · exact ⟨hb.1.trans (mul_le_mul_of_nonpos_right hx.2 hy),
      (mul_le_mul_of_nonpos_right hx.1 hy).trans ha.2⟩

private theorem linear_bounds_left {a b x y L U : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : L ≤ y*a ∧ y*a ≤ U) (hb : L ≤ y*b ∧ y*b ≤ U) :
    L ≤ y*x ∧ y*x ≤ U := by
  have h := linear_bounds (y := y) (L := L) (U := U) hx (by simpa only [mul_comm y a] using ha)
    (by simpa only [mul_comm y b] using hb)
  simpa only [mul_comm x y] using h

private theorem corner_bounds (a b c d : ℝ) :
    let L := Min.min (Min.min (a*c) (a*d)) (Min.min (b*c) (b*d))
    let U := Max.max (Max.max (a*c) (a*d)) (Max.max (b*c) (b*d))
    (L ≤ a*c ∧ a*c ≤ U) ∧ (L ≤ a*d ∧ a*d ≤ U) ∧
    (L ≤ b*c ∧ b*c ≤ U) ∧ (L ≤ b*d ∧ b*d ≤ U) := by
  dsimp
  exact ⟨⟨(min_le_left _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_left _ _)⟩,
    ⟨(min_le_left _ _).trans (min_le_right _ _),
      (le_max_right _ _).trans (le_max_left _ _)⟩,
    ⟨(min_le_right _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_right _ _)⟩,
    ⟨(min_le_right _ _).trans (min_le_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩⟩

theorem mul_contains {I J : QInterval} {x y : ℝ}
    (hx : I.contains x) (hy : J.contains y) : (mul I J).contains (x*y) := by
  have h := corner_bounds (I.lower : ℝ) (I.upper : ℝ) (J.lower : ℝ) (J.upper : ℝ)
  have hl := linear_bounds_left hy h.1 h.2.1
  have hu := linear_bounds_left hy h.2.2.1 h.2.2.2
  have hf := linear_bounds hx hl hu
  simpa only [contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using hf

theorem add_valid {I J : QInterval} (hI : I.valid) (hJ : J.valid) : (add I J).valid :=
  valid_of_contains (add_contains (contains_lower hI) (contains_lower hJ))
theorem neg_valid {I : QInterval} (hI : I.valid) : (neg I).valid :=
  valid_of_contains (neg_contains (contains_lower hI))
theorem mul_valid {I J : QInterval} (hI : I.valid) (hJ : J.valid) : (mul I J).valid :=
  valid_of_contains (mul_contains (contains_lower hI) (contains_lower hJ))

@[simp] theorem singleton_width (q : ℚ) : (singleton q).width = 0 := sub_self _
@[simp] theorem add_width (I J : QInterval) : (add I J).width = I.width + J.width := by
  simp only [width, add]; ring
@[simp] theorem neg_width (I : QInterval) : (neg I).width = I.width := by
  simp only [width, neg]; ring

theorem width_nonneg {I : QInterval} (hI : I.valid) : 0 ≤ I.width := sub_nonneg.mpr hI

theorem endpoint_errors_le_width {I : QInterval} {x : ℝ} (hx : I.contains x) :
    x - I.lower ≤ (I.width : ℝ) ∧ (I.upper : ℝ) - x ≤ (I.width : ℝ) := by
  simp only [width, Rat.cast_sub]
  constructor <;> linarith [hx.1, hx.2]

theorem invPos_contains {I : QInterval} {x : ℝ} (hpos : 0 < I.lower)
    (hx : I.contains x) : (invPos I).contains x⁻¹ := by
  have hl : (0 : ℝ) < I.lower := by exact_mod_cast hpos
  have hp : 0 < x := hl.trans_le hx.1
  simp only [contains, invPos, Rat.cast_inv]
  exact ⟨(inv_le_inv₀ (hp.trans_le hx.2) hp).2 hx.2, (inv_le_inv₀ hp hl).2 hx.1⟩

theorem invPos_valid {I : QInterval} (hpos : 0 < I.lower) (hI : I.valid) :
    (invPos I).valid := valid_of_contains (invPos_contains hpos (contains_lower hI))

theorem min_contains {I J : QInterval} {x y : ℝ}
    (hx : I.contains x) (hy : J.contains y) : (min I J).contains (Min.min x y) := by
  simp only [contains, min, Rat.cast_min]
  exact ⟨min_le_min hx.1 hy.1, min_le_min hx.2 hy.2⟩
theorem max_contains {I J : QInterval} {x y : ℝ}
    (hx : I.contains x) (hy : J.contains y) : (max I J).contains (Max.max x y) := by
  simp only [contains, max, Rat.cast_max]
  exact ⟨max_le_max hx.1 hy.1, max_le_max hx.2 hy.2⟩
theorem min_valid {I J : QInterval} (hI : I.valid) (hJ : J.valid) : (min I J).valid :=
  valid_of_contains (min_contains (contains_lower hI) (contains_lower hJ))
theorem max_valid {I J : QInterval} (hI : I.valid) (hJ : J.valid) : (max I J).valid :=
  valid_of_contains (max_contains (contains_lower hI) (contains_lower hJ))

end QInterval

namespace PolyExpr

theorem interval_sound (p : PolyExpr n a) {cs : Fin a → ℝ} {x : Fin n → ℝ}
    {ics : Fin a → QInterval} {box : Fin n → QInterval}
    (hc : ∀ i, (ics i).contains (cs i)) (hx : ∀ i, (box i).contains (x i)) :
    (interval ics box p).contains (eval cs x p) := by
  induction p with
  | rat q => exact QInterval.singleton_contains q
  | scalar i => exact hc i
  | var i => exact hx i
  | add p q hp hq => exact QInterval.add_contains hp hq
  | neg p hp => exact QInterval.neg_contains hp
  | mul p q hp hq => exact QInterval.mul_contains hp hq

theorem interval_valid (p : PolyExpr n a) {ics : Fin a → QInterval} {box : Fin n → QInterval}
    (hc : ∀ i, (ics i).valid) (hx : ∀ i, (box i).valid) : (interval ics box p).valid := by
  induction p with
  | rat q => exact QInterval.singleton_valid q
  | scalar i => exact hc i
  | var i => exact hx i
  | add p q hp hq => exact QInterval.add_valid hp hq
  | neg p hp => exact QInterval.neg_valid hp
  | mul p q hp hq => exact QInterval.mul_valid hp hq

end PolyExpr
end Cover
