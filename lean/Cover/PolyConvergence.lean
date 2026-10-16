import Cover.IntervalEstimates
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Cover.PolyExpr

def magnitudeBound (M : ℚ) : PolyExpr n a → ℚ
  | .rat q => |q|
  | .scalar _ => M
  | .var _ => M
  | .add p q => magnitudeBound M p + magnitudeBound M q
  | .neg p => magnitudeBound M p
  | .mul p q => magnitudeBound M p * magnitudeBound M q

def widthSlope (M : ℚ) : PolyExpr n a → ℚ
  | .rat _ => 0
  | .scalar _ => 1
  | .var _ => 1
  | .add p q => widthSlope M p + widthSlope M q
  | .neg p => widthSlope M p
  | .mul p q => magnitudeBound M p * widthSlope M q + magnitudeBound M q * widthSlope M p

theorem magnitudeBound_nonneg (p : PolyExpr n a) {M : ℚ} (hM : 0 ≤ M) :
    0 ≤ p.magnitudeBound M := by
  induction p with
  | rat q => exact abs_nonneg q
  | scalar _ => exact hM
  | var _ => exact hM
  | add p q hp hq => exact add_nonneg hp hq
  | neg p hp => exact hp
  | mul p q hp hq => exact mul_nonneg hp hq

theorem widthSlope_nonneg (p : PolyExpr n a) {M : ℚ} (hM : 0 ≤ M) :
    0 ≤ p.widthSlope M := by
  induction p with
  | rat _ => exact le_refl _
  | scalar _ => exact zero_le_one
  | var _ => exact zero_le_one
  | add p q hp hq => exact add_nonneg hp hq
  | neg p hp => exact hp
  | mul p q hp hq =>
      exact add_nonneg
        (mul_nonneg (p.magnitudeBound_nonneg hM) hq)
        (mul_nonneg (q.magnitudeBound_nonneg hM) hp)

theorem interval_mag_le (p : PolyExpr n a) {M : ℚ} (hM : 0 ≤ M)
    {ics : Fin a → QInterval} {box : Fin n → QInterval}
    (hc : ∀ i, (ics i).mag ≤ M) (hx : ∀ i, (box i).mag ≤ M) :
    (interval ics box p).mag ≤ p.magnitudeBound M := by
  induction p with
  | rat q => exact le_of_eq (QInterval.singleton_mag q)
  | scalar i => exact hc i
  | var i => exact hx i
  | add p q hp hq => exact (QInterval.add_mag_le _ _).trans (add_le_add hp hq)
  | neg p hp => simpa only [interval, magnitudeBound, QInterval.neg_mag] using hp
  | mul p q hp hq =>
      exact (QInterval.mul_mag_le _ _).trans
        (mul_le_mul hp hq (QInterval.mag_nonneg _) (p.magnitudeBound_nonneg hM))

theorem interval_width_le (p : PolyExpr n a) {M δ : ℚ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {ics : Fin a → QInterval} {box : Fin n → QInterval}
    (hcv : ∀ i, (ics i).valid) (hxv : ∀ i, (box i).valid)
    (hcm : ∀ i, (ics i).mag ≤ M) (hxm : ∀ i, (box i).mag ≤ M)
    (hcw : ∀ i, (ics i).width ≤ δ) (hxw : ∀ i, (box i).width ≤ δ) :
    (interval ics box p).width ≤ p.widthSlope M * δ := by
  induction p with
  | rat q => simp only [interval, widthSlope, QInterval.singleton_width, zero_mul, le_refl]
  | scalar i => simpa only [interval, widthSlope, one_mul] using hcw i
  | var i => simpa only [interval, widthSlope, one_mul] using hxw i
  | add p q hp hq =>
      simpa only [interval, QInterval.add_width, widthSlope, add_mul] using add_le_add hp hq
  | neg p hp => simpa only [interval, QInterval.neg_width, widthSlope] using hp
  | mul p q hp hq =>
      have hpm := p.interval_mag_le hM hcm hxm
      have hqm := q.interval_mag_le hM hcm hxm
      have hpv := p.interval_valid hcv hxv
      have hqv := q.interval_valid hcv hxv
      calc
        (interval ics box (.mul p q)).width ≤
            (interval ics box p).mag * (interval ics box q).width +
            (interval ics box q).mag * (interval ics box p).width := QInterval.mul_width_le hpv hqv
        _ ≤ p.magnitudeBound M * (q.widthSlope M * δ) +
            q.magnitudeBound M * (p.widthSlope M * δ) := add_le_add
          (mul_le_mul hpm hq (QInterval.width_nonneg hqv) (p.magnitudeBound_nonneg hM))
          (mul_le_mul hqm hp (QInterval.width_nonneg hpv) (q.magnitudeBound_nonneg hM))
        _ = (PolyExpr.mul p q).widthSlope M * δ := by simp only [widthSlope]; ring

/-- The coefficient and box precisions are independent inputs to the same bound. -/
theorem interval_joint_width_le (p : PolyExpr n a) {M δc δx : ℚ}
    (hM : 0 ≤ M) (hc0 : 0 ≤ δc) (hx0 : 0 ≤ δx)
    {ics : Fin a → QInterval} {box : Fin n → QInterval}
    (hcv : ∀ i, (ics i).valid) (hxv : ∀ i, (box i).valid)
    (hcm : ∀ i, (ics i).mag ≤ M) (hxm : ∀ i, (box i).mag ≤ M)
    (hcw : ∀ i, (ics i).width ≤ δc) (hxw : ∀ i, (box i).width ≤ δx) :
    (interval ics box p).width ≤ p.widthSlope M * (δc + δx) :=
  p.interval_width_le hM (add_nonneg hc0 hx0) hcv hxv hcm hxm
    (fun i => (hcw i).trans (le_add_of_nonneg_right hx0))
    (fun i => (hxw i).trans (le_add_of_nonneg_left hc0))


def familySlope (M : ℚ) : List (PolyExpr n a) → ℚ
  | [] => 0
  | p :: ps => max (p.widthSlope M) (familySlope M ps)

theorem familySlope_nonneg (ps : List (PolyExpr n a)) (M : ℚ) : 0 ≤ familySlope M ps := by
  induction ps with
  | nil => exact le_refl _
  | cons p ps ih => exact ih.trans (le_max_right _ _)

theorem widthSlope_le_familySlope {p : PolyExpr n a} {ps : List (PolyExpr n a)}
    (M : ℚ) (hp : p ∈ ps) : p.widthSlope M ≤ familySlope M ps := by
  induction ps with
  | nil => simp only [List.not_mem_nil] at hp
  | cons q ps ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact le_max_left _ _
      · exact (ih hp).trans (le_max_right _ _)

/-- A single threshold works simultaneously for all coefficient enclosures, all boxes,
all enclosed real points and every expression in a fixed finite family. Both the
coefficient width and the spatial mesh must tend to zero; neither is frozen. -/
theorem uniform_joint_convergence (ps : List (PolyExpr n a)) {M : ℚ} (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℚ, 0 < δ ∧
    ∀ (ics : Fin a → QInterval) (box : Fin n → QInterval)
      (cs : Fin a → ℝ) (x : Fin n → ℝ),
      (∀ i, (ics i).contains (cs i)) → (∀ i, (box i).contains (x i)) →
      (∀ i, (ics i).mag ≤ M) → (∀ i, (box i).mag ≤ M) →
      (∀ i, (ics i).width ≤ δ) → (∀ i, (box i).width ≤ δ) →
      ∀ p ∈ ps, eval cs x p - (interval ics box p).lower < ε ∧
        ((interval ics box p).upper : ℝ) - eval cs x p < ε := by
  let L := familySlope M ps
  have hL : 0 ≤ L := familySlope_nonneg ps M
  have hLreal : (0 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : (0 : ℝ) < L + 1 := by linarith
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_rat_lt (div_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  intro ics box cs x hcs hxs hcm hxm hcw hxw p hp
  have hv := p.interval_sound hcs hxs
  have hw := p.interval_width_le hM hδ.le
    (fun i => QInterval.valid_of_contains (hcs i))
    (fun i => QInterval.valid_of_contains (hxs i)) hcm hxm hcw hxw
  have hs := widthSlope_le_familySlope M hp
  have hwL : (interval ics box p).width ≤ L * δ :=
    hw.trans (mul_le_mul_of_nonneg_right hs hδ.le)
  have hwR : ((interval ics box p).width : ℝ) ≤ (L : ℝ) * δ := by exact_mod_cast hwL
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hlt : (L : ℝ) * δ < ε := by
    have ht := (lt_div_iff₀ hden).mp hδε
    nlinarith
  exact ⟨(QInterval.endpoint_errors_le_width hv).1.trans_lt (hwR.trans_lt hlt),
    (QInterval.endpoint_errors_le_width hv).2.trans_lt (hwR.trans_lt hlt)⟩

end Cover.PolyExpr
