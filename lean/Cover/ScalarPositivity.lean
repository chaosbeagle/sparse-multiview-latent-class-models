import Cover.ScalarBounds
import Cover.IntervalEstimates

namespace Cover.QInterval

lemma mul_lower_nonnegative {I J : QInterval} (hI : I.valid) (hJ : J.valid)
    (hIl : 0 ≤ I.lower) (hJl : 0 ≤ J.lower) :
    (I.mul J).lower = I.lower * J.lower := by
  unfold mul
  have hIu := hIl.trans hI
  have hJu := hJl.trans hJ
  have h1 : I.lower * J.lower ≤ I.lower * J.upper := mul_le_mul_of_nonneg_left hJ hIl
  have h2 : I.lower * J.lower ≤ I.upper * J.lower := mul_le_mul_of_nonneg_right hI hJl
  have h3 : I.lower * J.lower ≤ I.upper * J.upper := mul_le_mul hI hJ hJl hIu
  simp only
  rw [min_eq_left h1, min_eq_left (le_min h2 h3)]

end Cover.QInterval

namespace Cover.ScalarExpr

/-- Proof-only lower-bound bookkeeping for the concrete executable evaluator. -/
def HasLower (s : Nat) (w σ : QInterval) (p : ScalarExpr) (l : ℚ) : Prop :=
  ∃ I, p.bounds s w σ = some I ∧ I.valid ∧ l ≤ I.lower

variable {s : Nat} {w σ : QInterval} {p q : ScalarExpr} {l m : ℚ}

lemma HasLower.rat (q : ℚ) : HasLower s w σ (.rat q) q :=
  ⟨.singleton q, rfl, le_rfl, le_rfl⟩

lemma HasLower.add (hp : HasLower s w σ p l) (hq : HasLower s w σ q m) :
    HasLower s w σ (.add p q) (l+m) := by
  obtain ⟨I, hi, hiv, hil⟩ := hp
  obtain ⟨J, hj, hjv, hjl⟩ := hq
  refine ⟨I.add J, by simp [bounds, hi, hj], QInterval.add_valid hiv hjv, add_le_add hil hjl⟩

lemma HasLower.mul (hp : HasLower s w σ p l) (hq : HasLower s w σ q m)
    (hl : 0 ≤ l) (hm : 0 ≤ m) : HasLower s w σ (.mul p q) (l*m) := by
  obtain ⟨I, hi, hiv, hil⟩ := hp
  obtain ⟨J, hj, hjv, hjl⟩ := hq
  refine ⟨I.mul J, by simp [bounds, hi, hj], QInterval.mul_valid hiv hjv, ?_⟩
  rw [QInterval.mul_lower_nonnegative hiv hjv (hl.trans hil) (hm.trans hjl)]
  exact mul_le_mul hil hjl hm (hl.trans hil)

lemma HasLower.weaken (hp : HasLower s w σ p l) (h : m ≤ l) : HasLower s w σ p m := by
  obtain ⟨I, hi, hiv, hil⟩ := hp
  exact ⟨I, hi, hiv, h.trans hil⟩

lemma HasLower.pow (hp : HasLower s w σ p l) (hl : 0 ≤ l) (n : Nat) :
    HasLower s w σ (p.pow n) (l^n) := by
  induction n with
  | zero => simpa only [ScalarExpr.pow, pow_zero] using (HasLower.rat (s := s) (w := w) (σ := σ) 1)
  | succ n ih => simpa only [ScalarExpr.pow, pow_succ] using ih.mul hp (pow_nonneg hl n) hl

lemma HasLower.sum (ps : List ScalarExpr) (hp : ∀ p ∈ ps, HasLower s w σ p 0) :
    HasLower s w σ (.sum ps) 0 := by
  induction ps with
  | nil => exact HasLower.rat 0
  | cons p ps ih =>
    have h := (hp p (by simp)).add (ih fun q hq => hp q (by simp [hq]))
    simpa only [ScalarExpr.sum, zero_add] using h

lemma HasLower.sqrt_nonneg (hp : HasLower s w σ p 0) :
    HasLower s w σ (.sqrt p) 0 := by
  obtain ⟨I, hi, hiv, hil⟩ := hp
  refine ⟨DyadicSqrt.bounds s I, by simp [bounds, hi, hil], DyadicSqrt.bounds_valid s hiv hil, ?_⟩
  exact DyadicSqrt.lower_nonneg s I.lower

lemma HasLower.sqrt_half (hp : HasLower s w σ p (1/4)) :
    HasLower s w σ (.sqrt p) (1/2) := by
  obtain ⟨I, hi, hiv, hil⟩ := hp
  have hp0 : 0 ≤ I.lower := by linarith
  refine ⟨DyadicSqrt.bounds s I, by simp [bounds, hi, hp0], DyadicSqrt.bounds_valid s hiv hp0, ?_⟩
  exact DyadicSqrt.half_le_lower s hil

lemma HasLower.sqrt_one (hp : HasLower s w σ p 1) :
    HasLower s w σ (.sqrt p) 1 := by
  obtain ⟨I, hi, hiv, hil⟩ := hp
  have hp0 : 0 ≤ I.lower := by linarith
  refine ⟨DyadicSqrt.bounds s I, by simp [bounds, hi, hp0], DyadicSqrt.bounds_valid s hiv hp0, ?_⟩
  exact DyadicSqrt.one_le_lower s hil

lemma HasLower.inv_positive (hp : HasLower s w σ p l) (hl : 0 < l) :
    ∃ b : ℚ, 0 < b ∧ HasLower s w σ (.inv p) b := by
  obtain ⟨I, hi, hiv, hil⟩ := hp
  have hlo : 0 < I.lower := hl.trans_le hil
  have hup : 0 < I.upper := hlo.trans_le hiv
  exact ⟨I.upper⁻¹, inv_pos.mpr hup,
    I.invPos, by simp [bounds, hi, hlo], QInterval.invPos_valid hlo hiv, le_rfl⟩

lemma HasLower.max (hp : HasLower s w σ p l) (hq : HasLower s w σ q m) :
    HasLower s w σ (.max p q) (Max.max l m) := by
  obtain ⟨I, hi, hiv, hil⟩ := hp
  obtain ⟨J, hj, hjv, hjl⟩ := hq
  exact ⟨I.max J, by simp [bounds, hi, hj], QInterval.max_valid hiv hjv, max_le_max hil hjl⟩

lemma HasLower.min (hp : HasLower s w σ p l) (hq : HasLower s w σ q m) :
    HasLower s w σ (.min p q) (Min.min l m) := by
  obtain ⟨I, hi, hiv, hil⟩ := hp
  obtain ⟨J, hj, hjv, hjl⟩ := hq
  exact ⟨I.min J, by simp [bounds, hi, hj], QInterval.min_valid hiv hjv, min_le_min hil hjl⟩

lemma HasLower.maxList (ps : List ScalarExpr) (hne : ps ≠ [])
    (hp : ∀ p ∈ ps, HasLower s w σ p l) : HasLower s w σ (.maxList ps) l := by
  induction ps with
  | nil => contradiction
  | cons p ps ih =>
    cases ps with
    | nil => exact hp p (by simp)
    | cons q qs =>
      have h := (hp p (by simp)).max (ih (by simp) fun a ha => hp a (by simp [ha]))
      simpa only [ScalarExpr.maxList, max_self] using h

end Cover.ScalarExpr
