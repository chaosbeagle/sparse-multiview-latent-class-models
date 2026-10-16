import Cover.AlgebraicSemantics

namespace Cover
namespace QInterval

 theorem add_subset {I J I' J' : QInterval} (hI : I'.subset I) (hJ : J'.subset J) :
    (I'.add J').subset (I.add J) :=
  ⟨add_le_add hI.1 hJ.1, add_le_add hI.2 hJ.2⟩

 theorem mul_subset {I J I' J' : QInterval}
    (vI : I'.valid) (vJ : J'.valid) (hI : I'.subset I) (hJ : J'.subset J) :
    (I'.mul J').subset (I.mul J) := by
  have hlI := contains_of_subset hI (contains_lower vI)
  have huI := contains_of_subset hI (contains_upper vI)
  have hlJ := contains_of_subset hJ (contains_lower vJ)
  have huJ := contains_of_subset hJ (contains_upper vJ)
  have hll : (I.mul J).lower ≤ I'.lower * J'.lower ∧ I'.lower * J'.lower ≤ (I.mul J).upper := by
    have hh := mul_contains hlI hlJ
    unfold contains at hh
    exact_mod_cast hh
  have hlu : (I.mul J).lower ≤ I'.lower * J'.upper ∧ I'.lower * J'.upper ≤ (I.mul J).upper := by
    have hh := mul_contains hlI huJ
    unfold contains at hh
    exact_mod_cast hh
  have hul : (I.mul J).lower ≤ I'.upper * J'.lower ∧ I'.upper * J'.lower ≤ (I.mul J).upper := by
    have hh := mul_contains huI hlJ
    unfold contains at hh
    exact_mod_cast hh
  have huu : (I.mul J).lower ≤ I'.upper * J'.upper ∧ I'.upper * J'.upper ≤ (I.mul J).upper := by
    have hh := mul_contains huI huJ
    unfold contains at hh
    exact_mod_cast hh
  exact ⟨le_min (le_min hll.1 hlu.1) (le_min hul.1 huu.1),
    max_le (max_le hll.2 hlu.2) (max_le hul.2 huu.2)⟩

end QInterval
namespace IntPolynomial

 theorem intervalHorner_valid (p : Coeffs) {I : QInterval} (hv : I.valid) :
    (intervalHorner p I).valid :=
  QInterval.valid_of_contains (intervalHorner_sound p (QInterval.contains_lower hv))

 theorem intervalHorner_subset (p : Coeffs) {I J : QInterval}
    (hv : I.valid) (hs : I.subset J) : (intervalHorner p I).subset (intervalHorner p J) := by
  induction p with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons a as ih =>
    exact QInterval.add_subset ⟨le_rfl, le_rfl⟩
      (QInterval.mul_subset hv (intervalHorner_valid as hv) hs ih)

 theorem right_sign_change {a b m : ℚ} (h : a*b < 0) (hm : m ≠ 0) (hl : ¬ a*m < 0) :
    m*b < 0 := by
  rcases mul_neg_iff.mp h with h | h
  · have hp : 0 < m := by
      rcases lt_or_gt_of_ne hm with hn | hp
      · exact False.elim (hl (mul_neg_of_pos_of_neg h.1 hn))
      · exact hp
    exact mul_neg_of_pos_of_neg hp h.2
  · have hn : m < 0 := by
      rcases lt_or_gt_of_ne hm with hn | hp
      · exact hn
      · exact False.elim (hl (mul_neg_of_neg_of_pos h.1 hp))
    exact mul_neg_of_neg_of_pos hn h.2

end IntPolynomial
namespace AlgCode

 theorem validRoot_of_nested {p : IntPolynomial.Coeffs} {I J : QInterval}
    (hv : validRoot p I) (hJ : J.lower < J.upper)
    (hs : J.subset I) (hsg : IntPolynomial.horner p J.lower * IntPolynomial.horner p J.upper < 0) :
    validRoot p J := by
  refine ⟨hv.1, hv.2.1, hJ, hsg, ?_⟩
  have hm := IntPolynomial.intervalHorner_subset (IntPolynomial.derivative p) hJ.le hs
  rcases hv.2.2.2.2 with hn | hp
  · exact Or.inl (hm.2.trans_lt hn)
  · exact Or.inr (hp.trans_le hm.1)

 theorem refine_valid {c : AlgCode} (hv : c.valid) : c.refine.valid := by
  cases c with
  | rat q => trivial
  | root p I =>
    have hm := QInterval.midpoint_strict hv.2.2.1
    simp only [refine]
    split_ifs with hz hs
    · trivial
    · exact validRoot_of_nested hv hm.1 ⟨le_rfl, hm.2.le⟩ hs
    · exact validRoot_of_nested hv hm.2 ⟨hm.1.le, le_rfl⟩
        (IntPolynomial.right_sign_change hv.2.2.2.1 hz hs)

 theorem refine_denotes {c : AlgCode} {x : ℝ} (hv : c.valid) (hx : c.denotes x) :
    c.refine.denotes x := by
  cases c with
  | rat q => exact hx
  | root p I =>
    have hm := QInterval.midpoint_strict hv.2.2.1
    have hmr : (I.lower : ℝ) < (I.midpoint : ℝ) ∧ (I.midpoint : ℝ) < (I.upper : ℝ) := by
      exact_mod_cast hm
    have hu := IntPolynomial.unique_on_of_derivative_excludes p hv.2.2.2.2
    simp only [refine]
    split_ifs with hz hs
    · change x = (I.midpoint : ℝ)
      apply hu ⟨hx.2.1.le, hx.2.2.le⟩ ⟨hmr.1.le, hmr.2.le⟩
      rw [hx.1]
      have hzr : IntPolynomial.horner p (I.midpoint : ℝ) = 0 := by
        rw [← IntPolynomial.cast_horner, hz, Rat.cast_zero]
      exact hzr.symm
    · obtain ⟨y, hy, hl, hr⟩ := IntPolynomial.sign_change_exists p (I := ⟨I.lower, I.midpoint⟩) hm.1 hs
      have hxy : y = x := hu ⟨hl.le, hr.le.trans hmr.2.le⟩
        ⟨hx.2.1.le, hx.2.2.le⟩ (hy.trans hx.1.symm)
      subst y
      exact ⟨hx.1, hl, hr⟩
    · have hsr := IntPolynomial.right_sign_change hv.2.2.2.1 hz hs
      obtain ⟨y, hy, hl, hr⟩ := IntPolynomial.sign_change_exists p (I := ⟨I.midpoint, I.upper⟩) hm.2 hsr
      have hxy : y = x := hu ⟨hmr.1.le.trans hl.le, hr.le⟩
        ⟨hx.2.1.le, hx.2.2.le⟩ (hy.trans hx.1.symm)
      subst y
      exact ⟨hx.1, hl, hr⟩

 theorem iterate_code_valid {c : AlgCode} (hv : c.valid) (n : ℕ) : (c.iterate n).valid := by
  induction n with
  | zero => exact hv
  | succ n ih => exact refine_valid ih

 theorem iterate_denotes {c : AlgCode} {x : ℝ} (hv : c.valid) (hx : c.denotes x) (n : ℕ) :
    (c.iterate n).denotes x := by
  induction n with
  | zero => exact hx
  | succ n ih => exact refine_denotes (iterate_code_valid hv n) ih

end AlgCode
end Cover
