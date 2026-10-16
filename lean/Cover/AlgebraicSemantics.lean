import Cover.AlgebraicRefinement
import Cover.Interval

namespace Cover
namespace IntPolynomial

 theorem intervalHorner_sound (p : Coeffs) {I : QInterval} {x : ℝ} (hx : I.contains x) :
    (intervalHorner p I).contains (horner p x) := by
  induction p with
  | nil => simpa [intervalHorner, horner] using QInterval.singleton_contains 0
  | cons a as ih =>
    exact QInterval.add_contains (by simpa using QInterval.singleton_contains (a : ℚ))
      (QInterval.mul_contains hx ih)

 theorem horner_derivativeAux_succ {R : Type*} [CommRing R] (p : Coeffs) (n : ℕ) (x : R) :
    horner (derivativeAux (n+1) p) x = horner p x + horner (derivativeAux n p) x := by
  induction p generalizing n with
  | nil => simp [derivativeAux, horner]
  | cons a as ih =>
    simp only [derivativeAux, horner, Int.cast_mul, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
    rw [ih]
    push_cast
    ring

 theorem horner_derivativeAux_zero {R : Type*} [CommRing R] (p : Coeffs) (x : R) :
    horner (derivativeAux 0 p) x = x * horner (derivative p) x := by
  cases p <;> simp [derivativeAux, derivative, horner]

 theorem horner_derivative_cons {R : Type*} [CommRing R] (a : ℤ) (p : Coeffs) (x : R) :
    horner (derivative (a::p)) x = horner p x + x * horner (derivative p) x := by
  simpa only [derivative, Nat.zero_add, horner_derivativeAux_zero] using
    horner_derivativeAux_succ p 0 x

 theorem hasDerivAt_horner (p : Coeffs) (x : ℝ) :
    HasDerivAt (horner p) (horner (derivative p) x) x := by
  induction p with
  | nil => simpa [horner, derivative] using hasDerivAt_const x (0 : ℝ)
  | cons a as ih =>
    rw [horner_derivative_cons]
    simpa only [Pi.mul_apply, id_eq, one_mul, horner] using
      ((hasDerivAt_id x).mul ih).const_add (a : ℝ)

 theorem sign_change_exists (p : Coeffs) {I : QInterval}
    (hlt : I.lower < I.upper) (hsg : horner p I.lower * horner p I.upper < 0) :
    ∃ x : ℝ, horner p x = 0 ∧ (I.lower : ℝ) < x ∧ x < (I.upper : ℝ) := by
  have hab : (I.lower : ℝ) < I.upper := by exact_mod_cast hlt
  have hsg' : horner p (I.lower : ℝ) * horner p (I.upper : ℝ) < 0 := by
    have hh : ((horner p I.lower * horner p I.upper : ℚ) : ℝ) < 0 := by exact_mod_cast hsg
    simpa only [Rat.cast_mul, cast_horner] using hh
  have hc := (continuous_horner p).continuousOn (s := Set.Icc (I.lower : ℝ) (I.upper : ℝ))
  have hneL : horner p (I.lower : ℝ) ≠ 0 := by intro he; rw [he, zero_mul] at hsg'; exact lt_irrefl _ hsg'
  have hneU : horner p (I.upper : ℝ) ≠ 0 := by intro he; rw [he, mul_zero] at hsg'; exact lt_irrefl _ hsg'
  have hh : ∃ x ∈ Set.Icc (I.lower : ℝ) (I.upper : ℝ), horner p x = 0 := by
    rcases mul_neg_iff.mp hsg' with h | h
    · exact intermediate_value_Icc' hab.le hc ⟨h.2.le, h.1.le⟩
    · exact intermediate_value_Icc hab.le hc ⟨h.1.le, h.2.le⟩
  obtain ⟨x, hx, hp⟩ := hh
  refine ⟨x, hp, lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
  · intro he; apply hneL; rw [he]; exact hp
  · intro he; apply hneU; rw [← he]; exact hp

 theorem unique_on_of_derivative_excludes (p : Coeffs) {I : QInterval}
    (hex : (intervalHorner (derivative p) I).upper < 0 ∨
      0 < (intervalHorner (derivative p) I).lower) :
    Set.InjOn (horner p : ℝ → ℝ) (Set.Icc (I.lower : ℝ) (I.upper : ℝ)) := by
  rcases hex with hneg | hpos
  · apply StrictAntiOn.injOn
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_horner p).continuousOn
    intro x hx
    have hxi : I.contains x := (show x ∈ Set.Icc (I.lower : ℝ) (I.upper : ℝ) from interior_subset hx)
    have hb := intervalHorner_sound (derivative p) hxi
    rw [(hasDerivAt_horner p x).deriv]
    exact hb.2.trans_lt (by exact_mod_cast hneg)
  · apply StrictMonoOn.injOn
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_horner p).continuousOn
    intro x hx
    have hxi : I.contains x := (show x ∈ Set.Icc (I.lower : ℝ) (I.upper : ℝ) from interior_subset hx)
    have hb := intervalHorner_sound (derivative p) hxi
    rw [(hasDerivAt_horner p x).deriv]
    exact lt_of_lt_of_le (by exact_mod_cast hpos) hb.1

end IntPolynomial
namespace AlgCode

 theorem denotes_contains {c : AlgCode} {x : ℝ} (h : c.denotes x) : c.interval.contains x := by
  cases c with
  | rat q => subst x; exact QInterval.singleton_contains q
  | root p I => exact ⟨h.2.1.le, h.2.2.le⟩

 theorem valid_interval {c : AlgCode} (h : c.valid) : c.interval.valid := by
  cases c with
  | rat q => exact le_rfl
  | root p I => exact h.2.2.1.le

 theorem validAlgBracket_denotes_unique (c : AlgCode) (h : c.valid) : ∃! x : ℝ, c.denotes x := by
  cases c with
  | rat q => exact ⟨(q : ℝ), rfl, fun _ he => he⟩
  | root p I =>
    obtain ⟨x, hp, hl, hu⟩ := IntPolynomial.sign_change_exists p h.2.2.1 h.2.2.2.1
    refine ⟨x, ⟨hp, hl, hu⟩, ?_⟩
    intro y hy
    exact IntPolynomial.unique_on_of_derivative_excludes p h.2.2.2.2
      ⟨hy.2.1.le, hy.2.2.le⟩ ⟨hl.le, hu.le⟩ (hy.1.trans hp.symm)

end AlgCode
end Cover
