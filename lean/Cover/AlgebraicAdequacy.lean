import Cover.AlgebraicComparison
import Cover.Horner
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.GaussLemma

namespace Cover
namespace IntPolynomial

 theorem toPolynomial_surjective (p : Polynomial ℤ) : ∃ cs : Coeffs, toPolynomial cs = p := by
  induction p using Polynomial.recOnHorner with
  | M0 => exact ⟨[], rfl⟩
  | MC p a _ _ ih =>
    obtain ⟨cs, rfl⟩ := ih
    cases cs with
    | nil => exact ⟨[a], by simp [toPolynomial]⟩
    | cons b bs => exact ⟨(b+a)::bs, by simp [toPolynomial]; ring⟩
  | MX p _ ih =>
    obtain ⟨cs, rfl⟩ := ih
    exact ⟨0::cs, by simp [toPolynomial, mul_comm]⟩

 theorem canonical_representable (p : Polynomial ℤ) :
    ∃ cs : Coeffs, canonical cs ∧ toPolynomial cs = p := by
  obtain ⟨cs, hcs⟩ := toPolynomial_surjective p
  exact ⟨trim cs, canonical_trim cs, by simpa using hcs⟩

 theorem aeval_toPolynomial (p : Coeffs) (x : ℝ) :
    Polynomial.aeval x (toPolynomial p) = horner p x := by
  rw [Polynomial.aeval_def]
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := Subsingleton.elim _ _
  rw [hm]
  exact eval_toPolynomial p x

 theorem list_length_of_derivative_ne_zero {cs : Coeffs} {x : ℝ}
    (hn : horner (derivative cs) x ≠ 0) : 2 ≤ cs.length := by
  cases cs with
  | nil => simp [derivative, horner] at hn
  | cons a as =>
    cases as with
    | nil => simp [derivative, derivativeAux, horner] at hn
    | cons b bs => simp

 theorem simple_integer_polynomial_of_algebraic {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ p : Polynomial ℤ, p ≠ 0 ∧ Polynomial.aeval x p = 0 ∧
      Polynomial.aeval x (Polynomial.derivative p) ≠ 0 := by
  classical
  letI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hz : IsAlgebraic ℤ x := hx.restrictScalars ℤ
  have hex : ∃ n : ℕ, ∃ p : Polynomial ℤ,
      p.natDegree = n ∧ p ≠ 0 ∧ Polynomial.aeval x p = 0 := by
    obtain ⟨p, hp, hr⟩ := hz
    exact ⟨p.natDegree, p, rfl, hp, hr⟩
  obtain ⟨p, hdeg, hp, hr⟩ := Nat.find_spec hex
  have hd : p.natDegree ≠ 0 := by
    intro he
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero he
    have hv := hr
    rw [hconst, Polynomial.aeval_C] at hv
    have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := Subsingleton.elim _ _
    rw [hm] at hv
    change ((p.coeff 0 : ℤ) : ℝ) = 0 at hv
    have hz : p.coeff 0 = 0 := by exact_mod_cast hv
    apply hp
    rw [hconst, hz, Polynomial.C_0]
  refine ⟨p, hp, hr, ?_⟩
  intro hder
  have hm := Nat.find_min' hex (m := (Polynomial.derivative p).natDegree)
    ⟨Polynomial.derivative p, rfl, Polynomial.derivative_ne_zero.mpr hd, hder⟩
  have hlt := Polynomial.natDegree_derivative_lt hd
  omega

 theorem simple_canonical_list_of_algebraic {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ p : Coeffs, canonical p ∧ 2 ≤ p.length ∧ horner p x = 0 ∧ horner (derivative p) x ≠ 0 := by
  obtain ⟨P, _, hp, hd⟩ := simple_integer_polynomial_of_algebraic hx
  obtain ⟨p, hc, hP⟩ := canonical_representable P
  have he : horner p x = 0 := by rw [← aeval_toPolynomial, hP]; exact hp
  have hde : horner (derivative p) x ≠ 0 := by
    rw [← aeval_toPolynomial, derivative_toPolynomial, hP]
    exact hd
  exact ⟨p, hc, list_length_of_derivative_ne_zero hde, he, hde⟩

 theorem intervalHorner_as_hornerInterval (p : Coeffs) (I : QInterval) :
    intervalHorner p I = hornerInterval (p.map (fun a : ℤ => (a : ℚ))) I := by
  induction p with
  | nil => rfl
  | cons a as ih => simp only [intervalHorner, List.map_cons, hornerInterval_cons, ih]

 theorem horner_as_hornerValue (p : Coeffs) (x : ℝ) :
    horner p x = hornerValue (p.map (fun a : ℤ => (a : ℚ))) x := by
  induction p with
  | nil => rfl
  | cons a as ih => simp [horner, hornerValue, ih]

 theorem intervalHorner_eventually_excludes_zero (p : Coeffs) (x : ℝ) (hn : horner p x ≠ 0) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ I : QInterval, I.contains x → I.width ≤ δ →
      (intervalHorner p I).upper < 0 ∨ 0 < (intervalHorner p I).lower := by
  rw [horner_as_hornerValue] at hn
  obtain ⟨δ, hδ, hc⟩ := hornerInterval_eventually_excludes_zero _ x hn
  exact ⟨δ, hδ, fun I hx hw => by simpa [intervalHorner_as_hornerInterval, or_comm] using hc I hx hw⟩

theorem simple_root_has_bracket {p : Coeffs} {x : ℝ}
    (hp : horner p x = 0) (hd : horner (derivative p) x ≠ 0) :
    ∃ I : QInterval, I.lower < I.upper ∧
      horner p I.lower * horner p I.upper < 0 ∧
      ((intervalHorner (derivative p) I).upper < 0 ∨
        0 < (intervalHorner (derivative p) I).lower) ∧
      (I.lower : ℝ) < x ∧ x < (I.upper : ℝ) := by
  obtain ⟨δ, hδ, hcert⟩ := intervalHorner_eventually_excludes_zero (derivative p) x hd
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨l, hll, hl⟩ := exists_rat_btwn (sub_lt_self x (half_pos hδr))
  obtain ⟨u, hu, huu⟩ := exists_rat_btwn (lt_add_of_pos_right x (half_pos hδr))
  let I : QInterval := ⟨l, u⟩
  have hI : I.contains x := ⟨hl.le, hu.le⟩
  have hwidth : I.width ≤ δ := by
    have hr : (u : ℝ) - l ≤ δ := by linarith
    exact_mod_cast hr
  have hc := hcert I hI hwidth
  have hsg : horner p (l : ℝ) * horner p (u : ℝ) < 0 := by
    rcases hc with hn | hpos
    · have hm : StrictAntiOn (horner p : ℝ → ℝ) (Set.Icc (l : ℝ) (u : ℝ)) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_horner p).continuousOn
        intro y hy
        have hyI : I.contains y := (show y ∈ Set.Icc (l : ℝ) (u : ℝ) from interior_subset hy)
        have hb := intervalHorner_sound (derivative p) hyI
        rw [(hasDerivAt_horner p y).deriv]
        exact hb.2.trans_lt (by exact_mod_cast hn)
      have hpl := hm ⟨le_rfl, hl.le.trans hu.le⟩ hI hl
      have hpu := hm hI ⟨hl.le.trans hu.le, le_rfl⟩ hu
      rw [hp] at hpl hpu
      exact mul_neg_of_pos_of_neg hpl hpu
    · have hm : StrictMonoOn (horner p : ℝ → ℝ) (Set.Icc (l : ℝ) (u : ℝ)) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_horner p).continuousOn
        intro y hy
        have hyI : I.contains y := (show y ∈ Set.Icc (l : ℝ) (u : ℝ) from interior_subset hy)
        have hb := intervalHorner_sound (derivative p) hyI
        rw [(hasDerivAt_horner p y).deriv]
        exact lt_of_lt_of_le (by exact_mod_cast hpos) hb.1
      have hpl := hm ⟨le_rfl, hl.le.trans hu.le⟩ hI hl
      have hpu := hm hI ⟨hl.le.trans hu.le, le_rfl⟩ hu
      rw [hp] at hpl hpu
      exact mul_neg_of_neg_of_pos hpl hpu
  refine ⟨I, ?_, ?_, hc, hl, hu⟩
  · exact_mod_cast hl.trans hu
  · have hh : ((horner p l * horner p u : ℚ) : ℝ) < 0 := by
      simpa only [Rat.cast_mul, cast_horner] using hsg
    exact_mod_cast hh

end IntPolynomial
namespace AlgCode

/-- Every real algebraic over ℚ has a finite canonical integer-polynomial code.
All choices occur in this existence proof, not in any executable function. -/
theorem algebraic_has_certified_bracket {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ∃ c : AlgCode, c.valid ∧ c.denotes x := by
  obtain ⟨p, hc, hlen, hp, hd⟩ := IntPolynomial.simple_canonical_list_of_algebraic hx
  obtain ⟨I, hI, hsg, hdI, hl, hu⟩ := IntPolynomial.simple_root_has_bracket hp hd
  exact ⟨.root p I, ⟨hc, hlen, hI, hsg, hdI⟩, hp, hl, hu⟩

end AlgCode
end Cover
