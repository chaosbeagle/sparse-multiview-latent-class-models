import Cover.RefinementEvidence
import Mathlib.Algebra.Order.Floor.Ring

namespace Cover.AlgCode

def precisionFuel (c : AlgCode) (h : ℚ) : ℕ := ⌈c.interval.width / h⌉₊ + 1

theorem precisionFuel_suffices (c : AlgCode) (h : ℚ) (hh : 0 < h) :
    c.interval.width / (2 : ℚ)^(precisionFuel c h) ≤ h := by
  have hn : c.interval.width / h < (precisionFuel c h : ℚ) := by
    have hc := Nat.le_ceil (c.interval.width / h)
    simp only [precisionFuel, Nat.cast_add, Nat.cast_one]
    linarith
  have hp : (precisionFuel c h : ℚ) < (2 : ℚ)^(precisionFuel c h) := by
    exact_mod_cast Nat.lt_two_pow_self (n := precisionFuel c h)
  apply (div_le_iff₀ (pow_pos (by norm_num) _)).mpr
  have hm := (div_lt_iff₀ hh).mp (hn.trans hp)
  nlinarith

def refinePrecisely (c : AlgCode) (h : ℚ) : AlgCode :=
  (refineToPrecision h (precisionFuel c h) c).getD c

theorem refinePrecisely_sound {c : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) {h : ℚ} (hh : 0 < h) :
    (refinePrecisely c h).valid ∧ (refinePrecisely c h).denotes x ∧
      (refinePrecisely c h).interval.width ≤ h ∧
      (refinePrecisely c h).interval.subset c.interval := by
  obtain ⟨d, hd, _⟩ := refineToPrecision_success_of_iterate h c (precisionFuel c h)
    ((iterate_width c (valid_interval hv) _).trans (precisionFuel_suffices c h hh))
  simp only [refinePrecisely, hd, Option.getD_some]
  exact refineToPrecision_sound hv hx _ hd

 theorem comparison_has_fuel (c : AlgCode) (hv : c.valid) (t : ℚ) :
    ∃ n, (compareBracketRat t n c).isSome = true := by
  obtain ⟨n, o, ho⟩ := compareBracketRat_terminates c hv t
  exact ⟨n, by rw [ho]; rfl⟩

/-- Executable least-successful-fuel search; proof terms are erased.
The search predicate contains only the exact finite-data comparator. -/
def comparisonFuel (c : AlgCode) (hv : c.valid) (t : ℚ) : ℕ :=
  Nat.find (comparison_has_fuel c hv t)

def compareTotal (c : AlgCode) (hv : c.valid) (t : ℚ) : Ordering :=
  (compareBracketRat t (comparisonFuel c hv t) c).get (Nat.find_spec (comparison_has_fuel c hv t))

 theorem compareTotal_correct {c : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) (t : ℚ) :
    comparisonMeaning (compareTotal c hv t) x t := by
  apply compareBracketRat_correct hv hx (comparisonFuel c hv t)
  exact (Option.some_get _).symm

theorem compareTotal_eq_lt_iff {c : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) (t : ℚ) :
    compareTotal c hv t = .lt ↔ x < (t : ℝ) := by
  have hc := compareTotal_correct hv hx t
  cases he : compareTotal c hv t <;> simp_all [comparisonMeaning] <;> linarith

theorem compareTotal_eq_eq_iff {c : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) (t : ℚ) :
    compareTotal c hv t = .eq ↔ x = (t : ℝ) := by
  have hc := compareTotal_correct hv hx t
  cases he : compareTotal c hv t <;> simp_all [comparisonMeaning] <;> linarith

theorem compareTotal_eq_gt_iff {c : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) (t : ℚ) :
    compareTotal c hv t = .gt ↔ (t : ℝ) < x := by
  have hc := compareTotal_correct hv hx t
  cases he : compareTotal c hv t <;> simp_all [comparisonMeaning] <;> linarith

 theorem positive_has_fuel (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) :
    ∃ n, (positiveBracket n c).isSome = true := by
  obtain ⟨x, hx, _⟩ := validAlgBracket_denotes_unique c hv
  have hpos := compareTotal_correct hv hx 0
  rw [hp] at hpos
  have hxr : 0 < x := by simpa [comparisonMeaning] using hpos
  obtain ⟨n, d, hd, _⟩ := positiveBracket_terminates c hv hx hxr
  exact ⟨n, by rw [hd]; rfl⟩

/-- Positivity permission is itself supplied by the exact executable comparator. -/
def positiveFuel (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) : ℕ :=
  Nat.find (positive_has_fuel c hv hp)

def positiveTotal (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) : AlgCode :=
  (positiveBracket (positiveFuel c hv hp) c).get (Nat.find_spec (positive_has_fuel c hv hp))

 theorem positiveTotal_sound {c : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) (hp : compareTotal c hv 0 = .gt) :
    (positiveTotal c hv hp).valid ∧ (positiveTotal c hv hp).denotes x ∧
      0 < (positiveTotal c hv hp).interval.lower ∧
      (positiveTotal c hv hp).interval.subset c.interval := by
  apply positiveBracket_sound hv hx (positiveFuel c hv hp)
  exact (Option.some_get _).symm

end Cover.AlgCode
