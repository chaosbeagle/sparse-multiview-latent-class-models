import Cover.RefinementEvidence
import Cover.AlgebraicAdequacy

namespace Cover
namespace IntPolynomial

/-- Public zero bytes are [0]; empty lists and padded lists are rejected by the parser. -/
def serializeCoeffs (p : Coeffs) : Coeffs :=
  if trim p = [] then [0] else trim p

def parseCoeffs (raw : Coeffs) : Option Coeffs :=
  if raw = [0] then some [] else if raw ≠ [] ∧ canonical raw then some raw else none

 theorem parse_serialize (p : Coeffs) : parseCoeffs (serializeCoeffs p) = some (trim p) := by
  by_cases h : trim p = []
  · simp [serializeCoeffs, h, parseCoeffs]
  · have hn : trim p ≠ [0] := by
      intro he
      have hh := congrArg trim he
      simp only [trim_idempotent] at hh
      have hz : trim [0] = [] := by decide
      rw [hz] at hh
      exact h hh
    simp [serializeCoeffs, h, parseCoeffs, hn, canonical_trim]

 theorem serialize_parse {raw p : Coeffs} (h : parseCoeffs raw = some p) : serializeCoeffs p = raw := by
  unfold parseCoeffs at h
  split_ifs at h with h0 hc
  · cases h
    simp [serializeCoeffs, trim, h0]
  · cases h
    have ht : trim raw = raw := hc.2
    simp [serializeCoeffs, ht, hc.1]

end IntPolynomial
namespace AlgCode

def thirdRoot : AlgCode := .root [-1, 3] ⟨0, 1⟩

 theorem thirdRoot_valid : thirdRoot.valid := by
  norm_num [thirdRoot, valid, validRoot, IntPolynomial.canonical, IntPolynomial.trim,
    IntPolynomial.horner, IntPolynomial.derivative, IntPolynomial.derivativeAux,
    IntPolynomial.intervalHorner, QInterval.singleton, QInterval.add, QInterval.mul]
 theorem thirdRoot_denotes : thirdRoot.denotes (1/3 : ℝ) := by
  norm_num [thirdRoot, denotes, IntPolynomial.horner]

 theorem dyadic_ne_third (a : ℤ) (n : ℕ) : (a : ℚ) / (2 : ℚ)^n ≠ 1/3 := by
  intro h
  have he : (a : ℚ) * 3 = (2 : ℚ)^n := by
    simpa using (div_eq_div_iff (pow_ne_zero n (by norm_num)) (by norm_num : (3 : ℚ) ≠ 0)).mp h
  have hi : a * 3 = (2 : ℤ)^n := by exact_mod_cast he
  have hd : (3 : ℤ) ∣ (2 : ℤ)^n := ⟨a, by nlinarith [hi]⟩
  have hb := Int.prime_three.dvd_of_dvd_pow hd
  norm_num at hb

 theorem third_polynomial_midpoint_ne_zero {I : QInterval} {n : ℕ}
    (hl : ∃ a : ℤ, I.lower = (a : ℚ)/(2 : ℚ)^n)
    (hu : ∃ b : ℤ, I.upper = (b : ℚ)/(2 : ℚ)^n) :
    IntPolynomial.horner [-1,3] I.midpoint ≠ 0 := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hu
  intro he
  have hr : I.midpoint = (1/3 : ℚ) := by
    norm_num [IntPolynomial.horner] at he
    linarith
  apply dyadic_ne_third (a+b) (n+1)
  calc
    ((a+b : ℤ) : ℚ) / (2 : ℚ)^(n+1) = I.midpoint := by
      simp only [QInterval.midpoint, ha, hb, pow_succ, Int.cast_add]
      ring
    _ = 1/3 := hr

/-- The actual rational-valued Root never hits a midpoint, at any finite depth. -/
 theorem thirdRoot_iterate_stays_root (n : ℕ) :
    ∃ I : QInterval, thirdRoot.iterate n = .root [-1,3] I ∧
      (∃ a : ℤ, I.lower = (a : ℚ)/(2 : ℚ)^n) ∧
      (∃ b : ℤ, I.upper = (b : ℚ)/(2 : ℚ)^n) := by
  induction n with
  | zero => exact ⟨⟨0,1⟩, rfl, ⟨0, by norm_num⟩, ⟨1, by norm_num⟩⟩
  | succ n ih =>
    obtain ⟨I, hi, ⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    have hm := third_polynomial_midpoint_ne_zero ⟨a, ha⟩ ⟨b, hb⟩
    have hmid : I.midpoint = ((a+b : ℤ) : ℚ)/(2 : ℚ)^(n+1) := by
      simp only [QInterval.midpoint, ha, hb, pow_succ, Int.cast_add]
      ring
    have hlo : I.lower = ((2*a : ℤ) : ℚ)/(2 : ℚ)^(n+1) := by
      simp only [ha, pow_succ, Int.cast_mul, Int.cast_ofNat]
      field_simp
    have hup : I.upper = ((2*b : ℤ) : ℚ)/(2 : ℚ)^(n+1) := by
      simp only [hb, pow_succ, Int.cast_mul, Int.cast_ofNat]
      field_simp
    simp only [iterate, hi, refine, hm, ↓reduceIte]
    split_ifs
    · exact ⟨⟨I.lower, I.midpoint⟩, rfl, ⟨2*a, hlo⟩, ⟨a+b, hmid⟩⟩
    · exact ⟨⟨I.midpoint, I.upper⟩, rfl, ⟨a+b, hmid⟩, ⟨2*b, hup⟩⟩

 theorem thirdRoot_precision_terminates (h : ℚ) (hh : 0 < h) :
    ∃ n d, refineToPrecision h n thirdRoot = some d ∧ d.interval.width ≤ h :=
  refine_to_precision_terminates thirdRoot (valid_interval thirdRoot_valid) h hh

example : compareBracketRat (1/3) 0 thirdRoot = some .eq := by
  norm_num [compareBracketRat, compareStep, thirdRoot, IntPolynomial.horner]
example : compareBracketRat 0 0 thirdRoot = some .gt := by decide
example : compareBracketRat 1 0 thirdRoot = some .lt := by decide
example : refineToPrecision (1/16) 4 thirdRoot ≠ none := by
  norm_num [refineToPrecision, thirdRoot, interval, refine, QInterval.width,
    QInterval.midpoint, IntPolynomial.horner]
  intro h; cases h
example : verifyRefinement thirdRoot (.rat (1/3)) (1/1000) true = true := by
  simp only [verifyRefinement, decide_eq_true_eq]
  refine ⟨thirdRoot_valid, ?_, ?_, ?_⟩
  · norm_num [refinementEvidence, thirdRoot, IntPolynomial.horner]
  · norm_num [interval, QInterval.width, QInterval.singleton]
  · norm_num [interval, QInterval.singleton]
example : verifyRefinement thirdRoot (.root [-1,2] ⟨0,1⟩) 1 false = false := by
  simp [verifyRefinement, refinementEvidence, thirdRoot]

end AlgCode
end Cover
