import Cover.AlgebraicComparison

namespace Cover
namespace AlgCode

/-- A direct finite certificate, not an asserted generator trace. -/
def refinementEvidence (original candidate : AlgCode) : Prop :=
  match original, candidate with
  | .rat q, .rat q' => q = q'
  | .rat _, .root _ _ => False
  | .root p I, .rat q => I.lower < q ∧ q < I.upper ∧ IntPolynomial.horner p q = 0
  | .root p I, .root p' J => p' = p ∧ J.subset I ∧ J.lower < J.upper ∧
      IntPolynomial.horner p J.lower * IntPolynomial.horner p J.upper < 0

instance (original candidate : AlgCode) : Decidable (refinementEvidence original candidate) := by
  cases original <;> cases candidate <;> unfold refinementEvidence QInterval.subset <;> infer_instance

/-- The original input, exact canonical polynomial, width and positivity are all rechecked. -/
def verifyRefinement (original candidate : AlgCode) (h : ℚ) (positive : Bool) : Bool :=
  decide (original.valid ∧ refinementEvidence original candidate ∧
    candidate.interval.width ≤ h ∧ (positive = true → 0 < candidate.interval.lower))

 theorem refinementEvidence_sound {original candidate : AlgCode} {x : ℝ}
    (hv : original.valid) (hx : original.denotes x)
    (he : refinementEvidence original candidate) : candidate.valid ∧ candidate.denotes x := by
  cases original with
  | rat q =>
    cases candidate with
    | rat q' => cases he; exact ⟨trivial, hx⟩
    | root p I => exact False.elim he
  | root p I =>
    cases candidate with
    | rat q =>
      refine ⟨trivial, ?_⟩
      have hq : IntPolynomial.horner p (q : ℝ) = 0 := by
        rw [← IntPolynomial.cast_horner, he.2.2, Rat.cast_zero]
      exact IntPolynomial.unique_on_of_derivative_excludes p hv.2.2.2.2
        ⟨hx.2.1.le, hx.2.2.le⟩
        ⟨by exact_mod_cast he.1.le, by exact_mod_cast he.2.1.le⟩ (hx.1.trans hq.symm)
    | root p' J =>
      obtain ⟨heq, hs, hj, hsg⟩ := he
      subst p'
      have hnew := validRoot_of_nested hv hj hs hsg
      obtain ⟨y, hy, _⟩ := validAlgBracket_denotes_unique (.root p I) hv
      obtain ⟨z, hz, _⟩ := validAlgBracket_denotes_unique (.root p J) hnew
      have hzI : I.contains z := QInterval.contains_of_subset hs (denotes_contains hz)
      have hzx : z = x := IntPolynomial.unique_on_of_derivative_excludes p hv.2.2.2.2
        hzI ⟨hx.2.1.le, hx.2.2.le⟩ (hz.1.trans hx.1.symm)
      subst z
      exact ⟨hnew, hz⟩

 theorem verifyRefinement_sound {original candidate : AlgCode} {x : ℝ} {h : ℚ} {positive : Bool}
    (hx : original.denotes x) (hv : verifyRefinement original candidate h positive = true) :
    original.valid ∧ candidate.valid ∧ candidate.denotes x ∧ candidate.interval.width ≤ h ∧
      (positive = true → 0 < candidate.interval.lower) := by
  simp only [verifyRefinement, decide_eq_true_eq] at hv
  obtain ⟨hc, hd⟩ := refinementEvidence_sound hv.1 hx hv.2.1
  exact ⟨hv.1, hc, hd, hv.2.2⟩

 theorem refineToPrecision_sound {c d : AlgCode} {x : ℝ} {h : ℚ}
    (hv : c.valid) (hx : c.denotes x) (n : ℕ) (hs : refineToPrecision h n c = some d) :
    d.valid ∧ d.denotes x ∧ d.interval.width ≤ h ∧ d.interval.subset c.interval := by
  induction n generalizing c with
  | zero =>
    simp only [refineToPrecision] at hs
    split_ifs at hs with hh
    cases hs
    exact ⟨hv, hx, hh, le_rfl, le_rfl⟩
  | succ n ih =>
    simp only [refineToPrecision] at hs
    split_ifs at hs with hh
    · cases hs
      exact ⟨hv, hx, hh, le_rfl, le_rfl⟩
    · obtain ⟨vd, hd, wd, sd⟩ := ih (refine_valid hv) (refine_denotes hv hx) hs
      have sc := refine_nested c (valid_interval hv)
      exact ⟨vd, hd, wd, sc.1.trans sd.1, sd.2.trans sc.2⟩

 theorem positiveBracket_sound {c d : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) (n : ℕ) (hs : positiveBracket n c = some d) :
    d.valid ∧ d.denotes x ∧ 0 < d.interval.lower ∧ d.interval.subset c.interval := by
  induction n generalizing c with
  | zero =>
    simp only [positiveBracket] at hs
    split_ifs at hs with hh
    cases hs
    exact ⟨hv, hx, hh, le_rfl, le_rfl⟩
  | succ n ih =>
    simp only [positiveBracket] at hs
    split_ifs at hs with hh
    · cases hs
      exact ⟨hv, hx, hh, le_rfl, le_rfl⟩
    · obtain ⟨vd, hd, wd, sd⟩ := ih (refine_valid hv) (refine_denotes hv hx) hs
      have sc := refine_nested c (valid_interval hv)
      exact ⟨vd, hd, wd, sc.1.trans sd.1, sd.2.trans sc.2⟩

end AlgCode
end Cover
