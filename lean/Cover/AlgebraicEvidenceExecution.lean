import Cover.AlgebraicPreparation

namespace Cover.AlgCode

 theorem refinementEvidence_refl {c : AlgCode} (hv : c.valid) : refinementEvidence c c := by
  cases c with
  | rat q => rfl
  | root p I => exact ⟨rfl, ⟨le_rfl, le_rfl⟩, hv.2.2.1, hv.2.2.2.1⟩

 theorem refinementEvidence_trans {a b c : AlgCode}
    (hab : refinementEvidence a b) (hbc : refinementEvidence b c) : refinementEvidence a c := by
  cases a with
  | rat q =>
    cases b with
    | rat r => cases hab; exact hbc
    | root p I => exact False.elim hab
  | root p I =>
    cases b with
    | rat r =>
      cases c with
      | rat s => cases hbc; exact hab
      | root q J => exact False.elim hbc
    | root q J =>
      obtain ⟨hpq, hs, hj, hsg⟩ := hab
      subst q
      cases c with
      | rat r => exact ⟨hs.1.trans_lt hbc.1, hbc.2.1.trans_le hs.2, hbc.2.2⟩
      | root r K =>
        obtain ⟨hr, ht, hk, hkg⟩ := hbc
        exact ⟨hr, ⟨hs.1.trans ht.1, ht.2.trans hs.2⟩, hk, hkg⟩

 theorem refine_evidence {c : AlgCode} (hv : c.valid) : refinementEvidence c c.refine := by
  cases c with
  | rat q => rfl
  | root p I =>
    have hm := QInterval.midpoint_strict hv.2.2.1
    simp only [refine]
    split_ifs with hz hs
    · exact ⟨hm.1, hm.2, hz⟩
    · exact ⟨rfl, ⟨le_rfl, hm.2.le⟩, hm.1, hs⟩
    · exact ⟨rfl, ⟨hm.1.le, le_rfl⟩, hm.2,
        IntPolynomial.right_sign_change hv.2.2.2.1 hz hs⟩

 theorem refineToPrecision_evidence {c d : AlgCode} {h : ℚ} (hv : c.valid)
    (n : ℕ) (hs : refineToPrecision h n c = some d) : refinementEvidence c d := by
  induction n generalizing c with
  | zero =>
    simp only [refineToPrecision] at hs
    split_ifs at hs
    cases hs
    exact refinementEvidence_refl hv
  | succ n ih =>
    simp only [refineToPrecision] at hs
    split_ifs at hs
    · cases hs; exact refinementEvidence_refl hv
    · exact refinementEvidence_trans (refine_evidence hv) (ih (refine_valid hv) hs)

 theorem positiveBracket_evidence {c d : AlgCode} (hv : c.valid)
    (n : ℕ) (hs : positiveBracket n c = some d) : refinementEvidence c d := by
  induction n generalizing c with
  | zero =>
    simp only [positiveBracket] at hs
    split_ifs at hs
    cases hs
    exact refinementEvidence_refl hv
  | succ n ih =>
    simp only [positiveBracket] at hs
    split_ifs at hs
    · cases hs; exact refinementEvidence_refl hv
    · exact refinementEvidence_trans (refine_evidence hv) (ih (refine_valid hv) hs)

 theorem refinePrecisely_evidence {c : AlgCode} (hv : c.valid) {h : ℚ} (hh : 0 < h) :
    refinementEvidence c (refinePrecisely c h) := by
  obtain ⟨d, hd, _⟩ := refineToPrecision_success_of_iterate h c (precisionFuel c h)
    ((iterate_width c (valid_interval hv) _).trans (precisionFuel_suffices c h hh))
  simp only [refinePrecisely, hd, Option.getD_some]
  exact refineToPrecision_evidence hv _ hd

 theorem positiveTotal_evidence {c : AlgCode} (hv : c.valid) (hp : compareTotal c hv 0 = .gt) :
    refinementEvidence c (positiveTotal c hv hp) :=
  positiveBracket_evidence hv _ (Option.some_get _).symm

 theorem prepareMargin_evidence {c : AlgCode} (hv : c.valid) (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    refinementEvidence c (prepareMargin c hv hp s) := by
  obtain ⟨x, hx, _⟩ := validAlgBracket_denotes_unique c hv
  have hpv := (positiveTotal_sound hv hx hp).1
  exact refinementEvidence_trans (positiveTotal_evidence hv hp)
    (refinePrecisely_evidence hpv (marginMesh_pos s))

 theorem prepareMargin_verified {c : AlgCode} (hv : c.valid) (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    verifyRefinement c (prepareMargin c hv hp s) (marginMesh s) true = true := by
  obtain ⟨x, hx, _⟩ := validAlgBracket_denotes_unique c hv
  have hs := prepareMargin_sound hv hx hp s
  simp only [verifyRefinement, decide_eq_true_eq]
  exact ⟨hv, prepareMargin_evidence hv hp s, hs.2.2.2.1, fun _ => hs.2.2.1⟩

end Cover.AlgCode
