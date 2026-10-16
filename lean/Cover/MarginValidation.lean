import Cover.AlgebraicTotal

namespace Cover.AlgCode

/-- Exact scalar range, with finite code validity included. -/
def validMargin (c : AlgCode) (upper : ℚ) : Prop :=
  c.valid ∧ ∃ x : ℝ, c.denotes x ∧ 0 < x ∧ x ≤ (upper : ℝ)

/-- Total finite-data input check; positivity and the inclusive upper boundary use exact comparison. -/
def validateMargin (c : AlgCode) (upper : ℚ) : Bool :=
  if hv : c.valid then decide (compareTotal c hv 0 = .gt ∧ compareTotal c hv upper ≠ .gt)
  else false

 theorem validateMargin_iff (c : AlgCode) (upper : ℚ) :
    validateMargin c upper = true ↔ validMargin c upper := by
  by_cases hv : c.valid
  · obtain ⟨x, hx, hu⟩ := validAlgBracket_denotes_unique c hv
    rw [validateMargin, dif_pos hv, decide_eq_true_eq]
    simp only [ne_eq, compareTotal_eq_gt_iff hv hx 0, compareTotal_eq_gt_iff hv hx upper]
    simp only [Rat.cast_zero, not_lt]
    constructor
    · intro h; exact ⟨hv, x, hx, h⟩
    · rintro ⟨_, y, hy, hp, hb⟩
      have he : y = x := hu y hy
      subst y
      exact ⟨hp, hb⟩
  · simp [validateMargin, hv, validMargin]

/-- The design validator separately enforces r ≥ 2. This check has total semantics even at r=0. -/
def validateMargins (r : ℕ) (w sigma : AlgCode) : Bool :=
  validateMargin w (1/(r : ℚ)) && validateMargin sigma 1

 theorem validateMargins_iff (r : ℕ) (w sigma : AlgCode) :
    validateMargins r w sigma = true ↔
      w.valid ∧ sigma.valid ∧ ∃ w0 sigma0 : ℝ,
        w.denotes w0 ∧ sigma.denotes sigma0 ∧
        0 < w0 ∧ w0 ≤ 1/(r : ℝ) ∧ 0 < sigma0 ∧ sigma0 ≤ 1 := by
  simp only [validateMargins, Bool.and_eq_true, validateMargin_iff, validMargin,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  constructor
  · rintro ⟨⟨hw, w0, hdw, hwp, hwu⟩, hs, sigma0, hds, hsp, hsu⟩
    exact ⟨hw, hs, w0, sigma0, hdw, hds, hwp, hwu, hsp, hsu⟩
  · rintro ⟨hw, hs, w0, sigma0, hdw, hds, hwp, hwu, hsp, hsu⟩
    exact ⟨⟨hw, w0, hdw, hwp, hwu⟩, hs, sigma0, hds, hsp, hsu⟩

inductive MarginStatus where
  | unknown
  | invalid
  | valid
  deriving DecidableEq, Repr

def classifyMargin (lo hi : Ordering) : MarginStatus :=
  if lo = .gt ∧ hi ≠ .gt then .valid else .invalid

/-- Zero fuel interrupts validation and can never classify it as invalid. -/
def validateMarginFuel (upper : ℚ) : ℕ → AlgCode → MarginStatus
  | 0, _ => .unknown
  | n+1, c =>
    if c.validate then
      match compareBracketRat 0 n c, compareBracketRat upper n c with
      | some lo, some hi => classifyMargin lo hi
      | _, _ => .unknown
    else .invalid

 theorem compareBracketRat_succ_of_some {c : AlgCode} {t : ℚ} {o : Ordering}
    (n : ℕ) (hs : compareBracketRat t n c = some o) : compareBracketRat t (n+1) c = some o := by
  induction n generalizing c with
  | zero =>
    change compareStep c t = some o at hs
    simp only [compareBracketRat, hs]
  | succ n ih =>
    simp only [compareBracketRat] at hs ⊢
    cases hc : compareStep c t with
    | some a => simpa only [hc] using hs
    | none =>
      simp only [hc] at hs ⊢
      exact ih hs

 theorem compareBracketRat_mono_fuel {c : AlgCode} {t : ℚ} {o : Ordering}
    {n m : ℕ} (hnm : n ≤ m) (hs : compareBracketRat t n c = some o) :
    compareBracketRat t m c = some o := by
  induction m, hnm using Nat.le_induction with
  | base => exact hs
  | succ m _ ih => exact compareBracketRat_succ_of_some m ih

 theorem compareBracketRat_eq_total {c : AlgCode} {t : ℚ} {o : Ordering}
    (hv : c.valid) (n : ℕ) (hs : compareBracketRat t n c = some o) : o = compareTotal c hv t := by
  obtain ⟨x, hx, _⟩ := validAlgBracket_denotes_unique c hv
  have h1 := compareBracketRat_correct hv hx n hs
  have h2 := compareTotal_correct hv hx t
  cases o <;> cases ht : compareTotal c hv t
  all_goals simp only [ht, comparisonMeaning] at h1 h2
  all_goals first | rfl | exfalso; linarith

 theorem validateMarginFuel_sound (c : AlgCode) (upper : ℚ) (n : ℕ) :
    (validateMarginFuel upper n c = .valid → validMargin c upper) ∧
    (validateMarginFuel upper n c = .invalid → ¬validMargin c upper) := by
  cases n with
  | zero => simp [validateMarginFuel]
  | succ n =>
    by_cases hv : c.valid
    · simp only [validateMarginFuel, validate, decide_eq_true hv, ↓reduceIte]
      cases hlo : compareBracketRat 0 n c with
      | none => simp
      | some lo =>
        cases hhi : compareBracketRat upper n c with
        | none => simp
        | some hi =>
          have hel := compareBracketRat_eq_total hv n hlo
          have heh := compareBracketRat_eq_total hv n hhi
          rw [hel, heh]
          have hf : validMargin c upper ↔ (compareTotal c hv 0 = .gt ∧ compareTotal c hv upper ≠ .gt) := by
            rw [← validateMargin_iff, validateMargin, dif_pos hv, decide_eq_true_eq]
          simp only [classifyMargin]
          split_ifs with h
          · exact ⟨fun _ => hf.mpr h, by intro hbad; cases hbad⟩
          · constructor
            · intro hbad; cases hbad
            · exact fun _ he => h (hf.mp he)
    · simp [validateMarginFuel, validate, hv, validMargin]

/-- A concrete computed bound after which the capped checker has its exact answer. -/
def marginValidationFuel (c : AlgCode) (hv : c.valid) (upper : ℚ) : ℕ :=
  max (comparisonFuel c hv 0) (comparisonFuel c hv upper) + 1

 theorem validateMarginFuel_eventually (c : AlgCode) (upper : ℚ) :
    ∃ N : ℕ, ∀ n ≥ N, validateMarginFuel upper n c =
      if validateMargin c upper then .valid else .invalid := by
  by_cases hv : c.valid
  · refine ⟨marginValidationFuel c hv upper, ?_⟩
    intro n hn
    cases n with
    | zero => simp only [marginValidationFuel] at hn; omega
    | succ n =>
      have hl : comparisonFuel c hv 0 ≤ n := by
        have hm := le_max_left (comparisonFuel c hv 0) (comparisonFuel c hv upper)
        dsimp [marginValidationFuel] at hn
        omega
      have hh : comparisonFuel c hv upper ≤ n := by
        have hm := le_max_right (comparisonFuel c hv 0) (comparisonFuel c hv upper)
        dsimp [marginValidationFuel] at hn
        omega
      have hcl : compareBracketRat 0 n c = some (compareTotal c hv 0) :=
        compareBracketRat_mono_fuel hl (Option.some_get _).symm
      have hch : compareBracketRat upper n c = some (compareTotal c hv upper) :=
        compareBracketRat_mono_fuel hh (Option.some_get _).symm
      simp [validateMarginFuel, validate, hv, hcl, hch, classifyMargin, validateMargin]
  · refine ⟨1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n => simp [validateMarginFuel, validateMargin, validate, hv]

end Cover.AlgCode

namespace Cover.Margins
open AlgCode

/-- All decisions here are exact finite-data computations. -/
def Valid (r : ℕ) (w sigma : AlgCode) : Prop := validateMargins r w sigma = true
instance (r : ℕ) (w sigma : AlgCode) : Decidable (Valid r w sigma) :=
  inferInstanceAs (Decidable (validateMargins r w sigma = true))

 theorem valid_codes {r : ℕ} {w sigma : AlgCode} (h : Valid r w sigma) :
    w.valid ∧ sigma.valid := by
  have hh := (validateMargins_iff r w sigma).mp h
  exact ⟨hh.1, hh.2.1⟩

 theorem valid_comparisons {r : ℕ} {w sigma : AlgCode} (h : Valid r w sigma) :
    ∃ hw : w.valid, ∃ hs : sigma.valid,
      compareTotal w hw 0 = .gt ∧ compareTotal w hw (1/(r : ℚ)) ≠ .gt ∧
      compareTotal sigma hs 0 = .gt ∧ compareTotal sigma hs 1 ≠ .gt := by
  obtain ⟨hw, hs, w0, s0, hdw, hds, hwp, hwu, hsp, hsu⟩ := (validateMargins_iff r w sigma).mp h
  refine ⟨hw, hs, ?_, ?_, ?_, ?_⟩
  · exact (compareTotal_eq_gt_iff hw hdw 0).2 (by simpa using hwp)
  · intro he
    have hb := (compareTotal_eq_gt_iff hw hdw (1/(r : ℚ))).1 he
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at hb
    exact not_lt_of_ge hwu hb
  · exact (compareTotal_eq_gt_iff hs hds 0).2 (by simpa using hsp)
  · intro he
    have hb := (compareTotal_eq_gt_iff hs hds 1).1 he
    norm_cast at hb
    exact not_lt_of_ge hsu hb

 theorem valid_iff {r : ℕ} {w sigma : AlgCode} : Valid r w sigma ↔
      w.valid ∧ sigma.valid ∧ ∃ w0 sigma0 : ℝ,
        w.denotes w0 ∧ sigma.denotes sigma0 ∧
        0 < w0 ∧ w0 ≤ 1/(r : ℝ) ∧ 0 < sigma0 ∧ sigma0 ≤ 1 :=
  validateMargins_iff r w sigma

end Cover.Margins
