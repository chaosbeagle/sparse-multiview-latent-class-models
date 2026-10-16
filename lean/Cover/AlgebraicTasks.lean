import Cover.AlgebraicEvidenceExecution
import Cover.Fuel

namespace Cover.AlgCode

 theorem comparisonMeaning_unique {o₁ o₂ : Ordering} {x : ℝ} {t : ℚ}
    (h₁ : comparisonMeaning o₁ x t) (h₂ : comparisonMeaning o₂ x t) : o₁ = o₂ := by
  cases o₁ <;> cases o₂ <;> simp only [comparisonMeaning] at h₁ h₂
  all_goals first | rfl | exfalso; linarith

 theorem compareTotal_refine_eq {c : AlgCode} (hv : c.valid) (t : ℚ) :
    compareTotal c.refine (refine_valid hv) t = compareTotal c hv t := by
  obtain ⟨x, hx, _⟩ := validAlgBracket_denotes_unique c hv
  exact comparisonMeaning_unique
    (compareTotal_correct (refine_valid hv) (refine_denotes hv hx) t) (compareTotal_correct hv hx t)

 theorem refine_positive_comparison {c : AlgCode} (hv : c.valid) (hp : compareTotal c hv 0 = .gt) :
    compareTotal c.refine (refine_valid hv) 0 = .gt := by
  rw [compareTotal_refine_eq hv]; exact hp

 theorem comparisonFuel_refine_lt {c : AlgCode} (hv : c.valid) (t : ℚ)
    (hn : compareStep c t = none) :
    comparisonFuel c.refine (refine_valid hv) t < comparisonFuel c hv t := by
  have hs := Nat.find_spec (comparison_has_fuel c hv t)
  change (compareBracketRat t (comparisonFuel c hv t) c).isSome = true at hs
  cases he : comparisonFuel c hv t with
  | zero => simp [he, compareBracketRat, hn] at hs
  | succ n =>
    rw [he] at hs
    simp only [compareBracketRat, hn] at hs
    have hle := Nat.find_min' (comparison_has_fuel c.refine (refine_valid hv) t) hs
    exact Nat.lt_succ_of_le hle

/-- A comparison test and each actual bisection are exposed as interruptible steps.
The well-founded measure is proof-only; it is not evaluated to construct the task. -/
def compareTask (c : AlgCode) (hv : c.valid) (t : ℚ) : FinTask Ordering :=
  .step fun _ => match hs : compareStep c t with
    | some o => .done o
    | none => .step fun _ => compareTask c.refine (refine_valid hv) t
termination_by comparisonFuel c hv t
decreasing_by exact comparisonFuel_refine_lt hv t hs

 theorem compareTask_result (c : AlgCode) (hv : c.valid) (t : ℚ) :
    (compareTask c hv t).result = compareTotal c hv t := by
  rw [compareTask, FinTask.result_step]
  cases hs : compareStep c t with
  | some o =>
    simp only [FinTask.result_done]
    exact compareBracketRat_eq_total hv 0 hs
  | none =>
    simp only [FinTask.result_step]
    rw [compareTask_result c.refine (refine_valid hv) t]
    exact compareTotal_refine_eq hv t
termination_by comparisonFuel c hv t
decreasing_by exact comparisonFuel_refine_lt hv t hs

def refineToPrecisionTask (h : ℚ) : ℕ → AlgCode → FinTask (Option AlgCode)
  | 0, c => .step fun _ => .done (if c.interval.width ≤ h then some c else none)
  | n+1, c => .step fun _ =>
      if c.interval.width ≤ h then .done (some c)
      else .step fun _ => refineToPrecisionTask h n c.refine

 theorem refineToPrecisionTask_result (h : ℚ) (n : ℕ) (c : AlgCode) :
    (refineToPrecisionTask h n c).result = refineToPrecision h n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [refineToPrecisionTask, FinTask.result_step, refineToPrecision]
    split_ifs <;> simp_all

def precisionTask (c : AlgCode) (h : ℚ) : FinTask AlgCode :=
  .step fun _ => do
    let d ← refineToPrecisionTask h (precisionFuel c h) c
    .done (d.getD c)

 theorem precisionTask_result (c : AlgCode) (h : ℚ) :
    (precisionTask c h).result = refinePrecisely c h := by
  simp [precisionTask, refineToPrecisionTask_result, refinePrecisely]

 theorem positiveBracket_succ_of_some {c d : AlgCode} (n : ℕ)
    (hs : positiveBracket n c = some d) : positiveBracket (n+1) c = some d := by
  induction n generalizing c with
  | zero =>
    simp only [positiveBracket] at hs ⊢
    split_ifs at hs ⊢ <;> assumption
  | succ n ih =>
    rw [positiveBracket] at hs
    rw [positiveBracket]
    by_cases hp : 0 < c.interval.lower
    · rw [if_pos hp] at hs ⊢; exact hs
    · rw [if_neg hp] at hs ⊢; exact ih hs

 theorem positiveBracket_mono_fuel {c d : AlgCode} {n m : ℕ} (hnm : n ≤ m)
    (hs : positiveBracket n c = some d) : positiveBracket m c = some d := by
  induction m, hnm using Nat.le_induction with
  | base => exact hs
  | succ m _ ih => exact positiveBracket_succ_of_some m ih

 theorem positiveBracket_unique {c d e : AlgCode} {n m : ℕ}
    (hd : positiveBracket n c = some d) (he : positiveBracket m c = some e) : d = e := by
  have h1 := positiveBracket_mono_fuel (le_max_left n m) hd
  have h2 := positiveBracket_mono_fuel (le_max_right n m) he
  exact Option.some.inj (h1.symm.trans h2)

 theorem positiveBracket_eq_total {c d : AlgCode} (hv : c.valid)
    (hp : compareTotal c hv 0 = .gt) (n : ℕ) (hs : positiveBracket n c = some d) :
    d = positiveTotal c hv hp := positiveBracket_unique hs (Option.some_get _).symm

 theorem positiveTotal_eq_self {c : AlgCode} (hv : c.valid)
    (hp : compareTotal c hv 0 = .gt) (hl : 0 < c.interval.lower) : positiveTotal c hv hp = c := by
  exact (positiveBracket_eq_total hv hp 0 (by simp [positiveBracket, hl])).symm

 theorem positiveFuel_refine_lt {c : AlgCode} (hv : c.valid) (hp : compareTotal c hv 0 = .gt)
    (hn : ¬0 < c.interval.lower) :
    positiveFuel c.refine (refine_valid hv) (refine_positive_comparison hv hp) < positiveFuel c hv hp := by
  have hs := Nat.find_spec (positive_has_fuel c hv hp)
  change (positiveBracket (positiveFuel c hv hp) c).isSome = true at hs
  cases he : positiveFuel c hv hp with
  | zero => simp [he, positiveBracket, hn] at hs
  | succ n =>
    rw [he] at hs
    simp only [positiveBracket, hn, ↓reduceIte] at hs
    have hle := Nat.find_min' (positive_has_fuel c.refine (refine_valid hv) (refine_positive_comparison hv hp)) hs
    exact Nat.lt_succ_of_le hle

 theorem positiveTotal_eq_refine {c : AlgCode} (hv : c.valid) (hp : compareTotal c hv 0 = .gt)
    (hn : ¬0 < c.interval.lower) :
    positiveTotal c hv hp = positiveTotal c.refine (refine_valid hv) (refine_positive_comparison hv hp) := by
  have hs : positiveBracket (positiveFuel c hv hp) c = some (positiveTotal c hv hp) := (Option.some_get _).symm
  cases he : positiveFuel c hv hp with
  | zero => simp [he, positiveBracket, hn] at hs
  | succ n =>
    rw [he] at hs
    simp only [positiveBracket, hn, ↓reduceIte] at hs
    exact positiveBracket_eq_total (refine_valid hv) (refine_positive_comparison hv hp) n hs

/-- No `positiveFuel` computation occurs at runtime: the measure is erased. -/
def positiveTask (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) : FinTask AlgCode :=
  .step fun _ => if hl : 0 < c.interval.lower then .done c else
    .step fun _ => positiveTask c.refine (refine_valid hv) (refine_positive_comparison hv hp)
termination_by positiveFuel c hv hp
decreasing_by exact positiveFuel_refine_lt hv hp hl

 theorem positiveTask_result (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) :
    (positiveTask c hv hp).result = positiveTotal c hv hp := by
  rw [positiveTask, FinTask.result_step]
  split_ifs with hl
  · exact (positiveTotal_eq_self hv hp hl).symm
  · rw [FinTask.result_step, positiveTask_result]
    exact (positiveTotal_eq_refine hv hp hl).symm
termination_by positiveFuel c hv hp
decreasing_by exact positiveFuel_refine_lt hv hp hl

def prepareMarginTask (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) (s : ℕ) : FinTask AlgCode := do
  let d ← positiveTask c hv hp
  precisionTask d (marginMesh s)

 theorem prepareMarginTask_result (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    (prepareMarginTask c hv hp s).result = prepareMargin c hv hp s := by
  simp [prepareMarginTask, positiveTask_result, precisionTask_result, prepareMargin]

def validateMarginTask (c : AlgCode) (upper : ℚ) : FinTask Bool :=
  .step fun _ => if hv : c.valid then do
    let lo ← compareTask c hv 0
    let hi ← compareTask c hv upper
    .step fun _ => .done (decide (lo = .gt ∧ hi ≠ .gt))
  else .done false

 theorem validateMarginTask_result (c : AlgCode) (upper : ℚ) :
    (validateMarginTask c upper).result = validateMargin c upper := by
  simp only [validateMarginTask, FinTask.result_step, validateMargin]
  split_ifs <;> simp [compareTask_result]

def validateMarginsTask (r : ℕ) (w sigma : AlgCode) : FinTask Bool := do
  let hw ← validateMarginTask w (1/(r : ℚ))
  if hw then validateMarginTask sigma 1 else .done false

 theorem validateMarginsTask_result (r : ℕ) (w sigma : AlgCode) :
    (validateMarginsTask r w sigma).result = validateMargins r w sigma := by
  simp only [validateMarginsTask, FinTask.result_bindM, validateMarginTask_result, validateMargins]
  split <;> simp_all [validateMarginTask_result]

 theorem validateMarginTask_zero_unknown (c : AlgCode) (upper : ℚ) :
    FinTask.run 0 (validateMarginTask c upper) = none := rfl

 theorem prepareMarginTask_verified {c : AlgCode} (hv : c.valid) (hp : compareTotal c hv 0 = .gt)
    (s fuel : ℕ) (d : AlgCode) (hr : FinTask.run fuel (prepareMarginTask c hv hp s) = some d) :
    verifyRefinement c d (marginMesh s) true = true := by
  have hd := FinTask.run_sound fuel (prepareMarginTask c hv hp s) d hr
  rw [prepareMarginTask_result] at hd
  rw [← hd]
  exact prepareMargin_verified hv hp s

end Cover.AlgCode
