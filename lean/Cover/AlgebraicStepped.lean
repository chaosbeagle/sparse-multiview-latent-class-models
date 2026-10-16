import Cover.AlgebraicPrimitiveTasks

namespace Cover.AlgCode

/-- Fully stepped comparison, including each coefficient operation in every Horner evaluation. -/
def compareSteppedTask (c : AlgCode) (hv : c.valid) (t : ℚ) : FinTask Ordering := do
  let r ← compareCertifiedTask c t
  match hr : r.val with
  | some o => .done o
  | none => do
    let d ← refineCertifiedTask c
    compareSteppedTask d.val (d.property.symm ▸ refine_valid hv) t
termination_by comparisonFuel c hv t
decreasing_by
  have hn : compareStep c t = none := r.property.symm.trans hr
  simpa only [d.property] using comparisonFuel_refine_lt hv t hn

 theorem compareSteppedTask_result (c : AlgCode) (hv : c.valid) (t : ℚ) :
    (compareSteppedTask c hv t).result = compareTotal c hv t := by
  rw [compareSteppedTask, FinTask.result_bindM]
  split
  · rename_i o ho
    exact compareBracketRat_eq_total hv 0 ((compareCertifiedTask c t).result.property.symm.trans ho)
  · rename_i ho
    rw [FinTask.result_bindM, compareSteppedTask_result]
    simpa only [(refineCertifiedTask c).result.property] using compareTotal_refine_eq hv t
termination_by comparisonFuel c hv t
decreasing_by
  have ho : (compareCertifiedTask c t).result.val = none := by assumption
  have hn := (compareCertifiedTask c t).result.property.symm.trans ho
  simpa only [(refineCertifiedTask c).result.property] using comparisonFuel_refine_lt hv t hn

 def precisionFuelTask (c : AlgCode) (h : ℚ) : FinTask ℕ := do
  let w ← FinTask.step fun _ => .done (c.interval.upper - c.interval.lower)
  let q ← FinTask.step fun _ => .done (w/h)
  let n ← FinTask.step fun _ => .done (Nat.ceil q)
  .step fun _ => .done (n+1)

 theorem precisionFuelTask_result (c : AlgCode) (h : ℚ) :
    (precisionFuelTask c h).result = precisionFuel c h := by
  simp [precisionFuelTask, precisionFuel, QInterval.width]

 def refineToPrecisionSteppedTask (h : ℚ) : ℕ → AlgCode → FinTask (Option AlgCode)
  | 0, c => do
    let w ← FinTask.step fun _ => .done (c.interval.upper-c.interval.lower)
    .step fun _ => .done (if w≤h then some c else none)
  | n+1, c => do
    let w ← FinTask.step fun _ => .done (c.interval.upper-c.interval.lower)
    .step fun _ => if w≤h then .done (some c) else do
      let d ← refineStepTask c
      refineToPrecisionSteppedTask h n d

 theorem refineToPrecisionSteppedTask_result (h : ℚ) (n : ℕ) (c : AlgCode) :
    (refineToPrecisionSteppedTask h n c).result = refineToPrecision h n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [refineToPrecisionSteppedTask, FinTask.result_bindM, FinTask.result_step,
      FinTask.result_done, refineToPrecision, QInterval.width]
    split_ifs <;> simp_all [refineStepTask_result]

 def precisionSteppedTask (c : AlgCode) (h : ℚ) : FinTask AlgCode := do
  let fuel ← precisionFuelTask c h
  let d ← refineToPrecisionSteppedTask h fuel c
  .done (d.getD c)

 theorem precisionSteppedTask_result (c : AlgCode) (h : ℚ) :
    (precisionSteppedTask c h).result = refinePrecisely c h := by
  simp [precisionSteppedTask, precisionFuelTask_result, refineToPrecisionSteppedTask_result, refinePrecisely]

 def positiveSteppedTask (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) : FinTask AlgCode :=
  .step fun _ => if hl : 0 < c.interval.lower then .done c else do
    let d ← refineCertifiedTask c
    positiveSteppedTask d.val (d.property.symm ▸ refine_valid hv)
      (by simpa only [d.property] using refine_positive_comparison hv hp)
termination_by positiveFuel c hv hp
decreasing_by simpa only [d.property] using positiveFuel_refine_lt hv hp hl

 theorem positiveSteppedTask_result (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) :
    (positiveSteppedTask c hv hp).result = positiveTotal c hv hp := by
  rw [positiveSteppedTask, FinTask.result_step]
  split_ifs with hl
  · exact (positiveTotal_eq_self hv hp hl).symm
  · simp only [FinTask.result_bindM, refineCertifiedTask_result]
    rw [positiveSteppedTask_result]
    exact (positiveTotal_eq_refine hv hp hl).symm
termination_by positiveFuel c hv hp
decreasing_by exact positiveFuel_refine_lt hv hp hl

 def rationalPowTask (q : ℚ) : ℕ → FinTask ℚ
  | 0 => .done 1
  | n+1 => .step fun _ => do
    let v ← rationalPowTask q n
    .step fun _ => .done (v*q)

 theorem rationalPowTask_result (q : ℚ) (n : ℕ) : (rationalPowTask q n).result = q^n := by
  induction n <;> simp_all [rationalPowTask, pow_succ]

 def marginMeshTask (s : ℕ) : FinTask ℚ := .step fun _ => do
  let power ← rationalPowTask 2 (s+2)
  .step fun _ => .done (1/power)

 theorem marginMeshTask_result (s : ℕ) : (marginMeshTask s).result = marginMesh s := by
  simp [marginMeshTask, rationalPowTask_result, marginMesh]

 def prepareMarginSteppedTask (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    FinTask AlgCode := do
  let d ← positiveSteppedTask c hv hp
  let mesh ← marginMeshTask s
  precisionSteppedTask d mesh

 theorem prepareMarginSteppedTask_result (c : AlgCode) (hv : c.valid)
    (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    (prepareMarginSteppedTask c hv hp s).result = prepareMargin c hv hp s := by
  simp [prepareMarginSteppedTask, positiveSteppedTask_result, marginMeshTask_result,
    precisionSteppedTask_result, prepareMargin]

 def validateMarginSteppedTask (c : AlgCode) (upper : ℚ) : FinTask Bool := do
  let validated ← (validateAlgTask c).attach
  if hb : validated.val = true then
    have hv : c.valid := (validate_iff c).mp ((validated.property.trans (validateAlgTask_result c)).symm.trans hb)
    do
      let lo ← compareSteppedTask c hv 0
      let hi ← compareSteppedTask c hv upper
      .step fun _ => .done (decide (lo = .gt ∧ hi ≠ .gt))
  else .done false

 theorem validateMarginSteppedTask_result (c : AlgCode) (upper : ℚ) :
    (validateMarginSteppedTask c upper).result = validateMargin c upper := by
  simp only [validateMarginSteppedTask, FinTask.result_bindM, FinTask.attach_result, validateAlgTask_result]
  by_cases hv : c.valid <;> simp [validate, hv, compareSteppedTask_result, validateMargin]

 def validateMarginsSteppedTask (r : ℕ) (w sigma : AlgCode) : FinTask Bool := do
  let hw ← validateMarginSteppedTask w (1/(r : ℚ))
  if hw then validateMarginSteppedTask sigma 1 else .done false

 theorem validateMarginsSteppedTask_result (r : ℕ) (w sigma : AlgCode) :
    (validateMarginsSteppedTask r w sigma).result = validateMargins r w sigma := by
  simp only [validateMarginsSteppedTask, FinTask.result_bindM, validateMarginSteppedTask_result, validateMargins]
  split <;> simp_all [validateMarginSteppedTask_result]

 theorem validateMarginSteppedTask_zero_unknown (c : AlgCode) (upper : ℚ) :
    FinTask.run 0 (validateMarginSteppedTask c upper) = none := rfl

 theorem validateMarginSteppedTask_run_sound {c : AlgCode} {upper : ℚ} {fuel : ℕ} {accepted : Bool}
    (hr : FinTask.run fuel (validateMarginSteppedTask c upper) = some accepted) :
    (accepted = true ↔ validMargin c upper) := by
  have he := FinTask.run_sound fuel _ _ hr
  rw [validateMarginSteppedTask_result] at he
  rw [← he]
  exact validateMargin_iff c upper

 theorem prepareMarginSteppedTask_verified {c : AlgCode} (hv : c.valid) (hp : compareTotal c hv 0 = .gt)
    (s fuel : ℕ) (d : AlgCode) (hr : FinTask.run fuel (prepareMarginSteppedTask c hv hp s) = some d) :
    verifyRefinement c d (marginMesh s) true = true := by
  have hd := FinTask.run_sound fuel (prepareMarginSteppedTask c hv hp s) d hr
  rw [prepareMarginSteppedTask_result] at hd
  rw [← hd]
  exact prepareMargin_verified hv hp s

end Cover.AlgCode
