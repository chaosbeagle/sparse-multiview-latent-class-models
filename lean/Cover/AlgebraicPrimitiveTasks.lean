import Cover.AlgebraicTasks

namespace Cover.FinTask

/-- Attach the already proved denotation to a stepped result without recomputing it. -/
def attach (p : FinTask α) : FinTask {a : α // a = p.result} :=
  match p with
  | .done a => .done ⟨a, rfl⟩
  | .step next => .step fun _ => attach (next ())

@[simp] theorem attach_result (p : FinTask α) : (attach p).result = ⟨p.result, rfl⟩ := by
  apply Subtype.ext
  exact ((attach p).result).property

end Cover.FinTask
namespace Cover.IntPolynomial

 def hornerTask (p : Coeffs) (q : ℚ) : FinTask ℚ :=
  match p with
  | [] => .done 0
  | a::as => .step fun _ => do
    let v ← hornerTask as q
    let w ← FinTask.step fun _ => .done (q*v)
    .step fun _ => .done ((a : ℚ)+w)

 theorem hornerTask_result (p : Coeffs) (q : ℚ) : (hornerTask p q).result = horner p q := by
  induction p <;> simp_all [hornerTask, horner]

 def trimTask : Coeffs → FinTask Coeffs
  | [] => .done []
  | a::as => .step fun _ => do
    let ts ← trimTask as
    .step fun _ => .done (if ts=[] ∧ a=0 then [] else a::ts)

 theorem trimTask_result (p : Coeffs) : (trimTask p).result = trim p := by
  induction p <;> simp_all [trimTask, trim]

 def lengthTask : Coeffs → FinTask ℕ
  | [] => .done 0
  | _::as => .step fun _ => do
    let n ← lengthTask as
    .step fun _ => .done (n+1)

 theorem lengthTask_result (p : Coeffs) : (lengthTask p).result = p.length := by
  induction p <;> simp_all [lengthTask]

 def equalTask : Coeffs → Coeffs → FinTask Bool
  | [], [] => .done true
  | [], _::_ => .done false
  | _::_, [] => .done false
  | a::as, b::bs => .step fun _ => if a=b then equalTask as bs else .done false

 theorem equalTask_result (p q : Coeffs) : (equalTask p q).result = decide (p=q) := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a as ih =>
    cases q with
    | nil => rfl
    | cons b bs =>
      by_cases hab : a=b <;> simp [equalTask, hab, ih]

 def derivativeAuxTask (n : ℕ) : Coeffs → FinTask Coeffs
  | [] => .done []
  | a::as => do
    let v ← FinTask.step fun _ => .done ((n : ℤ)*a)
    let ts ← derivativeAuxTask (n+1) as
    .step fun _ => .done (v::ts)

 theorem derivativeAuxTask_result (n : ℕ) (p : Coeffs) :
    (derivativeAuxTask n p).result = derivativeAux n p := by
  induction p generalizing n <;> simp_all [derivativeAuxTask, derivativeAux]

 def derivativeTask (p : Coeffs) : FinTask Coeffs :=
  .step fun _ => match p with
  | [] => .done []
  | _::as => derivativeAuxTask 1 as

 theorem derivativeTask_result (p : Coeffs) : (derivativeTask p).result = derivative p := by
  cases p <;> simp [derivativeTask, derivative, derivativeAuxTask_result]

 def intervalMulTask (I J : QInterval) : FinTask QInterval := do
  let ll ← FinTask.step fun _ => .done (I.lower*J.lower)
  let lu ← FinTask.step fun _ => .done (I.lower*J.upper)
  let ul ← FinTask.step fun _ => .done (I.upper*J.lower)
  let uu ← FinTask.step fun _ => .done (I.upper*J.upper)
  let l₁ ← FinTask.step fun _ => .done (min ll lu)
  let l₂ ← FinTask.step fun _ => .done (min ul uu)
  let u₁ ← FinTask.step fun _ => .done (max ll lu)
  let u₂ ← FinTask.step fun _ => .done (max ul uu)
  let l ← FinTask.step fun _ => .done (min l₁ l₂)
  let u ← FinTask.step fun _ => .done (max u₁ u₂)
  .done ⟨l,u⟩

 theorem intervalMulTask_result (I J : QInterval) : (intervalMulTask I J).result = I.mul J := by
  simp [intervalMulTask, QInterval.mul]

 def intervalHornerTask (p : Coeffs) (I : QInterval) : FinTask QInterval :=
  match p with
  | [] => .done (.singleton 0)
  | a::as => .step fun _ => do
    let R ← intervalHornerTask as I
    let S ← intervalMulTask I R
    let l ← FinTask.step fun _ => .done ((a : ℚ)+S.lower)
    let u ← FinTask.step fun _ => .done ((a : ℚ)+S.upper)
    .done ⟨l,u⟩

 theorem intervalHornerTask_result (p : Coeffs) (I : QInterval) :
    (intervalHornerTask p I).result = intervalHorner p I := by
  induction p <;> simp_all [intervalHornerTask, intervalMulTask_result, intervalHorner,
    QInterval.add, QInterval.singleton]

end Cover.IntPolynomial
namespace Cover.AlgCode
open IntPolynomial

 def validateAlgTask (c : AlgCode) : FinTask Bool :=
  .step fun _ => match c with
  | .rat _ => .done true
  | .root p I => do
    let pt ← trimTask p
    let canon ← equalTask pt p
    let len ← lengthTask p
    let degree ← FinTask.step fun _ => .done (decide (2 ≤ len))
    let ordered ← FinTask.step fun _ => .done (decide (I.lower < I.upper))
    let l ← hornerTask p I.lower
    let u ← hornerTask p I.upper
    let prod ← FinTask.step fun _ => .done (l*u)
    let changes ← FinTask.step fun _ => .done (decide (prod < 0))
    let der ← derivativeTask p
    let J ← intervalHornerTask der I
    let neg ← FinTask.step fun _ => .done (decide (J.upper < 0))
    let pos ← FinTask.step fun _ => .done (decide (0 < J.lower))
    .done (canon && degree && ordered && changes && (neg || pos))

 theorem validateAlgTask_result (c : AlgCode) : (validateAlgTask c).result = c.validate := by
  cases c <;> simp [validateAlgTask, trimTask_result, equalTask_result, lengthTask_result,
    hornerTask_result, derivativeTask_result, intervalHornerTask_result, validate,
    valid, validRoot, canonical, Bool.and_assoc] <;> rfl

 def midpointTask (I : QInterval) : FinTask ℚ := do
  let v ← FinTask.step fun _ => .done (I.lower+I.upper)
  .step fun _ => .done (v/2)

 theorem midpointTask_result (I : QInterval) : (midpointTask I).result = I.midpoint := by
  simp [midpointTask, QInterval.midpoint]

 def compareStepTask (c : AlgCode) (t : ℚ) : FinTask (Option Ordering) :=
  .step fun _ => match c with
  | .rat q => .step fun _ => if q<t then .done (some .lt) else
      .step fun _ => .done (some (if q=t then .eq else .gt))
  | .root p I => .step fun _ => if t≤I.lower then .done (some .gt) else
      .step fun _ => if I.upper≤t then .done (some .lt) else do
        let v ← hornerTask p t
        .step fun _ => .done (if v=0 then some .eq else none)

 theorem compareStepTask_result (c : AlgCode) (t : ℚ) :
    (compareStepTask c t).result = compareStep c t := by
  cases c with
  | rat q => simp only [compareStepTask, FinTask.result_step, compareStep]; split_ifs <;> rfl
  | root p I =>
    simp only [compareStepTask, FinTask.result_step, compareStep]
    split_ifs <;> simp_all [hornerTask_result]

 def refineStepTask (c : AlgCode) : FinTask AlgCode :=
  .step fun _ => match c with
  | .rat q => .done (.rat q)
  | .root p I => do
    let m ← midpointTask I
    let pm ← hornerTask p m
    .step fun _ => if pm=0 then .done (.rat m) else do
      let pl ← hornerTask p I.lower
      let prod ← FinTask.step fun _ => .done (pl*pm)
      .step fun _ => .done (if prod<0 then .root p ⟨I.lower,m⟩ else .root p ⟨m,I.upper⟩)

 theorem refineStepTask_result (c : AlgCode) : (refineStepTask c).result = c.refine := by
  cases c with
  | rat q => rfl
  | root p I =>
    simp only [refineStepTask, FinTask.result_step, FinTask.result_bindM,
      midpointTask_result, hornerTask_result, refine]
    split_ifs <;> simp_all [hornerTask_result]

 def compareCertifiedTask (c : AlgCode) (t : ℚ) : FinTask {o : Option Ordering // o = compareStep c t} := do
  let o ← (compareStepTask c t).attach
  .done ⟨o.val, o.property.trans (compareStepTask_result c t)⟩

 @[simp] theorem compareCertifiedTask_result (c : AlgCode) (t : ℚ) :
    (compareCertifiedTask c t).result = ⟨compareStep c t,rfl⟩ := by
  apply Subtype.ext
  exact ((compareCertifiedTask c t).result).property

 def refineCertifiedTask (c : AlgCode) : FinTask {d : AlgCode // d = c.refine} := do
  let d ← (refineStepTask c).attach
  .done ⟨d.val, d.property.trans (refineStepTask_result c)⟩

 @[simp] theorem refineCertifiedTask_result (c : AlgCode) :
    (refineCertifiedTask c).result = ⟨c.refine,rfl⟩ := by
  apply Subtype.ext
  exact ((refineCertifiedTask c).result).property

end Cover.AlgCode
