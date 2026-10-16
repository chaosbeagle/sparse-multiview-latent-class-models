import Cover.AlgebraicStepped
import Cover.ScalarCoefficients
import Cover.FiniteTasks

namespace Cover
namespace DyadicSqrt

/-- The floor, signed-to-natural conversion, and verified total natural integer-square-root
are separate finite arithmetic primitives. They are never evaluated before a fuel step. -/
def floorSqrtTask (q : ℚ) : FinTask ℕ := do
  let z ← FinTask.step fun _ => .done (Int.floor q)
  let n ← FinTask.step fun _ => .done z.toNat
  .step fun _ => .done (Nat.sqrt n)

@[simp] theorem floorSqrtTask_result (q : ℚ) : (floorSqrtTask q).result = floorSqrt q := by
  simp [floorSqrtTask,floorSqrt]

def lowerTask (s : ℕ) (q : ℚ) : FinTask ℚ := .step fun _ => do
  let d ← AlgCode.rationalPowTask 2 (s+2)
  let dsq ← FinTask.step fun _ => .done (d*d)
  let scaled ← FinTask.step fun _ => .done (q*dsq)
  let root ← floorSqrtTask scaled
  let rootQ ← FinTask.step fun _ => .done (root : ℚ)
  .step fun _ => .done (rootQ/d)

@[simp] theorem lowerTask_result (s : ℕ) (q : ℚ) : (lowerTask s q).result = lower s q := by
  simp [lowerTask,AlgCode.rationalPowTask_result,lower,scale,pow_two]

def upperTask (s : ℕ) (q : ℚ) : FinTask ℚ := do
  let l ← lowerTask s q
  let lsq ← FinTask.step fun _ => .done (l*l)
  .step fun _ => if lsq=q then .done l else do
    let h ← AlgCode.marginMeshTask s
    .step fun _ => .done (l+h)

@[simp] theorem upperTask_result (s : ℕ) (q : ℚ) : (upperTask s q).result = upper s q := by
  simp only [upperTask,FinTask.result_bindM,lowerTask_result,FinTask.result_step,
    FinTask.result_done,upper,pow_two]
  split_ifs <;> simp_all [AlgCode.marginMeshTask_result,AlgCode.marginMesh,mesh,scale,one_div]

/-- Literal outward dyadic sqrt with all endpoint computation inside the stepped task. -/
def boundsTask (s : ℕ) (I : QInterval) : FinTask QInterval := do
  let l ← lowerTask s I.lower
  let u ← upperTask s I.upper
  .step fun _ => .done ⟨l,u⟩

@[simp] theorem boundsTask_result (s : ℕ) (I : QInterval) :
    (boundsTask s I).result = bounds s I := by
  simp [boundsTask,bounds]

end DyadicSqrt

namespace ScalarExpr

def intervalAddTask (I J : QInterval) : FinTask QInterval := do
  let l ← FinTask.step fun _ => .done (I.lower+J.lower)
  let u ← FinTask.step fun _ => .done (I.upper+J.upper)
  .done ⟨l,u⟩
@[simp] theorem intervalAddTask_result (I J : QInterval) : (intervalAddTask I J).result = I.add J := by
  simp [intervalAddTask,QInterval.add]

def intervalInvTask (I : QInterval) : FinTask QInterval := do
  let l ← FinTask.step fun _ => .done I.upper⁻¹
  let u ← FinTask.step fun _ => .done I.lower⁻¹
  .done ⟨l,u⟩
@[simp] theorem intervalInvTask_result (I : QInterval) : (intervalInvTask I).result = I.invPos := by
  simp [intervalInvTask,QInterval.invPos]

def intervalMinTask (I J : QInterval) : FinTask QInterval := do
  let l ← FinTask.step fun _ => .done (Min.min I.lower J.lower)
  let u ← FinTask.step fun _ => .done (Min.min I.upper J.upper)
  .done ⟨l,u⟩
@[simp] theorem intervalMinTask_result (I J : QInterval) : (intervalMinTask I J).result = I.min J := by
  simp [intervalMinTask,QInterval.min]

def intervalMaxTask (I J : QInterval) : FinTask QInterval := do
  let l ← FinTask.step fun _ => .done (Max.max I.lower J.lower)
  let u ← FinTask.step fun _ => .done (Max.max I.upper J.upper)
  .done ⟨l,u⟩
@[simp] theorem intervalMaxTask_result (I J : QInterval) : (intervalMaxTask I J).result = I.max J := by
  simp [intervalMaxTask,QInterval.max]

/-- Each recursive scalar node, legality check, rational endpoint operation and dyadic
sqrt primitive is exposed through FinTask. Failure short-circuits exactly like bounds. -/
def boundsTask (s : ℕ) (w σ : QInterval) : ScalarExpr → FinTask (Option QInterval)
  | .rat q => .step fun _ => .done (some (.singleton q))
  | .weight => .step fun _ => .done (some w)
  | .sigma => .step fun _ => .done (some σ)
  | .add p q => .step fun _ => do
      let a ← boundsTask s w σ p
      match a with
      | none => .done none
      | some A => do
          let b ← boundsTask s w σ q
          match b with
          | none => .done none
          | some B => do
              let I ← intervalAddTask A B
              .done (some I)
  | .mul p q => .step fun _ => do
      let a ← boundsTask s w σ p
      match a with
      | none => .done none
      | some A => do
          let b ← boundsTask s w σ q
          match b with
          | none => .done none
          | some B => do
              let I ← IntPolynomial.intervalMulTask A B
              .done (some I)
  | .inv p => .step fun _ => do
      let a ← boundsTask s w σ p
      match a with
      | none => .done none
      | some A => .step fun _ => if 0<A.lower then do
          let I ← intervalInvTask A
          .done (some I)
        else .done none
  | .sqrt p => .step fun _ => do
      let a ← boundsTask s w σ p
      match a with
      | none => .done none
      | some A => .step fun _ => if 0≤A.lower then do
          let I ← DyadicSqrt.boundsTask s A
          .done (some I)
        else .done none
  | .min p q => .step fun _ => do
      let a ← boundsTask s w σ p
      match a with
      | none => .done none
      | some A => do
          let b ← boundsTask s w σ q
          match b with
          | none => .done none
          | some B => do
              let I ← intervalMinTask A B
              .done (some I)
  | .max p q => .step fun _ => do
      let a ← boundsTask s w σ p
      match a with
      | none => .done none
      | some A => do
          let b ← boundsTask s w σ q
          match b with
          | none => .done none
          | some B => do
              let I ← intervalMaxTask A B
              .done (some I)

theorem boundsTask_result (s : ℕ) (w σ : QInterval) (p : ScalarExpr) :
    (boundsTask s w σ p).result = p.bounds s w σ := by
  induction p with
  | rat q => rfl
  | weight => rfl
  | sigma => rfl
  | add p q hp hq | mul p q hp hq | min p q hp hq | max p q hp hq =>
      simp only [boundsTask,FinTask.result_step,FinTask.result_bindM,hp]
      cases ha : p.bounds s w σ <;> cases hb : q.bounds s w σ <;>
        simp [ha,hb,hq,bounds,IntPolynomial.intervalMulTask_result]
  | inv p hp | sqrt p hp =>
      simp only [boundsTask,FinTask.result_step,FinTask.result_bindM,hp]
      cases ha : p.bounds s w σ with
      | none => simp [bounds,ha]
      | some A =>
          dsimp only
          simp only [FinTask.result_step]
          split_ifs <;> simp_all [bounds]

theorem boundsTask_run_correct (s : ℕ) (w σ : QInterval) (p : ScalarExpr)
    (fuel : ℕ) (answer : Option QInterval)
    (hr : FinTask.run fuel (boundsTask s w σ p) = some answer) : p.bounds s w σ = answer := by
  have hs := FinTask.run_sound fuel _ answer hr
  rwa [boundsTask_result] at hs

theorem boundsTask_zero_unknown (s : ℕ) (w σ : QInterval) (p : ScalarExpr) :
    FinTask.run 0 (boundsTask s w σ p) = none := by
  cases p <;> rfl

end ScalarExpr

namespace ScalarExpr

/-- Scalar syntax powers are constructed one multiplication node per step. -/
def powTask (p : ScalarExpr) : ℕ → FinTask ScalarExpr
  | 0 => .step fun _ => .done (.rat 1)
  | n+1 => .step fun _ => do
      let q ← powTask p n
      FinTask.primitive (fun _ => .mul q p)
@[simp] theorem powTask_result (p : ScalarExpr) (n : ℕ) : (powTask p n).result = p.pow n := by
  induction n <;> simp_all [powTask,pow]

def sumTask : List ScalarExpr → FinTask ScalarExpr
  | [] => .step fun _ => .done (.rat 0)
  | p::ps => .step fun _ => do
      let q ← sumTask ps
      FinTask.primitive (fun _ => .add p q)
@[simp] theorem sumTask_result (ps : List ScalarExpr) : (sumTask ps).result = sum ps := by
  induction ps <;> simp_all [sumTask,sum]

def maxListTask : List ScalarExpr → FinTask ScalarExpr
  | [] => .step fun _ => .done (.rat 0)
  | [p] => .step fun _ => .done p
  | p::q::ps => .step fun _ => do
      let m ← maxListTask (q::ps)
      FinTask.primitive (fun _ => .max p m)
@[simp] theorem maxListTask_result (ps : List ScalarExpr) : (maxListTask ps).result = maxList ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases ps with
    | nil => rfl
    | cons q ps => simp only [maxListTask,FinTask.result_step,FinTask.result_bindM,ih,
        FinTask.primitive_result,maxList]

end ScalarExpr

namespace FinTask

def natSumTask : List ℕ → FinTask ℕ
  | [] => .step fun _ => .done 0
  | n::ns => .step fun _ => do
      let k ← natSumTask ns
      primitive (fun _ => n+k)
@[simp] theorem natSumTask_result (ns : List ℕ) : (natSumTask ns).result = ns.sum := by
  induction ns <;> simp_all [natSumTask]

def natProductTask : List ℕ → FinTask ℕ
  | [] => .step fun _ => .done 1
  | n::ns => .step fun _ => do
      let k ← natProductTask ns
      primitive (fun _ => n*k)
@[simp] theorem natProductTask_result (ns : List ℕ) : (natProductTask ns).result = ns.prod := by
  induction ns <;> simp_all [natProductTask]

end FinTask

namespace Literal

/-- Construct every node of the literal a_g syntax within resumable steps. -/
def aTask (n : Fin g → ℕ) (i : Fin g) : FinTask ScalarExpr := .step fun _ => do
  let size ← FinTask.primitive (fun _ => (n i : ℚ))
  let sizeExpr ← FinTask.primitive (fun _ => ScalarExpr.rat size)
  let root ← FinTask.primitive (fun _ => ScalarExpr.sqrt sizeExpr)
  let one ← FinTask.primitive (fun _ => ScalarExpr.rat 1)
  let numerator ← FinTask.primitive (fun _ => ScalarExpr.add one root)
  let sigma ← FinTask.primitive (fun _ => ScalarExpr.sigma)
  let sigmaSq ← ScalarExpr.powTask sigma 2
  let weight ← FinTask.primitive (fun _ => ScalarExpr.weight)
  let denominator ← FinTask.primitive (fun _ => ScalarExpr.mul weight sigmaSq)
  let inverse ← FinTask.primitive (fun _ => ScalarExpr.inv denominator)
  FinTask.primitive (fun _ => ScalarExpr.mul numerator inverse)
@[simp] theorem aTask_result (n : Fin g → ℕ) (i : Fin g) : (aTask n i).result = a n i := by
  simp [aTask,a]

def bTask (n : Fin g → ℕ) (e : List (Fin g)) : FinTask ScalarExpr := .step fun _ => do
  let sigma ← FinTask.primitive (fun _ => ScalarExpr.sigma)
  let inverse ← FinTask.primitive (fun _ => ScalarExpr.inv sigma)
  let cube ← ScalarExpr.powTask inverse 3
  let terms ← FinTask.mapTask (aTask n) e
  let total ← ScalarExpr.sumTask terms
  let product ← FinTask.primitive (fun _ => ScalarExpr.mul inverse total)
  FinTask.primitive (fun _ => ScalarExpr.add cube product)
@[simp] theorem bTask_result (n : Fin g → ℕ) (e : List (Fin g)) : (bTask n e).result = b n e := by
  simp [bTask,b]

def edgeBTask (n : Fin g → ℕ) (e : List (Fin g)) : FinTask ScalarExpr := .step fun _ => do
  let bExpr ← bTask n e
  let bSq ← ScalarExpr.powTask bExpr 2
  let squares ← FinTask.mapTask (fun i => do
    let aExpr ← aTask n i
    ScalarExpr.powTask aExpr 2) e
  let total ← ScalarExpr.sumTask squares
  let radicand ← FinTask.primitive (fun _ => ScalarExpr.add bSq total)
  FinTask.primitive (fun _ => ScalarExpr.sqrt radicand)
@[simp] theorem edgeBTask_result (n : Fin g → ℕ) (e : List (Fin g)) : (edgeBTask n e).result = edgeB n e := by
  simp [edgeBTask,edgeB]

def BTask (n : Fin g → ℕ) (edges : List (List (Fin g))) : FinTask ScalarExpr := .step fun _ => do
  let terms ← FinTask.mapTask (edgeBTask n) edges
  ScalarExpr.maxListTask terms
@[simp] theorem BTask_result (n : Fin g → ℕ) (edges : List (List (Fin g))) :
    (BTask n edges).result = B n edges := by
  simp [BTask,B]

def kappaTask (n : Fin g → ℕ) (edges : List (List (Fin g))) : FinTask ScalarExpr := .step fun _ => do
  let b ← BTask n edges
  FinTask.primitive (fun _ => ScalarExpr.inv b)
@[simp] theorem kappaTask_result (n : Fin g → ℕ) (edges : List (List (Fin g))) :
    (kappaTask n edges).result = kappa n edges := by
  simp [kappaTask,kappa]

/-- Cell counts are computed by stepped per-edge products followed by a stepped sum. -/
def mTask (n : Fin g → ℕ) (edges : List (List (Fin g))) : FinTask ℕ := .step fun _ => do
  let counts ← FinTask.mapTask (fun e => do
    let sizes ← FinTask.mapTask (fun i => FinTask.primitive (fun _ => n i)) e
    FinTask.natProductTask sizes) edges
  FinTask.natSumTask counts
@[simp] theorem mTask_result (n : Fin g → ℕ) (edges : List (List (Fin g))) :
    (mTask n edges).result = m n edges := by
  simp [mTask,m]

def MTask (n : Fin g → ℕ) (edges : List (List (Fin g))) : FinTask ScalarExpr := .step fun _ => do
  let count ← mTask n edges
  let q ← FinTask.primitive (fun _ => (count : ℚ))
  let constant ← FinTask.primitive (fun _ => ScalarExpr.rat q)
  let root ← FinTask.primitive (fun _ => ScalarExpr.sqrt constant)
  let twelve ← FinTask.primitive (fun _ => ScalarExpr.rat 12)
  FinTask.primitive (fun _ => ScalarExpr.mul twelve root)
@[simp] theorem MTask_result (n : Fin g → ℕ) (edges : List (List (Fin g))) :
    (MTask n edges).result = M n edges := by
  simp [MTask,M]

def RTask (n : Fin g → ℕ) (edges : List (List (Fin g))) : FinTask ScalarExpr := .step fun _ => do
  let kappa ← kappaTask n edges
  let curvature ← MTask n edges
  let inverse ← FinTask.primitive (fun _ => ScalarExpr.inv curvature)
  let ratio ← FinTask.primitive (fun _ => ScalarExpr.mul kappa inverse)
  let one ← FinTask.primitive (fun _ => ScalarExpr.rat 1)
  FinTask.primitive (fun _ => ScalarExpr.min one ratio)
@[simp] theorem RTask_result (n : Fin g → ℕ) (edges : List (List (Fin g))) :
    (RTask n edges).result = R n edges := by
  simp [RTask,R]

/-- The three fully constructed expressions are cached and then consumed by the evaluator. -/
def coefficientSyntaxTask (n : Fin g → ℕ) (edges : List (List (Fin g))) : FinTask (Fin 3 → ScalarExpr) :=
  .step fun _ => do
    let weight ← FinTask.primitive (fun _ => ScalarExpr.weight)
    let sigma ← FinTask.primitive (fun _ => ScalarExpr.sigma)
    let sigmaSq ← ScalarExpr.powTask sigma 2
    let radius ← RTask n edges
    let radiusSq ← ScalarExpr.powTask radius 2
    FinTask.primitive (fun _ => ![weight,sigmaSq,radiusSq])
@[simp] theorem coefficientSyntaxTask_result (n : Fin g → ℕ) (edges : List (List (Fin g))) :
    (coefficientSyntaxTask n edges).result = coefficientSyntax n edges := by
  simp [coefficientSyntaxTask,coefficientSyntax]

/-- Construct and execute exactly the three literal scalar leaves used by the compiler.
Formula construction and interval evaluation both have internal checkpoints. -/
def coefficientBoundsTask (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (s : ℕ) (w σ : QInterval) : FinTask (Fin 3 → QInterval) := .step fun _ => do
  let expressions ← coefficientSyntaxTask n edges
  let wI ← ScalarExpr.boundsTask s w σ (expressions 0)
  let σI ← ScalarExpr.boundsTask s w σ (expressions 1)
  let RI ← ScalarExpr.boundsTask s w σ (expressions 2)
  .step fun _ => .done ![wI.getD (.singleton 0),σI.getD (.singleton 0),RI.getD (.singleton 0)]

theorem coefficientBoundsTask_result (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (s : ℕ) (w σ : QInterval) :
    (coefficientBoundsTask n edges s w σ).result = coefficientBounds n edges s w σ := by
  simp only [coefficientBoundsTask,FinTask.result_step,FinTask.result_bindM,
    coefficientSyntaxTask_result,ScalarExpr.boundsTask_result,FinTask.result_done]
  funext i
  fin_cases i <;> rfl

end Literal

namespace AlgCode

theorem prepareMargin_interval_eq_preparedBracket (c : AlgCode) (hv : c.valid)
    (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    (prepareMargin c hv hp s).interval = preparedBracket c hv hp s := by
  simp only [prepareMargin,preparedBracket,marginMesh,DyadicSqrt.mesh,DyadicSqrt.scale,one_div]

end AlgCode

/-- All margin preparation and scalar evaluation is inside finite fuel steps. The
validation proof is erased; it introduces no executed denoted real or selected output. -/
def validatedScalarCoefficientsTask (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ) (s : ℕ) : FinTask (Fin 3 → QInterval) :=
  .step fun _ => do
    let wp ← AlgCode.prepareMarginSteppedTask w (Margins.valid_codes h).1 (Margins.valid_positive_comparisons h).1 s
    let σp ← AlgCode.prepareMarginSteppedTask σ (Margins.valid_codes h).2 (Margins.valid_positive_comparisons h).2 s
    Literal.coefficientBoundsTask n edges s wp.interval σp.interval

theorem validatedScalarCoefficientsTask_result (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ) (s : ℕ) :
    (validatedScalarCoefficientsTask n edges r w σ h s).result =
      validatedScalarCoefficients n edges r w σ h s := by
  simp only [validatedScalarCoefficientsTask,FinTask.result_step,FinTask.result_bindM,
    AlgCode.prepareMarginSteppedTask_result,Literal.coefficientBoundsTask_result,
    AlgCode.prepareMargin_interval_eq_preparedBracket,validatedScalarCoefficients,scalarCoefficients]

theorem validatedScalarCoefficientsTask_zero_unknown (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ) (s : ℕ) :
    FinTask.run 0 (validatedScalarCoefficientsTask n edges r w σ h s) = none := rfl

theorem validatedScalarCoefficientsTask_run_sound (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ) (s fuel : ℕ)
    (cs : Fin 3 → QInterval)
    (hr : FinTask.run fuel (validatedScalarCoefficientsTask n edges r w σ h s) = some cs) :
    cs = validatedScalarCoefficients n edges r w σ h s := by
  have hs := FinTask.run_sound fuel _ cs hr
  rw [validatedScalarCoefficientsTask_result] at hs
  exact hs.symm

/-- Finite-task completeness: the bound is a proof of finite discrete execution,
not an oracle evaluated by the capped driver before it checks its fuel. -/
theorem validatedScalarCoefficientsTask_has_fuel (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ) (s : ℕ) :
    ∃ fuel : ℕ, FinTask.run fuel (validatedScalarCoefficientsTask n edges r w σ h s) =
      some (validatedScalarCoefficients n edges r w σ h s) := by
  let p := validatedScalarCoefficientsTask n edges r w σ h s
  refine ⟨p.steps,?_⟩
  simpa only [p,validatedScalarCoefficientsTask_result] using FinTask.run_sufficient p p.steps (le_refl _)

end Cover
