import Cover.A06Certificate
import Cover.ByteTasks
import Cover.AlgebraicStepped

namespace Cover.Capped

inductive Outcome (α : Type) where
  | certificate : α → Outcome α
  | unknownResource
  | invalidInput
  | implementationError

inductive Action (α : Type) where
  | again : Nat → Action α
  | stop : Outcome α → Action α

/-- The same explicit lazy transition interpreter is used before and after input
    validation. Exhausted fuel has only UNKNOWN_RESOURCE semantics. -/
def execute (next : Nat → FinTask (Action α)) : Nat → FinTask (Action α) → Outcome α
  | 0, _ => .unknownResource
  | fuel+1, .step k => execute next fuel (k ())
  | fuel+1, .done (.again s) => execute next fuel (next s)
  | _+1, .done (.stop out) => out

theorem fuel_prefix (next : Nat → FinTask (Action α)) (f g : Nat) (hfg : f≤g)
    (job : FinTask (Action α)) (h : execute next f job ≠ .unknownResource) :
    execute next g job = execute next f job := by
  induction f generalizing g job with
  | zero => exact False.elim (h rfl)
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      cases job with
      | step k => exact ih g (by omega) (k ()) h
      | done action => cases action with
        | stop out => rfl
        | again s => exact ih g (by omega) (next s) h

def Checked (P : α → Prop) : Outcome α → Prop
  | .certificate value => P value
  | _ => True

def ActionChecked (P : α → Prop) : Action α → Prop
  | .stop out => Checked P out
  | .again _ => True

theorem checked (next : Nat → FinTask (Action α)) (P : α → Prop)
    (hn : ∀ s, ActionChecked P (next s).result) (fuel : Nat) (job : FinTask (Action α))
    (hj : ActionChecked P job.result) : Checked P (execute next fuel job) := by
  induction fuel generalizing job with
  | zero => trivial
  | succ fuel ih =>
    cases job with
    | step k => exact ih (k ()) hj
    | done action => cases action with
      | stop out => exact hj
      | again s => exact ih (next s) (hn s)

theorem finish_task (next : Nat → FinTask (Action α)) (job : FinTask (Action α)) (fuel : Nat) :
    execute next (job.steps+fuel+1) job = match job.result with
      | .stop out => out
      | .again s => execute next fuel (next s) := by
  induction job with
  | done action => cases action <;> simp [FinTask.steps, execute]
  | step k ih =>
    have heq : (FinTask.step k).steps+fuel+1 = ((k ()).steps+fuel+1)+1 := by
      simp [FinTask.steps]; omega
    rw [heq]
    exact ih ()

theorem eventual (next : Nat → FinTask (Action α))
    (hshape : ∀ s, (next s).result = .again (s+1) ∨ ∃ value, (next s).result = .stop (.certificate value))
    (distance start : Nat) (value : α) (hs : (next (start+distance)).result = .stop (.certificate value)) :
    ∃ fuel result, execute next fuel (next start) = .certificate result := by
  induction distance generalizing start value with
  | zero =>
    simp only [Nat.add_zero] at hs
    refine ⟨(next start).steps+0+1, value, ?_⟩
    rw [finish_task next (next start) 0, hs]
  | succ distance ih =>
    rcases hshape start with hcontinue | ⟨found,hfound⟩
    · have heq : start+1+distance = start+(distance+1) := by omega
      obtain ⟨fuel,result,hr⟩ := ih (start+1) value (by rw [heq]; exact hs)
      refine ⟨(next start).steps+fuel+1,result,?_⟩
      rw [finish_task, hcontinue]
      exact hr
    · refine ⟨(next start).steps+0+1,found,?_⟩
      rw [finish_task next (next start) 0, hfound]

theorem avoids (next : Nat → FinTask (Action α)) (bad : Outcome α)
    (hb : bad ≠ .unknownResource) (hn : ∀ s, (next s).result ≠ .stop bad)
    (fuel : Nat) (job : FinTask (Action α)) (hj : job.result ≠ .stop bad) :
    execute next fuel job ≠ bad := by
  induction fuel generalizing job with
  | zero => exact Ne.symm hb
  | succ fuel ih =>
    cases job with
    | step k => exact ih (k ()) hj
    | done action => cases action with
      | again s => exact ih (next s) (hn s)
      | stop out => exact fun h => hj (congrArg Action.stop h)
end Cover.Capped

namespace Cover.A06

/-- Finite returned data. The proof of admitted input comes from completed finite
    validation and is erased; acceptance is independently proved below. -/
structure Returned where
  input : Input
  valid : Valid input
  certificate : Certificate input valid
  bytes : ByteArray

abbrev CappedResult := Capped.Outcome Returned
abbrev CappedAction := Capped.Action Returned

def Returned.Checked (r : Returned) : Prop :=
  Bytes.parseEvidenceByteArray (pairDimension r.input r.valid) (constraintCount r.input r.valid) r.bytes =
      some r.certificate ∧ verifyCertificate r.input r.valid r.certificate = true

/-- Admitted scalar codes are prepared by the actual interruptible bisection loops. -/
def preparedMarginsTask (I : Input) (h : Valid I) (s : Nat) : FinTask (AlgCode × AlgCode) := do
  let w ← AlgCode.prepareMarginSteppedTask I.weight (Margins.valid_codes h.2).1
    (Margins.valid_positive_comparisons h.2).1 s
  let sigma ← AlgCode.prepareMarginSteppedTask I.sigma (Margins.valid_codes h.2).2
    (Margins.valid_positive_comparisons h.2).2 s
  .done (w,sigma)

theorem preparedMarginsTask_result (I : Input) (h : Valid I) (s : Nat) :
    (preparedMarginsTask I h s).result = (preparedWeight I h s, preparedSigma I h s) := by
  simp [preparedMarginsTask, AlgCode.prepareMarginSteppedTask_result, preparedWeight, preparedSigma]

end Cover.A06
