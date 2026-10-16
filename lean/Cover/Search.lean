import Cover.TokenTasks

namespace Cover

inductive CappedOutcome (n j : Nat) where
  | certificate : CoverCertificate n j → List CoverToken → CappedOutcome n j
  | unknownResource
  | invalidInput
  | implementationError
  deriving DecidableEq, Repr

inductive SearchAction (n j : Nat) where
  | again : Nat → SearchAction n j
  | stop : CappedOutcome n j → SearchAction n j
  deriving DecidableEq, Repr

/-- Complete serialization, complete parse, exact identity comparison, and full
    interval replay are all completed before the positive status is constructed. -/
def packageTask (input : List Nat) (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (s : Nat) (t : CoverTree n j) : FinTask (CappedOutcome n j) :=
  let c := makeCertificate input s t
  serializeCertificateTask c >>= fun wire =>
  parseCertificateTask n j wire >>= fun parsed =>
    match parsed with
    | none => .done .implementationError
    | some parsed => .step (fun _ =>
        if parsed = c then
          checkTreeTask cs gs H s (unitBox n) parsed.tree >>= fun checked =>
            .step (fun _ => .done (if checked then .certificate parsed wire else .implementationError))
        else .done .implementationError)

theorem packageTask_result (input : List Nat) (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (s : Nat) (t : CoverTree n j)
    (hc : checkTree cs gs H s (unitBox n) t = true) :
    (packageTask input cs gs H s t).result =
      .certificate (makeCertificate input s t) (serializeCertificate (makeCertificate input s t)) := by
  simp [packageTask, serializeCertificateTask_result, parseCertificateTask_result,
    parseCertificate_serialize, checkTreeTask_result, makeCertificate, hc]

/-- Scalar preparation is itself a finite stepped program, so it can be interrupted.
    A concrete application supplies its literal validated scalar-refinement program. -/
def stageJob (input : List Nat) (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (s : Nat) : FinTask (SearchAction n j) := do
  let cs ← prepare s
  let outcome ← stageTask cs gs H hn s
  match outcome with
  | .inconclusive => .done (.again (s+1))
  | .implementationError => .done (.stop .implementationError)
  | .success t => do
    let packed ← packageTask input cs gs H s t
    .done (.stop packed)

theorem stageJob_result (input : List Nat) (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (s : Nat) :
    (stageJob input prepare gs H hn s).result =
      match coverStage (fun s => (prepare s).result) gs H hn s with
      | .inconclusive => .again (s+1)
      | .implementationError => .stop .implementationError
      | .success t => .stop (.certificate (makeCertificate input s t)
          (serializeCertificate (makeCertificate input s t))) := by
  simp only [stageJob, FinTask.result_bindM]
  rw [stageTask_result (fun s => (prepare s).result) gs H hn s]
  split
  · simp_all
  · simp_all
  · rename_i t ht
    have hc := coverStage_success_checked (fun s => (prepare s).result) gs H hn s t ht
    simp_all [packageTask_result input _ gs H s t hc]

/-- Validation can also be interrupted; only completed false returns INVALID_INPUT. -/
def initialJob (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) : FinTask (SearchAction n j) := do
  let valid ← validate
  if valid then stageJob input prepare gs H hn 0 else .done (.stop .invalidInput)

/-- One fuel unit is consumed per explicit task step or stage-control transition.
    Every fuel exhaustion, even during parsing, validation, or replay, is UNKNOWN. -/
def executeJobs (next : Nat → FinTask (SearchAction n j)) : Nat → FinTask (SearchAction n j) → CappedOutcome n j
  | 0, _ => .unknownResource
  | fuel+1, .step k => executeJobs next fuel (k ())
  | fuel+1, .done (.again s) => executeJobs next fuel (next s)
  | _+1, .done (.stop out) => out

def runCoverFuel (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (fuel : Nat) : CappedOutcome n j :=
  executeJobs (stageJob input prepare gs H hn) fuel (initialJob input validate prepare gs H hn)

theorem executeJobs_prefix (next : Nat → FinTask (SearchAction n j))
    (f g : Nat) (hfg : f ≤ g) (job : FinTask (SearchAction n j))
    (hout : executeJobs next f job ≠ .unknownResource) :
    executeJobs next g job = executeJobs next f job := by
  induction f generalizing g job with
  | zero => exact False.elim (hout rfl)
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      cases job with
      | step k => exact ih g (by omega) (k ()) hout
      | done action =>
        cases action with
        | stop out => rfl
        | again s => exact ih g (by omega) (next s) hout

theorem runCoverFuel_prefix (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (f g : Nat)
    (hfg : f ≤ g) (hout : runCoverFuel input validate prepare gs H hn f ≠ .unknownResource) :
    runCoverFuel input validate prepare gs H hn g = runCoverFuel input validate prepare gs H hn f :=
  executeJobs_prefix _ f g hfg _ hout

def OutcomeChecked (input : List Nat) (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) : CappedOutcome n j → Prop
  | .certificate c tokens => parseCertificate n j tokens = some c ∧ verifyCoverCertificate input cs gs H c = true
  | _ => True

def ActionChecked (input : List Nat) (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) : SearchAction n j → Prop
  | .stop out => OutcomeChecked input cs gs H out
  | .again _ => True

theorem stageJob_checked (input : List Nat) (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (s : Nat) :
    ActionChecked input (fun s => (prepare s).result) gs H (stageJob input prepare gs H hn s).result := by
  rw [stageJob_result]
  split
  · trivial
  · trivial
  · rename_i t ht
    have hc := coverStage_success_checked (fun s => (prepare s).result) gs H hn s t ht
    exact ⟨parseCertificate_serialize _, by simp [verifyCoverCertificate, makeCertificate, hc]⟩

theorem executeJobs_checked (input : List Nat) (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a)
    (next : Nat → FinTask (SearchAction n j))
    (hnext : ∀ s, ActionChecked input cs gs H (next s).result)
    (fuel : Nat) (job : FinTask (SearchAction n j))
    (hjob : ActionChecked input cs gs H job.result) :
    OutcomeChecked input cs gs H (executeJobs next fuel job) := by
  induction fuel generalizing job with
  | zero => trivial
  | succ fuel ih =>
    cases job with
    | step k => exact ih (k ()) hjob
    | done action => cases action with
      | stop out => exact hjob
      | again s => exact ih (next s) (hnext s)

theorem runCoverFuel_checked (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (fuel : Nat) :
    OutcomeChecked input (fun s => (prepare s).result) gs H
      (runCoverFuel input validate prepare gs H hn fuel) := by
  apply executeJobs_checked _ _ _ _ _ (stageJob_checked input prepare gs H hn)
  simp only [initialJob, FinTask.result_bindM]
  split
  · exact stageJob_checked input prepare gs H hn 0
  · trivial

theorem runCoverFuel_success_sound (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval)) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (fuel : Nat)
    (c : CoverCertificate n j) (tokens : List CoverToken)
    (hrun : runCoverFuel input validate prepare gs H hn fuel = .certificate c tokens)
    (hcs : ∀ s i, ((prepare s).result i).contains (values i))
    (x : Fin n → ℝ) (hx : (unitBox n).Contains x) (hf : ∀ i, 0 ≤ (gs i).eval values x) :
    parseCertificate n j tokens = some c ∧ c.input = input ∧
      0 < dyadic c.k ∧ (dyadic (2*c.k) : ℝ) ≤ H.eval values x := by
  have hc := runCoverFuel_checked input validate prepare gs H hn fuel
  rw [hrun] at hc
  exact ⟨hc.1, (verifyCoverCertificate_binding input _ gs H c hc.2).1,
    verifyCoverCertificate_sound input _ values gs H c hcs hc.2 x hx hf⟩

/-- Completing a finite job takes its finite task length plus the explicit
    stage-control transition. This lemma accounts for replay/serialization work too. -/
theorem executeJobs_finish_task (next : Nat → FinTask (SearchAction n j))
    (job : FinTask (SearchAction n j)) (fuel : Nat) :
    executeJobs next (job.steps + fuel + 1) job =
      match job.result with
      | .stop out => out
      | .again s => executeJobs next fuel (next s) := by
  induction job with
  | done action => cases action <;> simp [FinTask.steps, executeJobs]
  | step k ih =>
    have heq : (FinTask.step k).steps + fuel + 1 = ((k ()).steps + fuel + 1) + 1 := by
      simp [FinTask.steps]; omega
    rw [heq]
    exact ih ()


theorem stage_search_finite_success (input : List Nat) (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n)
    (distance start : Nat) (t : CoverTree n j)
    (hs : coverStage (fun s => (prepare s).result) gs H hn (start+distance) = .success t) :
    ∃ fuel c tokens, executeJobs (stageJob input prepare gs H hn) fuel
      (stageJob input prepare gs H hn start) = .certificate c tokens := by
  induction distance generalizing start t with
  | zero =>
    simp only [Nat.add_zero] at hs
    refine ⟨(stageJob input prepare gs H hn start).steps + 0 + 1,
      makeCertificate input start t, serializeCertificate (makeCertificate input start t), ?_⟩
    rw [executeJobs_finish_task (stageJob input prepare gs H hn) (stageJob input prepare gs H hn start) 0, stageJob_result, hs]
  | succ distance ih =>
    cases hc : coverStage (fun s => (prepare s).result) gs H hn start with
    | implementationError => exact False.elim (coverStage_no_implementationError _ _ _ _ _ hc)
    | success tree =>
      refine ⟨(stageJob input prepare gs H hn start).steps + 0 + 1,
        makeCertificate input start tree, serializeCertificate (makeCertificate input start tree), ?_⟩
      rw [executeJobs_finish_task (stageJob input prepare gs H hn) (stageJob input prepare gs H hn start) 0, stageJob_result, hc]
    | inconclusive =>
      have hs' : coverStage (fun s => (prepare s).result) gs H hn ((start+1)+distance) = .success t := by
        have heq : (start+1)+distance = start+(distance+1) := by omega
        rw [heq]
        exact hs
      obtain ⟨fuel, c, tokens, hr⟩ := ih (start+1) t hs'
      refine ⟨(stageJob input prepare gs H hn start).steps + fuel + 1, c, tokens, ?_⟩
      rw [executeJobs_finish_task, stageJob_result, hc]
      exact hr

/-- Existence of fuel is derived from an actual successful stage, never used to
    select the returned certificate. The program above remains ordinary execution. -/
theorem runCoverFuel_eventual_of_stage (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n)
    (hv : validate.result = true) (s : Nat) (t : CoverTree n j)
    (hs : coverStage (fun s => (prepare s).result) gs H hn s = .success t) :
    ∃ fuel c tokens, runCoverFuel input validate prepare gs H hn fuel = .certificate c tokens := by
  have hs' : coverStage (fun s => (prepare s).result) gs H hn (0+s) = .success t := by simpa using hs
  obtain ⟨fuel, c, tokens, hr⟩ := stage_search_finite_success input prepare gs H hn s 0 t hs'
  let next := stageJob input prepare gs H hn
  let first := initialJob input validate prepare gs H hn
  have hsame : first.result = (next 0).result := by simp [first, next, initialJob, hv]
  have hstable : executeJobs next ((next 0).steps + fuel + 1) (next 0) = .certificate c tokens := by
    have hp := executeJobs_prefix next fuel ((next 0).steps + fuel + 1) (by omega) (next 0)
      (by rw [hr]; simp)
    exact hp.trans hr
  refine ⟨first.steps + fuel + 1, c, tokens, ?_⟩
  change executeJobs next (first.steps + fuel + 1) first = _
  rw [executeJobs_finish_task, hsame]
  rw [executeJobs_finish_task] at hstable
  exact hstable

theorem runCoverFuel_eventual_of_stages (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n)
    (hv : validate.result = true)
    (hs : ∃ s0, ∀ s ≥ s0, ∃ t, coverStage (fun s => (prepare s).result) gs H hn s = .success t) :
    ∃ fuel c tokens, runCoverFuel input validate prepare gs H hn fuel = .certificate c tokens := by
  obtain ⟨s0, hs⟩ := hs
  obtain ⟨t, ht⟩ := hs s0 (le_refl _)
  exact runCoverFuel_eventual_of_stage input validate prepare gs H hn hv s0 t ht

end Cover

namespace Cover

theorem executeJobs_stop_only (next : Nat → FinTask (SearchAction n j))
    (fuel : Nat) (job : FinTask (SearchAction n j)) (out : CappedOutcome n j)
    (h : job.result = .stop out) :
    executeJobs next fuel job = .unknownResource ∨ executeJobs next fuel job = out := by
  induction fuel generalizing job with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
    cases job with
    | step k => exact ih (k ()) h
    | done action =>
      have ha : action = .stop out := h
      subst action
      exact Or.inr rfl

theorem executeJobs_avoids (next : Nat → FinTask (SearchAction n j))
    (bad : CappedOutcome n j) (hb : bad ≠ .unknownResource)
    (hnext : ∀ s, (next s).result ≠ .stop bad)
    (fuel : Nat) (job : FinTask (SearchAction n j))
    (hjob : job.result ≠ .stop bad) : executeJobs next fuel job ≠ bad := by
  induction fuel generalizing job with
  | zero => exact Ne.symm hb
  | succ fuel ih =>
    cases job with
    | step k => exact ih (k ()) hjob
    | done action => cases action with
      | again s => exact ih (next s) (hnext s)
      | stop out =>
        intro h
        exact hjob (congrArg SearchAction.stop h)

theorem stageJob_ne_invalid (input : List Nat) (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (s : Nat) :
    (stageJob input prepare gs H hn s).result ≠ .stop .invalidInput := by
  rw [stageJob_result]
  split <;> simp

theorem runCoverFuel_invalid_only_after_validation (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (fuel : Nat)
    (h : runCoverFuel input validate prepare gs H hn fuel = .invalidInput) :
    validate.result = false := by
  cases hv : validate.result with
  | false => rfl
  | true =>
    have hnxt := stageJob_ne_invalid input prepare gs H hn
    have hi : (initialJob input validate prepare gs H hn).result ≠ .stop .invalidInput := by
      simpa [initialJob, hv] using hnxt 0
    exact False.elim (executeJobs_avoids _ .invalidInput (by simp) hnxt fuel _ hi h)

theorem runCoverFuel_success_validated (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (fuel : Nat)
    (c : CoverCertificate n j) (tokens : List CoverToken)
    (h : runCoverFuel input validate prepare gs H hn fuel = .certificate c tokens) :
    validate.result = true := by
  cases hv : validate.result with
  | true => rfl
  | false =>
    have hi : (initialJob input validate prepare gs H hn).result = .stop .invalidInput := by
      simp [initialJob, hv]
    have hout := executeJobs_stop_only (stageJob input prepare gs H hn) fuel
      (initialJob input validate prepare gs H hn) .invalidInput hi
    change runCoverFuel input validate prepare gs H hn fuel = .unknownResource ∨
      runCoverFuel input validate prepare gs H hn fuel = .invalidInput at hout
    rw [h] at hout
    simp at hout

theorem runCoverFuel_certificate_serialized (input : List Nat) (validate : FinTask Bool)
    (prepare : Nat → FinTask (Fin a → QInterval))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (fuel : Nat)
    (c : CoverCertificate n j) (tokens : List CoverToken)
    (h : runCoverFuel input validate prepare gs H hn fuel = .certificate c tokens) :
    serializeCertificate c = tokens := by
  have hc := runCoverFuel_checked input validate prepare gs H hn fuel
  rw [h] at hc
  exact parseCertificate_sound n j tokens c hc.1

end Cover
