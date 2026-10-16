import Cover.A06RawValidation
import Cover.CompilerTasks
import Cover.InputSerializationTasks
import Cover.A06Executable

set_option maxHeartbeats 1600000

namespace Cover.A06
open FinTask

 def compiledArray (d : CompilerTasks.CompiledData) : Fin d.constraintCount → PolyExpr d.n 3 :=
  fun i => d.constraints.get ⟨i.val, by rw [← d.count_eq]; exact i.isLt⟩

/-- Direct native-table lookup; no repeated List.get traversal is used at leaves. -/
def arrayConstraints (d : CompilerTasks.CompiledData) (table : Array (PolyExpr d.n 3))
    (ht : table = d.constraints.toArray) : Fin d.constraintCount → PolyExpr d.n 3 :=
  fun i => table[i.val]'(by rw [ht]; simpa [d.count_eq] using i.isLt)

theorem arrayConstraints_eq (d : CompilerTasks.CompiledData) (table : Array (PolyExpr d.n 3))
    (ht : table = d.constraints.toArray) : arrayConstraints d table ht = compiledArray d := by
  funext i
  simp [arrayConstraints,compiledArray,ht]

 theorem compiledArray_align (I : Input) (h : Valid I) (d : CompilerTasks.CompiledData)
    (hd : d = CompilerTasks.canonicalData I.design h.1) :
    Runtime.alignArray I h (congrArg CompilerTasks.CompiledData.n hd)
      (congrArg CompilerTasks.CompiledData.constraintCount hd) (compiledArray d) =
      ProjectSemantics.constraintArray I.design h.1 := by
  subst d
  unfold Runtime.alignArray
  apply eq_of_heq
  exact (cast_heq _ _).trans (by rfl)

 theorem compiledObjective_align (I : Input) (h : Valid I) (d : CompilerTasks.CompiledData)
    (hd : d = CompilerTasks.canonicalData I.design h.1) :
    Runtime.alignObjective I h (congrArg CompilerTasks.CompiledData.n hd) d.objective =
      ConcreteCompiler.objective I.design h.1 := by
  subst d
  unfold Runtime.alignObjective
  exact eq_of_heq (cast_heq _ _)

/-- Actual concrete compiler, with stored runtime n/count and exact cached syntax.
    Compiler initialization granularity is documented by CompilerTasks itself. -/
def admittedStageJob (I : Input) (h : Valid I) (raw : List Nat) (s : Nat) : FinTask CappedAction := do
  let data ← (CompilerTasks.compileTask I.design h.1).attach
  have hd : data.val = CompilerTasks.canonicalData I.design h.1 :=
    data.property.trans (CompilerTasks.compileTask_result I.design h.1)
  let table ← (FinTask.primitive (fun _ => data.val.constraints.toArray)).attach
  have ht : table.val = data.val.constraints.toArray := table.property.trans (FinTask.primitive_result _)
  Runtime.stageCoreTask I h raw data.val.n data.val.constraintCount
    (congrArg CompilerTasks.CompiledData.n hd) (congrArg CompilerTasks.CompiledData.constraintCount hd)
    (arrayConstraints data.val table.val ht) data.val.objective s

 theorem admittedStageJob_result (I : Input) (h : Valid I) (raw : List Nat)
    (hraw : raw = A06InputCodec.serialize I) (s : Nat) :
    (admittedStageJob I h raw s).result = stageAction I h s := by
  simp only [admittedStageJob,FinTask.result_bindM]
  generalize hp : (CompilerTasks.compileTask I.design h.1).attach.result = data
  have hd : data.val = CompilerTasks.canonicalData I.design h.1 :=
    data.property.trans (CompilerTasks.compileTask_result I.design h.1)
  generalize ha : (FinTask.primitive (fun _ => data.val.constraints.toArray)).attach.result = table
  have ht : table.val = data.val.constraints.toArray := table.property.trans (FinTask.primitive_result _)
  apply Runtime.stageCoreTask_result I h raw hraw data.val.n data.val.constraintCount
    (congrArg CompilerTasks.CompiledData.n hd) (congrArg CompilerTasks.CompiledData.constraintCount hd)
    (arrayConstraints data.val table.val ht) data.val.objective
  · rw [arrayConstraints_eq]
    exact compiledArray_align I h data.val hd
  · exact compiledObjective_align I h data.val hd

 def admittedTokensTask (raw : List Nat) : FinTask (Option (AdmittedTokens raw)) :=
  validateTokenTask raw (InputTasks.parseRawTask raw) (InputTasks.parseRawTask_result raw)
    InputTasks.serializeInputTask InputTasks.serializeInputTask_result

 theorem admittedTokensTask_result (raw : List Nat) :
    (admittedTokensTask raw).result.map AdmittedTokens.input = A06InputCodec.parse raw :=
  validateTokenTask_result raw _ _ _ _

/-- Raw finite input is fully parsed, exactly validated, and canonically rebound
    before any stage can execute. Interrupted work is handled only by execute. -/
def rawTokenStageJob (raw : List Nat) (s : Nat) : FinTask CappedAction := do
  let parsed ← admittedTokensTask raw
  match parsed with
  | none => .done (.stop .invalidInput)
  | some admitted => admittedStageJob admitted.input admitted.valid raw s

 theorem rawTokenStageJob_checked (raw : List Nat) (s : Nat) :
    Capped.ActionChecked (fun r => r.Checked ∧ r.BoundToTokens raw) (rawTokenStageJob raw s).result := by
  simp only [rawTokenStageJob,FinTask.result_bindM]
  split
  · trivial
  · rename_i admitted ha
    rw [admittedStageJob_result _ _ _ admitted.binding.symm]
    exact stageAction_bound _ _ raw admitted.binding s

 theorem rawTokenStageJob_admitted (I : Input) (h : Valid I) (s : Nat) :
    (rawTokenStageJob (A06InputCodec.serialize I) s).result = stageAction I h s := by
  have hm := admittedTokensTask_result (A06InputCodec.serialize I)
  rw [A06InputCodec.parse_serialize I h] at hm
  cases hp : (admittedTokensTask (A06InputCodec.serialize I)).result with
  | none => simp [hp] at hm
  | some admitted =>
    rw [hp] at hm
    have he : admitted.input = I := Option.some.inj hm
    rcases admitted with ⟨J,hJ,hbound⟩
    dsimp only at he
    subst J
    simp only [rawTokenStageJob,FinTask.result_bindM,hp]
    exact admittedStageJob_result I hJ _ rfl s

/-- Array materialization is an explicit representation primitive. Every subsequent
    byte/natural/list parser step and all mathematical validation is task controlled. -/
def rawByteStageJob (raw : ByteArray) (s : Nat) : FinTask CappedAction := .step fun _ => do
  let parsed ← Bytes.decodeNatsTask raw.data.toList
  match parsed with
  | none => .done (.stop .invalidInput)
  | some (tokens,rest) => .step fun _ =>
      if rest = [] then rawTokenStageJob tokens s else .done (.stop .invalidInput)

 theorem rawByteStageJob_admitted (I : Input) (h : Valid I) (s : Nat) :
    (rawByteStageJob (serializeInputBytes I) s).result = stageAction I h s := by
  have hd := Bytes.decodeNats_encodeNats (A06InputCodec.serialize I) []
  simp only [List.append_nil] at hd
  change Bytes.decodeNats (Bytes.encodeList Bytes.encodeNat (A06InputCodec.serialize I)) = some (A06InputCodec.serialize I,[]) at hd
  simp [rawByteStageJob,serializeInputBytes,Bytes.decodeNatsTask_result,Bytes.encodeNats,
    hd,rawTokenStageJob_admitted I h s]

 theorem boundToInputBytes (raw : ByteArray) (tokens : List Nat)
    (hd : Bytes.decodeNats raw.data.toList = some (tokens,[])) (r : Returned)
    (hb : r.BoundToTokens tokens) : serializeInputBytes r.input = raw := by
  have he := Bytes.decodeNats_sound raw.data.toList tokens [] hd
  simp only [List.append_nil] at he
  change Bytes.encodeList Bytes.encodeNat tokens = raw.data.toList at he
  apply ByteArray.ext
  simp only [serializeInputBytes]
  rw [hb,he]

 theorem actionChecked_mono {P Q : Returned → Prop} (action : CappedAction)
    (h : ∀ r, P r → Q r) (ha : Capped.ActionChecked P action) : Capped.ActionChecked Q action := by
  cases action with
  | again s => trivial
  | stop out => cases out with
    | certificate r => exact h r ha
    | unknownResource => trivial
    | invalidInput => trivial
    | implementationError => trivial

 theorem rawByteStageJob_checked (raw : ByteArray) (s : Nat) :
    Capped.ActionChecked (fun r => r.Checked ∧ serializeInputBytes r.input = raw)
      (rawByteStageJob raw s).result := by
  simp only [rawByteStageJob,FinTask.result_step,FinTask.result_bindM,Bytes.decodeNatsTask_result]
  cases hd : Bytes.decodeNats raw.data.toList with
  | none => trivial
  | some pair =>
    rcases pair with ⟨tokens,rest⟩
    simp only [FinTask.result_step]
    by_cases hr : rest = []
    · subst rest
      simp only [ite_true]
      apply actionChecked_mono _ _ (rawTokenStageJob_checked tokens s)
      intro r h
      exact ⟨h.1,boundToInputBytes raw tokens hd r h.2⟩
    · simp [hr,Capped.ActionChecked,Capped.Checked]

/-- The final concrete finite-input capped program. Revalidating the same exact raw
    input before successive stages is finite and changes no search-stage semantics.
    A zero or exhausted budget returns only UNKNOWN_RESOURCE. -/
def runCoverCapped (raw : ByteArray) (fuel : Nat) : CappedResult :=
  Capped.execute (rawByteStageJob raw) fuel (rawByteStageJob raw 0)

 theorem runCoverCapped_zero (raw : ByteArray) : runCoverCapped raw 0 = .unknownResource := rfl

 theorem runCoverCapped_prefix (raw : ByteArray) (f g : Nat) (hfg : f≤g)
    (h : runCoverCapped raw f ≠ .unknownResource) : runCoverCapped raw g = runCoverCapped raw f :=
  Capped.fuel_prefix _ f g hfg _ h

 theorem runCoverCapped_checked (raw : ByteArray) (fuel : Nat) :
    Capped.Checked (fun r => r.Checked ∧ serializeInputBytes r.input = raw) (runCoverCapped raw fuel) :=
  Capped.checked _ _ (rawByteStageJob_checked raw) fuel _ (rawByteStageJob_checked raw 0)

/-- CERTIFICATE includes completed exact byte parsing and independent scalar/tree
    replay, tied to the exact original input bytes. -/
 theorem runCoverCapped_success_fully_checked (raw : ByteArray) (fuel : Nat) (r : Returned)
    (hr : runCoverCapped raw fuel = .certificate r) :
    parseInputBytes raw = some r.input ∧ serializeInputBytes r.input = raw ∧
      verifyCertificateBytes r.input r.valid r.bytes = true := by
  have hc := runCoverCapped_checked raw fuel
  rw [hr] at hc
  refine ⟨?_,hc.2,?_⟩
  · rw [←hc.2]; exact parseInputBytes_roundtrip r.input r.valid
  · simp [verifyCertificateBytes,hc.1.1,hc.1.2]

 theorem runCoverCapped_eventual (I : Input) (h : Valid I) :
    ∃ fuel result, runCoverCapped (serializeInputBytes I) fuel = .certificate result := by
  let next := rawByteStageJob (serializeInputBytes I)
  have hshape s : (next s).result = .again (s+1) ∨ ∃ value, (next s).result = .stop (.certificate value) := by
    rw [rawByteStageJob_admitted I h s]
    exact stageAction_shape I h s
  obtain ⟨s0,hs0⟩ := coverStage_eventually_succeeds I h
  obtain ⟨t,ht⟩ := hs0 s0 le_rfl
  have hs : (next (0+s0)).result = .stop (.certificate
      ⟨I,h,certificateAt I h s0 t,Bytes.serializeEvidenceByteArray (certificateAt I h s0 t)⟩) := by
    rw [Nat.zero_add,rawByteStageJob_admitted I h s0]
    simp [stageAction,ht]
  exact Capped.eventual next hshape s0 0 _ hs

 theorem runCoverCapped_invalid_completed (raw : ByteArray) (fuel : Nat)
    (hr : runCoverCapped raw fuel = .invalidInput) : parseInputBytes raw = none := by
  cases hp : parseInputBytes raw with
  | none => rfl
  | some I =>
    have hv := parseInputBytes_valid hp
    have he := parseInputBytes_exact hp
    have hn s : (rawByteStageJob raw s).result ≠ .stop .invalidInput := by
      rw [←he,rawByteStageJob_admitted I hv s]
      rcases stageAction_shape I hv s with hs | ⟨r,hs⟩ <;> rw [hs] <;> simp
    exact False.elim (Capped.avoids _ .invalidInput (by simp) hn fuel _ (hn 0) hr)

end Cover.A06

namespace Cover.A06

 theorem runCoverCapped_eventual_of_parsed {raw : ByteArray} {I : Input}
    (hp : parseInputBytes raw = some I) :
    ∃ fuel result, runCoverCapped raw fuel = .certificate result := by
  rw [←parseInputBytes_exact hp]
  exact runCoverCapped_eventual I (parseInputBytes_valid hp)

/-- Operational capped success exports the exact all-real far-pair separation. -/
 theorem runCoverCapped_success_separates (raw : ByteArray) (fuel : Nat) (r : Returned)
    (hr : runCoverCapped raw fuel = .certificate r)
    {w σ : ℝ} (hwd : r.input.weight.denotes w) (hσd : r.input.sigma.denotes σ) :
    (0 < dyadic r.certificate.base.k) ∧
    ∀ θ ∈ Gen.Conditioned.K (FiniteDesign.toBaseline r.input.design r.valid.1)
      (fun g => Fin (r.input.design.outputPred g+1)) (r.input.design.rankPred+1) w σ,
    ∀ η ∈ Gen.Conditioned.K (FiniteDesign.toBaseline r.input.design r.valid.1)
      (fun g => Fin (r.input.design.outputPred g+1)) (r.input.design.rankPred+1) w σ,
    (Literal.R (alphabetSizes r.input) (edgeLists r.input)).eval w σ ≤
      Gen.ConditionedRates.distance (FiniteDesign.toBaseline r.input.design r.valid.1)
        (fun g => Fin (r.input.design.outputPred g+1)) (r.input.design.rankPred+1) θ η →
    (dyadic r.certificate.base.k : ℝ) ≤
      ‖Gen.Geometry.observation (FiniteDesign.toBaseline r.input.design r.valid.1)
        (fun g => Fin (r.input.design.outputPred g+1)) (r.input.design.rankPred+1) θ -
       Gen.Geometry.observation (FiniteDesign.toBaseline r.input.design r.valid.1)
        (fun g => Fin (r.input.design.outputPred g+1)) (r.input.design.rankPred+1) η‖ := by
  have hc := runCoverCapped_checked raw fuel
  rw [hr] at hc
  exact verifyCoverCertificate_sound r.input r.valid r.certificate hc.1.2 hwd hσd

end Cover.A06


namespace Cover.A06

/-- For actual admitted input, finite exhaustion is the only alternative to a
    complete certificate. Stable errors are excluded by eventual actual success. -/
theorem runCoverCapped_admitted_status (I : Input) (h : Valid I) (fuel : Nat) :
    runCoverCapped (serializeInputBytes I) fuel = .unknownResource ∨
      ∃ result, runCoverCapped (serializeInputBytes I) fuel = .certificate result := by
  classical
  obtain ⟨successFuel,result,hs⟩ := runCoverCapped_eventual I h
  by_cases hu : runCoverCapped (serializeInputBytes I) fuel = .unknownResource
  · exact Or.inl hu
  · right
    have hp := runCoverCapped_prefix (serializeInputBytes I) fuel (max fuel successFuel)
      (le_max_left _ _) hu
    have hsneq : runCoverCapped (serializeInputBytes I) successFuel ≠ .unknownResource := by rw [hs]; simp
    have hq := runCoverCapped_prefix (serializeInputBytes I) successFuel (max fuel successFuel)
      (le_max_right _ _) hsneq
    exact ⟨result,hp.symm.trans (hq.trans hs)⟩

theorem runCoverCapped_admitted_no_errors (I : Input) (h : Valid I) (fuel : Nat) :
    runCoverCapped (serializeInputBytes I) fuel ≠ .invalidInput ∧
      runCoverCapped (serializeInputBytes I) fuel ≠ .implementationError := by
  rcases runCoverCapped_admitted_status I h fuel with hu | ⟨result,hr⟩
  · rw [hu]; simp
  · rw [hr]; simp

end Cover.A06
