import Cover.FiniteTasks
import Cover.A06InputCodec
import Cover.AlgebraicCodecTasks
import Cover.FlatComponentCache

namespace Cover.InputTasks
open Cover.FinTask Cover.FiniteDesign

/-- Nat successor is the deliberately atomic arithmetic primitive for length scanning. -/
def lengthTask {α : Type} : List α → FinTask ℕ
  | [] => .step fun _ => .done 0
  | _::xs => .step fun _ => do
      let n ← lengthTask xs
      .step fun _ => .done (n+1)
@[simp] theorem lengthTask_result {α : Type} (xs : List α) : (lengthTask xs).result = xs.length := by
  induction xs <;> simp_all [lengthTask]

/-- Design validation has checkpoints throughout all group/edge scans and duplicate tests.
Nat/Fin comparisons, a single Finset membership/cardinality, and Finset equality are declared primitives. -/
def validateDesignTask (I : Syntax) : FinTask Bool := .step fun _ => do
  let hc ← allTask (fun e => do
    let count ← finsetCardTask e
    primitive (fun _ => decide (count = 3))) I.edges
  if hc then do
    let groups ← finRangeTask I.groups
    let hr ← primitive (fun _ => decide (0 < I.rankPred))
    let hs ← allTask (fun g => primitive (fun _ => decide (I.rankPred ≤ I.outputPred g))) groups
    let he ← primitive (fun _ => decide (I.edges ≠ []))
    let hn ← nodupTask I.edges
    let hv ← allTask (fun g => anyTask (fun e => primitive (fun _ => decide (g ∈ e))) I.edges) groups
    .step fun _ => .done (hr && hs && he && hn && hv)
  else .done false

theorem validateDesignTask_result (I : Syntax) :
    (validateDesignTask I).result = FiniteDesign.validate I := by
  apply Bool.eq_iff_iff.mpr
  simp [validateDesignTask,FiniteDesign.validate,FiniteDesign.Valid,
    List.all_eq_true,List.any_eq_true]
  split <;> simp_all [List.all_eq_true,List.any_eq_true] <;> tauto

def readBlockTask : List ℕ → FinTask (Option (List ℕ × List ℕ))
  | [] => .step fun _ => .done none
  | n::xs => .step fun _ => takeTask n xs
@[simp] theorem readBlockTask_result (xs : List ℕ) :
    (readBlockTask xs).result = DesignCodec.readBlock xs := by
  cases xs <;> simp [readBlockTask,DesignCodec.readBlock,takeTask_result]

def readIndicesTask (g : ℕ) : List ℕ → FinTask (Option (List (Fin g)))
  | [] => .step fun _ => .done (some [])
  | i::is => .step fun _ =>
      if hi : i < g then do
        let js ← readIndicesTask g is
        .step fun _ => .done (js.map (fun ks => ⟨i,hi⟩::ks))
      else .done none
@[simp] theorem readIndicesTask_result (g : ℕ) (xs : List ℕ) :
    (readIndicesTask g xs).result = DesignCodec.readIndices g xs := by
  induction xs with
  | nil => rfl
  | cons i is ih => by_cases hi : i < g <;> simp [readIndicesTask,DesignCodec.readIndices,hi,ih]

/-- Only after scanning the length and checking it equals three is the fixed-size triple predicate evaluated. -/
def readEdgeTask (g : ℕ) (xs : List ℕ) : FinTask (Option (Finset (Fin g) × List ℕ)) := do
  let block ← readBlockTask xs
  match block with
  | none => .done none
  | some (ys,rest) => do
    let indices ← readIndicesTask g ys
    match indices with
    | none => .done none
    | some zs => do
      let len ← lengthTask zs
      .step fun _ =>
        if len = 3 then
          .done (if zs.Nodup ∧ zs.Pairwise (· ≤ ·) then some (zs.toFinset,rest) else none)
        else .done none
@[simp] theorem readEdgeTask_result (g : ℕ) (xs : List ℕ) :
    (readEdgeTask g xs).result = DesignCodec.readEdge g xs := by
  simp_all only [readEdgeTask,FinTask.result_bindM,readBlockTask_result,DesignCodec.readEdge]
  split
  · simp_all
  · simp_all only [FinTask.result_bindM,readIndicesTask_result]
    split
    · simp_all
    · simp_all only [FinTask.result_bindM,lengthTask_result,FinTask.result_step,FinTask.result_done]
      split <;> simp_all

def readEdgesTask (g : ℕ) : ℕ → List ℕ → FinTask (Option (List (Finset (Fin g)) × List ℕ))
  | 0, xs => .step fun _ => .done (some ([],xs))
  | m+1, xs => .step fun _ => do
      let head ← readEdgeTask g xs
      match head with
      | none => .done none
      | some (e,rest) => do
        let tail ← readEdgesTask g m rest
        .step fun _ => .done (tail.map (fun q => (e::q.1,q.2)))
@[simp] theorem readEdgesTask_result (g m : ℕ) (xs : List ℕ) :
    (readEdgesTask g m xs).result = DesignCodec.readEdges g m xs := by
  induction m generalizing xs with
  | zero => rfl
  | succ m ih =>
    simp_all only [readEdgesTask,FinTask.result_step,FinTask.result_bindM,readEdgeTask_result,DesignCodec.readEdges]
    split
    · simp_all
    · simp_all only [FinTask.result_bindM,ih,FinTask.result_step,FinTask.result_done]
      split <;> simp_all

/-- A declared representation-copy step. Physical allocation limits require the external guard. -/
def copySizeArrayTask (xs : List ℕ) : FinTask {a : Array ℕ // a = xs.toArray} :=
  .step fun _ => .done ⟨xs.toArray,rfl⟩
@[simp] theorem copySizeArrayTask_result (xs : List ℕ) :
    (copySizeArrayTask xs).result = ⟨xs.toArray,rfl⟩ := rfl

/-- Token and edge parsing plus design scans are internally stepped. -/
def parseDesignTask : List ℕ → FinTask (Option Syntax)
  | 1::g::r::xs => .step fun _ =>
    FinTask.bind (readBlockTask xs) (fun block => match block with
    | none => .done none
    | some (ns,rest) => FinTask.bind (certify (lengthTask ns)) (fun len =>
      FinTask.bind (copySizeArrayTask ns) (fun sizes => .step fun _ =>
      if hn : len.val = g then
        let outputs : Fin g → ℕ := fun i => sizes.val[i.val]' (by
          have hh : ns.length = g := (len.property.trans (lengthTask_result ns)).symm.trans hn
          have ha : sizes.val.size = ns.length := by rw [sizes.property]; simp
          omega)
        match rest with
        | [] => .done none
        | m::tail => FinTask.bind (readEdgesTask g m tail) (fun result => match result with
          | none => .done none
          | some (es,leftover) => .step fun _ =>
            if leftover = [] then
              let I : Syntax := ⟨g,r,outputs,es⟩
              FinTask.bind (validateDesignTask I) (fun valid => .done (if valid then some I else none))
            else .done none)
      else .done none)))
  | _ => .step fun _ => .done none

theorem parseDesignTask_result (raw : List ℕ) :
    (parseDesignTask raw).result = DesignCodec.parse raw := by
  unfold parseDesignTask DesignCodec.parse
  split
  · simp_all only [FinTask.result_step,FinTask.result_bind,FinTask.result_bindM,readBlockTask_result]
    split
    · simp_all
    · simp_all only [FinTask.result_bind,FinTask.certify_result,lengthTask_result,copySizeArrayTask_result,primitive_result,FinTask.result_step,List.getElem_toArray,List.get_eq_getElem]
      split
      · split
        · simp_all
        · simp_all only [FinTask.result_bind,FinTask.result_bindM,readEdgesTask_result]
          split
          · simp_all
          · simp_all only [FinTask.result_step]
            split
            · simp_all only [FinTask.result_bind,FinTask.result_bindM,validateDesignTask_result,FiniteDesign.validate,
                FinTask.result_done,decide_eq_true_eq]
            · simp_all
      · simp_all
  · simp_all

/-- All three frames are consumed token by token. -/
def readFramesTask : List ℕ → FinTask (Option (List ℕ × List ℕ × List ℕ))
  | 1::xs => .step fun _ => do
    let first ← readBlockTask xs
    match first with
    | none => .done none
    | some (d,rest) => do
      let second ← readBlockTask rest
      match second with
      | none => .done none
      | some (w,tail) => do
        let third ← readBlockTask tail
        .step fun _ => .done (match third with
          | some (s,[]) => some (d,w,s)
          | _ => none)
  | _ => .step fun _ => .done none
@[simp] theorem readFramesTask_result (raw : List ℕ) :
    (readFramesTask raw).result = A06InputCodec.readFrames raw := by
  unfold readFramesTask A06InputCodec.readFrames
  split
  · simp_all only [FinTask.result_step,FinTask.result_bind,FinTask.result_bindM,readBlockTask_result]
    split
    · simp_all
    · simp_all only [FinTask.result_bindM,readBlockTask_result]
      split
      · simp_all
      · simp_all only [FinTask.result_bindM,readBlockTask_result,FinTask.result_step,FinTask.result_done]
        split <;> simp_all
        all_goals split <;> simp_all
  · simp_all

/-- Canonical scalar parsing uses the supplied internally stepped integer/polynomial codec. -/
def scalarCanonicalTask (raw : List ℕ) : FinTask (Option AlgCode) :=
  AlgCodec.parseCanonicalTask raw
@[simp] theorem scalarCanonicalTask_result (raw : List ℕ) :
    (scalarCanonicalTask raw).result = AlgCodec.parseCanonical raw :=
  AlgCodec.parseCanonicalTask_result raw

def parseRawTask (raw : List ℕ) : FinTask (Option A06.Input) := do
  let frames ← readFramesTask raw
  match frames with
  | none => .done none
  | some (d,w,s) => do
    let design ← parseDesignTask d
    match design with
    | none => .done none
    | some design => do
      let weight ← scalarCanonicalTask w
      match weight with
      | none => .done none
      | some weight => do
        let sigma ← scalarCanonicalTask s
        .step fun _ => .done (sigma.map (fun sigma => ⟨design,weight,sigma⟩))

theorem parseRawTask_result (raw : List ℕ) :
    (parseRawTask raw).result = A06InputCodec.parseRaw raw := by
  simp_all only [parseRawTask,FinTask.result_bindM,readFramesTask_result,A06InputCodec.parseRaw]
  split
  · simp_all
  · simp_all only [FinTask.result_bindM,parseDesignTask_result,A06InputCodec.parseParts]
    split
    · simp_all
    · simp_all only [FinTask.result_bindM,scalarCanonicalTask_result]
      split
      · simp_all
      · simp_all only [FinTask.result_bindM,scalarCanonicalTask_result,FinTask.result_step,FinTask.result_done]
        split <;> simp_all
end Cover.InputTasks
