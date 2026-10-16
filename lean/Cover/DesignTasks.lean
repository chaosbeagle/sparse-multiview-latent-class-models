import Cover.FiniteDesign
import Cover.FiniteTasks
import Cover.AlgebraicPrimitiveTasks

namespace Cover.FiniteDesign
open Gen.ModelEncoding.Ordered Cover.FiniteEnumeration
variable {G : Type} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G)

/-- Each design edge has exactly three groups; overlap uses the finite intersection,
not a scan through the entire abstract group universe. -/
def adjacentTask (e f : D.Edge) : FinTask Bool := do
  let different ← FinTask.primitive fun _ => decide (e≠f)
  let shared ← FinTask.primitive fun _ => decide ((e.val ∩ f.val).Nonempty)
  .done (different && shared)

theorem adjacentTask_result (e f : D.Edge) :
    (adjacentTask D e f).result = decide ((edgeGraph D).Adj e f) := by
  apply Bool.eq_iff_iff.mpr
  simp only [adjacentTask, FinTask.result_bindM, FinTask.primitive_result, FinTask.result_done,
    Bool.and_eq_true, decide_eq_true_eq, edgeGraph, Ext.TripleDesign.Adjacent, Ext.TripleDesign.Overlap]
  constructor
  · rintro ⟨hne,g,hg⟩
    exact ⟨hne,g,(Finset.mem_inter.mp hg).1,(Finset.mem_inter.mp hg).2⟩
  · rintro ⟨hne,g,hg,hf⟩
    exact ⟨hne,g,Finset.mem_inter.mpr ⟨hg,hf⟩⟩

def lengthTask {α : Type} : List α → FinTask ℕ
  | [] => .step fun _ => .done 0
  | _::xs => .step fun _ => do
    let n ← lengthTask xs
    .step fun _ => .done (n+1)

@[simp] theorem lengthTask_result {α : Type} (xs : List α) : (lengthTask xs).result = xs.length := by
  induction xs <;> simp_all [lengthTask]

def rangeTask : ℕ → FinTask (List ℕ)
  | 0 => .step fun _ => .done []
  | n+1 => .step fun _ => do
    let xs ← rangeTask n
    FinTask.appendTask xs [n]

@[simp] theorem rangeTask_result (n : ℕ) : (rangeTask n).result = List.range n := by
  induction n <;> simp_all [rangeTask, List.range_succ]

/-- A bounded walk search with explicit vertex-list and edge-test checkpoints. -/
def walkLengthTask (edges : Enumeration D.Edge) : ℕ → D.Edge → D.Edge → FinTask Bool
  | 0, e, f => FinTask.primitive fun _ => decide (e=f)
  | n+1, e, f => .step fun _ =>
    FinTask.anyTask (fun v => do
      let adjacent ← adjacentTask D e v
      if adjacent then walkLengthTask edges n v f else .done false) edges.values

theorem walkLengthTask_correct (edges : Enumeration D.Edge) (n : ℕ) (e f : D.Edge) :
    (walkLengthTask D edges n e f).result = true ↔
      ∃ p : (edgeGraph D).Walk e f, p.length=n := by
  induction n generalizing e f with
  | zero =>
    simp only [walkLengthTask, FinTask.primitive_result, decide_eq_true_eq]
    constructor
    · intro h; subst f; exact ⟨.nil,rfl⟩
    · rintro ⟨p,hp⟩; exact p.eq_of_length_eq_zero hp
  | succ n ih =>
    simp only [walkLengthTask, FinTask.result_step, FinTask.anyTask_result,
      FinTask.result_bindM, adjacentTask_result, List.any_eq_true]
    constructor
    · rintro ⟨v,_,hv⟩
      by_cases ha : (edgeGraph D).Adj e v
      · simp only [decide_eq_true ha, ↓reduceIte] at hv
        obtain ⟨p,hp⟩ := (ih v f).mp hv
        exact ⟨.cons ha p,by simp [hp]⟩
      · simp [ha] at hv
    · rintro ⟨p,hp⟩
      cases p with
      | nil => simp at hp
      | @cons u v w ha p =>
        refine ⟨v,edges.complete v,?_⟩
        simp only [decide_eq_true ha, ↓reduceIte]
        apply (ih v _).mpr
        exact ⟨p,by simpa using hp⟩

/-- Every path has fewer edges than the finite vertex count; all those lengths
are searched in ascending order from the exact input edge enumeration. -/
def reachabilityTask (edges : Enumeration D.Edge) (e f : D.Edge) : FinTask Bool := do
  let count ← lengthTask edges.values
  let lengths ← rangeTask count
  FinTask.anyTask (fun n => walkLengthTask D edges n e f) lengths

theorem reachabilityTask_result (edges : Enumeration D.Edge) (e f : D.Edge) :
    (reachabilityTask D edges e f).result = decide ((edgeGraph D).Reachable e f) := by
  apply Bool.eq_iff_iff.mpr
  simp only [reachabilityTask, FinTask.result_bindM, lengthTask_result, rangeTask_result,
    FinTask.anyTask_result, List.any_eq_true, List.mem_range, decide_eq_true_eq,
    walkLengthTask_correct]
  constructor
  · rintro ⟨n,_,p,_⟩; exact ⟨p⟩
  · intro hr
    obtain ⟨n,p,hp⟩ := (SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty (edgeGraph D) e f).mp hr
    refine ⟨n.val,?_,p,SimpleGraph.mem_finsetWalkLength_iff.mp hp⟩
    rw [length_eq_card]
    exact n.isLt

def sameComponentTask (edges : Enumeration D.Edge) (e : D.Edge) (xs : List D.Edge) : FinTask Bool :=
  FinTask.anyTask (fun f => reachabilityTask D edges e f) xs

theorem sameComponentTask_result (edges : Enumeration D.Edge) (e : D.Edge) (xs : List D.Edge) :
    letI := componentDecidableEq D
    (sameComponentTask D edges e xs).result = decide (componentOfEdge D e ∈ xs.map (componentOfEdge D)) := by
  letI := componentDecidableEq D
  apply Bool.eq_iff_iff.mpr
  simp only [sameComponentTask, FinTask.anyTask_result, List.any_eq_true,
    reachabilityTask_result, decide_eq_true_eq, reachable_iff_components,
    List.mem_map, componentOfEdge_eq]
  constructor
  · rintro ⟨f,hf,he⟩; exact ⟨f,hf,he.symm⟩
  · rintro ⟨f,hf,he⟩; exact ⟨f,hf,he.symm⟩

/-- Duplicate removal stays on representative edges. No task is quotient-lifted. -/
def dedupRepresentativesTask (edges : Enumeration D.Edge) : List D.Edge → FinTask (List D.Edge)
  | [] => .step fun _ => .done []
  | e::es => .step fun _ => do
    let rs ← dedupRepresentativesTask edges es
    let present ← sameComponentTask D edges e es
    .step fun _ => .done (if present then rs else e::rs)

theorem dedupRepresentativesTask_result (edges : Enumeration D.Edge) (xs : List D.Edge) :
    letI := componentDecidableEq D
    ((dedupRepresentativesTask D edges xs).result.map (componentOfEdge D)) =
      (xs.map (componentOfEdge D)).dedup := by
  letI := componentDecidableEq D
  induction xs with
  | nil => rfl
  | cons e es ih =>
    simp only [dedupRepresentativesTask, FinTask.result_step, FinTask.result_bindM,
      sameComponentTask_result, FinTask.result_done, List.map_cons, List.dedup_cons]
    simp only [decide_eq_true_eq]
    split_ifs <;> simp_all only [List.map_cons]

def reverseAccTask {α : Type} : List α → List α → FinTask (List α)
  | [], ys => .step fun _ => .done ys
  | x::xs, ys => .step fun _ => reverseAccTask xs (x::ys)

@[simp] theorem reverseAccTask_result {α : Type} (xs ys : List α) :
    (reverseAccTask xs ys).result = xs.reverse ++ ys := by
  induction xs generalizing ys <;> simp_all [reverseAccTask,List.reverse_cons,List.append_assoc]

def reverseTask {α : Type} (xs : List α) : FinTask (List α) := reverseAccTask xs []
@[simp] theorem reverseTask_result {α : Type} (xs : List α) : (reverseTask xs).result = xs.reverse := by
  simp [reverseTask]

/-- Reverse/dedup/reverse exactly preserves the original earliest-edge component order. -/
def componentValuesTask (edges : Enumeration D.Edge) : FinTask (List D.Component) := do
  let reversed ← reverseTask edges.values
  let representatives ← dedupRepresentativesTask D edges reversed
  let ordered ← reverseTask representatives
  FinTask.mapTask (fun e => FinTask.primitive (fun _ => componentOfEdge D e)) ordered

theorem componentValuesTask_result (edges : Enumeration D.Edge) :
    (componentValuesTask D edges).result = (components D edges).values := by
  letI := componentDecidableEq D
  simp only [componentValuesTask, FinTask.result_bindM, reverseTask_result,
    FinTask.mapTask_result, FinTask.primitive_result, List.map_reverse,
    dedupRepresentativesTask_result]
  simp only [components, List.map_reverse]

def componentsTask (edges : Enumeration D.Edge) : FinTask (Enumeration D.Component) := do
  let xs ← (componentValuesTask D edges).attach
  have he : xs.val = (components D edges).values := xs.property.trans (componentValuesTask_result D edges)
  .done ⟨xs.val,he.symm ▸ (components D edges).nodup,
    fun c => he.symm ▸ (components D edges).complete c⟩

theorem enumeration_ext {α : Type} {E F : Enumeration α} (h : E.values=F.values) : E=F := by
  cases E; cases F; cases h; rfl

theorem componentsTask_result (edges : Enumeration D.Edge) :
    (componentsTask D edges).result = components D edges := by
  apply enumeration_ext
  simp [componentsTask, FinTask.attach_result, componentValuesTask_result]

theorem incident_filter_nonempty (edges : Enumeration D.Edge) (g : G) :
    (edges.values.filter (fun e => decide (g∈e.val))) ≠ [] := by
  intro hnil
  obtain ⟨e,he,hg⟩ := D.covered g
  have hm : (⟨e,he⟩ : D.Edge) ∈ edges.values.filter (fun e => decide (g∈e.val)) := by
    simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨edges.complete _,hg⟩
  rw [hnil] at hm
  exact List.not_mem_nil hm

/-- The literal filter/head first-incident-edge algorithm, with every list position stepped. -/
def incidentTask (edges : Enumeration D.Edge) (g : G) : FinTask D.Edge := do
  let xs ← (FinTask.filterTask (fun e : D.Edge => decide (g∈e.val)) edges.values).attach
  have he : xs.val = edges.values.filter (fun e => decide (g∈e.val)) :=
    xs.property.trans (FinTask.filterTask_result _ _)
  .step fun _ => .done (xs.val.head (he.symm ▸ incident_filter_nonempty D edges g))

theorem incidentTask_result (edges : Enumeration D.Edge) (g : G) :
    (incidentTask D edges g).result = incident D edges g := by
  simp [incidentTask,FinTask.attach_result,incident]

def groupComponentTask (edges : Enumeration D.Edge) (g : G) : FinTask D.Component := do
  let e ← incidentTask D edges g
  FinTask.primitive fun _ => componentOfEdge D e

theorem groupComponentTask_result (edges : Enumeration D.Edge) (g : G) :
    (groupComponentTask D edges g).result = groupComponent D edges g := by
  simp [groupComponentTask,incidentTask_result,groupComponent]

end Cover.FiniteDesign
