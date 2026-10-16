import Cover.DesignTasks
import Cover.EnumerationTasks

namespace Cover.FiniteDesign
open Gen.ModelEncoding.Ordered Cover.FiniteEnumeration
variable {G : Type} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G)

abbrev ComponentPairRow := D.Edge × D.Edge × Bool

/-- Exact data specification only: execution uses flatReachabilityRowsTask. -/
def flatReachabilityRows (edges : Enumeration D.Edge) : List (ComponentPairRow D) :=
  edges.values.flatMap (fun e => edges.values.map (fun f =>
    (e,f,decide ((edgeGraph D).Reachable e f))))

/-- The certificate is an erased equality to the exact full, ordered pair table. -/
abbrev FlatComponentTable (edges : Enumeration D.Edge) :=
  {rows : List (ComponentPairRow D) // rows = flatReachabilityRows D edges}

def flatReachabilityRowsTask (edges : Enumeration D.Edge) : FinTask (List (ComponentPairRow D)) :=
  FinTask.flatMapTask (fun e => FinTask.mapTask (fun f => do
    let related ← reachabilityTask D edges e f
    FinTask.primitive (fun _ => (e,f,related))) edges.values) edges.values

@[simp] theorem flatReachabilityRowsTask_result (edges : Enumeration D.Edge) :
    (flatReachabilityRowsTask D edges).result = flatReachabilityRows D edges := by
  simp [flatReachabilityRowsTask,reachabilityTask_result,flatReachabilityRows]

def flatReachabilityTableTask (edges : Enumeration D.Edge) : FinTask (FlatComponentTable D edges) := do
  let rows ← (flatReachabilityRowsTask D edges).attach
  .step fun _ => .done ⟨rows.val,rows.property.trans (flatReachabilityRowsTask_result D edges)⟩

@[simp] theorem flatReachabilityTableTask_result (edges : Enumeration D.Edge) :
    (flatReachabilityTableTask D edges).result.val = flatReachabilityRows D edges :=
  (flatReachabilityTableTask D edges).result.property

/-- A mathematical list-query specification, not an atomic operation in the task. -/
def pairRowsQuery (rows : List (ComponentPairRow D)) (e f : D.Edge) : Bool :=
  rows.any fun row => decide (e=row.1) && decide (f=row.2.1) && row.2.2

/-- Every row is visited regardless of the queried representatives or cached bits.
Two bounded-triple edge comparisons and all Boolean operations have explicit checkpoints. -/
def pairRowsQueryTask : List (ComponentPairRow D) → D.Edge → D.Edge → FinTask Bool
  | [],_,_ => .step fun _ => .done false
  | row::rows,e,f => .step fun _ => do
    let left ← FinTask.primitive (fun _ => decide (e=row.1))
    let right ← FinTask.primitive (fun _ => decide (f=row.2.1))
    let hit ← FinTask.primitive (fun _ => left && right && row.2.2)
    let tail ← pairRowsQueryTask rows e f
    FinTask.primitive (fun _ => hit || tail)

@[simp] theorem pairRowsQueryTask_result (rows : List (ComponentPairRow D)) (e f : D.Edge) :
    (pairRowsQueryTask D rows e f).result = pairRowsQuery D rows e f := by
  induction rows <;> simp_all [pairRowsQueryTask,pairRowsQuery,List.any_cons]

@[simp] theorem pairRowsQueryTask_steps (rows : List (ComponentPairRow D)) (e f : D.Edge) :
    (pairRowsQueryTask D rows e f).steps = 5*rows.length+1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [pairRowsQueryTask,FinTask.steps,FinTask.steps_bind,FinTask.primitive_steps,
      FinTask.primitive_result,ih,List.length_cons]
    omega

theorem pairRowsQuery_flat (edges : Enumeration D.Edge) (e f : D.Edge) :
    pairRowsQuery D (flatReachabilityRows D edges) e f = decide ((edgeGraph D).Reachable e f) := by
  apply Bool.eq_iff_iff.mpr
  simp only [pairRowsQuery,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨row,hrow,htrue⟩
    obtain ⟨a,_,hb⟩ := List.mem_flatMap.mp hrow
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb
    simp only [Bool.and_eq_true,decide_eq_true_eq] at htrue
    obtain ⟨⟨he,hf⟩,hr⟩ := htrue
    subst a; subst b
    exact hr
  · intro hr
    refine ⟨(e,f,decide ((edgeGraph D).Reachable e f)),?_,?_⟩
    · exact List.mem_flatMap.mpr ⟨e,edges.complete e,
        List.mem_map.mpr ⟨f,edges.complete f,rfl⟩⟩
    · simp [hr]

theorem pairRowsQueryTask_component_result (edges : Enumeration D.Edge) (table : FlatComponentTable D edges)
    (e f : D.Edge) :
    (pairRowsQueryTask D table.val e f).result =
      @decide (D.component e=D.component f) (componentDecidableEq D _ _) := by
  rw [pairRowsQueryTask_result,table.property,pairRowsQuery_flat]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact reachable_iff_components D e f

/-- Quotient safety includes the entire transition tree, not just its final Boolean. -/
theorem pairRowsQueryTask_congr (edges : Enumeration D.Edge) (table : FlatComponentTable D edges)
    {e e' f f' : D.Edge} (he : Relation.EqvGen D.Overlap e e')
    (hf : Relation.EqvGen D.Overlap f f') :
    pairRowsQueryTask D table.val e f = pairRowsQueryTask D table.val e' f' := by
  apply FinTask.eq_of_steps_result
  · simp only [pairRowsQueryTask_steps]
  · rw [pairRowsQueryTask_component_result,pairRowsQueryTask_component_result]
    have heq := (D.component_eq_iff e e').mpr he
    have hfq := (D.component_eq_iff f f').mpr hf
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [heq,hfq]

/-- Fully stepped quotient-component equality over concrete stored rows.
No representative is chosen, no lookup closure is applied, and no graph search is rerun. -/
def componentEqTask (edges : Enumeration D.Edge) (table : FlatComponentTable D edges)
    (c d : D.Component) : FinTask Bool :=
  Quotient.liftOn₂ c d (fun e f => pairRowsQueryTask D table.val e f) (by
    intro e f e' f' he hf
    exact pairRowsQueryTask_congr D edges table he hf)

theorem componentEqTask_result [DecidableEq D.Component] (edges : Enumeration D.Edge)
    (table : FlatComponentTable D edges) (c d : D.Component) :
    (componentEqTask D edges table c d).result = decide (c=d) := by
  induction c using Quotient.inductionOn with
  | h e =>
    induction d using Quotient.inductionOn with
    | h f =>
      change (pairRowsQueryTask D table.val e f).result = _
      rw [pairRowsQueryTask_component_result]
      congr 1

theorem componentEqTask_steps (edges : Enumeration D.Edge) (table : FlatComponentTable D edges)
    (c d : D.Component) : (componentEqTask D edges table c d).steps = 5*table.val.length+1 := by
  induction c using Quotient.inductionOn with
  | h e =>
    induction d using Quotient.inductionOn with
    | h f => exact pairRowsQueryTask_steps D table.val e f

theorem componentEqTask_zero_unknown (edges : Enumeration D.Edge) (table : FlatComponentTable D edges)
    (c d : D.Component) : FinTask.run 0 (componentEqTask D edges table c d) = none := by
  induction c using Quotient.inductionOn with
  | h e =>
    induction d using Quotient.inductionOn with
    | h f =>
      change FinTask.run 0 (pairRowsQueryTask D table.val e f) = none
      cases table.val <;> rfl

theorem componentEqTask_run_sound [DecidableEq D.Component] (edges : Enumeration D.Edge)
    (table : FlatComponentTable D edges) (c d : D.Component) (fuel : ℕ) (equal : Bool)
    (hr : FinTask.run fuel (componentEqTask D edges table c d) = some equal) :
    equal = decide (c=d) := by
  have hs := FinTask.run_sound fuel _ _ hr
  rw [componentEqTask_result] at hs
  exact hs.symm

end Cover.FiniteDesign

namespace Cover.FiniteDesign
@[simp] theorem lengthTask_steps {α : Type} (xs : List α) :
    (lengthTask xs).steps = 2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [lengthTask,FinTask.steps,FinTask.steps_bind,FinTask.result_step,
      FinTask.result_done,ih,List.length_cons]
    omega
end Cover.FiniteDesign

namespace Cover.FinTask

/-- Quotient-safe complete length traversal; representation permutations have
exactly equal task results and exactly equal transition counts. -/
def multisetCardTask {α : Type} (s : Multiset α) : FinTask ℕ :=
  Quotient.liftOn s FiniteDesign.lengthTask (by
    intro xs ys h
    apply eq_of_steps_result
    · simp only [FiniteDesign.lengthTask_steps,h.length_eq]
    · simp only [FiniteDesign.lengthTask_result,h.length_eq])

@[simp] theorem multisetCardTask_result {α : Type} (s : Multiset α) :
    (multisetCardTask s).result = s.card := by
  induction s using Quotient.inductionOn with
  | h xs => exact FiniteDesign.lengthTask_result xs

@[simp] theorem multisetCardTask_steps {α : Type} (s : Multiset α) :
    (multisetCardTask s).steps = 2*s.card+1 := by
  induction s using Quotient.inductionOn with
  | h xs => exact FiniteDesign.lengthTask_steps xs

/-- Cardinality of arbitrary raw finite sets is traversed, not hidden in a primitive. -/
def finsetCardTask {α : Type} (s : Finset α) : FinTask ℕ := multisetCardTask s.val

@[simp] theorem finsetCardTask_result {α : Type} (s : Finset α) :
    (finsetCardTask s).result = s.card := multisetCardTask_result s.val

@[simp] theorem finsetCardTask_steps {α : Type} (s : Finset α) :
    (finsetCardTask s).steps = 2*s.card+1 := multisetCardTask_steps s.val

theorem finsetCardTask_zero_unknown {α : Type} (s : Finset α) :
    run 0 (finsetCardTask s) = none := by
  cases s with
  | mk xs hxs =>
    induction xs using Quotient.inductionOn with
    | h xs => cases xs <;> rfl

end Cover.FinTask
