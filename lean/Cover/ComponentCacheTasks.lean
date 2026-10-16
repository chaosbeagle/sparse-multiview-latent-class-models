import Cover.DesignTasks
import Cover.EnumerationTasks

namespace Cover.FiniteDesign
open Gen.ModelEncoding.Ordered Cover.FiniteEnumeration
variable {G : Type} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G)

/-- Every edge-pair search finishes inside the task before the resulting lookup
closure is returned. The stored function indexes only the supplied edge keys. -/
def reachabilityTableTask (edges : Enumeration D.Edge) : FinTask (D.Edge → D.Edge → Bool) :=
  dependentTask edges fun e => dependentTask edges fun f => reachabilityTask D edges e f

@[simp] theorem reachabilityTableTask_result (edges : Enumeration D.Edge) :
    (reachabilityTableTask D edges).result = fun e f => decide ((edgeGraph D).Reachable e f) := by
  simp [reachabilityTableTask,reachabilityTask_result]

/-- This dictionary reads a cached Boolean; it does not invoke a graph search.
The logical relation proof is erased by compilation. -/
@[reducible] def componentRelationFromTable (table : D.Edge → D.Edge → Bool)
    (correct : ∀ e f, table e f = true ↔ Relation.EqvGen D.Overlap e f) :
    DecidableRel (Relation.EqvGen D.Overlap) := fun e f =>
  if found : table e f = true then isTrue ((correct e f).mp found)
  else isFalse (fun related => found ((correct e f).mpr related))

/-- Quotient equality is induced by the cached representative relation. -/
def componentDecidableEqFromTable (table : D.Edge → D.Edge → Bool)
    (correct : ∀ e f, table e f = true ↔ Relation.EqvGen D.Overlap e f) :
    DecidableEq D.Component := by
  letI : DecidableRel (Relation.EqvGen D.Overlap) := componentRelationFromTable D table correct
  exact Quotient.decidableEq

/-- Full cached equality construction is resource-visible. No lookup closure
recomputes finite reachability or constructs a fresh finite path enumeration. -/
def componentDecidableEqTask (edges : Enumeration D.Edge) : FinTask (DecidableEq D.Component) := .step fun _ => do
  let table ← (reachabilityTableTask D edges).attach
  have correct : ∀ e f, table.val e f = true ↔ Relation.EqvGen D.Overlap e f := by
    intro e f
    rw [table.property,reachabilityTableTask_result,decide_eq_true_eq]
    exact (reachable_iff_components D e f).trans (D.component_eq_iff e f)
  .step fun _ => .done (componentDecidableEqFromTable D table.val correct)

@[simp] theorem componentDecidableEqTask_result (edges : Enumeration D.Edge) :
    (componentDecidableEqTask D edges).result = componentDecidableEq D :=
  Subsingleton.elim _ _

theorem componentDecidableEqTask_run_sound (edges : Enumeration D.Edge) (fuel : ℕ)
    (dictionary : DecidableEq D.Component)
    (h : FinTask.run fuel (componentDecidableEqTask D edges) = some dictionary) :
    dictionary = componentDecidableEq D := by
  have he := FinTask.run_sound fuel _ _ h
  rw [componentDecidableEqTask_result] at he
  exact he.symm

theorem componentDecidableEqTask_zero_unknown (edges : Enumeration D.Edge) :
    FinTask.run 0 (componentDecidableEqTask D edges) = none := rfl

theorem componentDecidableEqTask_has_fuel (edges : Enumeration D.Edge) :
    ∃ fuel, (FinTask.run fuel (componentDecidableEqTask D edges)).isSome = true := by
  refine ⟨(componentDecidableEqTask D edges).steps,?_⟩
  rw [FinTask.run_sufficient _ _ (le_refl _)]
  rfl

/-- The Boolean observed from the cached quotient dictionary has the original
component equality semantics, independently of which representatives occur. -/
theorem componentDecidableEqTask_correct (edges : Enumeration D.Edge) (c d : D.Component) :
    @decide (c=d) ((componentDecidableEqTask D edges).result c d) =
      @decide (c=d) (componentDecidableEq D c d) := by
  rw [componentDecidableEqTask_result]

end Cover.FiniteDesign
