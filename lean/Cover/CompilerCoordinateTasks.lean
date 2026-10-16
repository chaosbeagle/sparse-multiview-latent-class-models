import Cover.CompilerAstTasks

namespace Cover.CompilerCoordinateTasks
open Cover.FinTask Gen.ModelEncoding.Ordered
variable {G : Type} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {n : G → ℕ} {k : ℕ}

/-- Sum tags and the bounded tuple of scalar indices are explicit primitives.
Component comparisons are supplied as resumable tasks, rather than opaque graph searches. -/
def reducedEqTask [DecidableEq D.Component]
    (componentTest : D.Component → D.Component → FinTask Bool) :
    Normalization.ReducedCoordinate D n k → Normalization.ReducedCoordinate D n k → FinTask Bool
  | .inl (c,z), .inl (d,w) => .step fun _ => do
      let same ← componentTest c d
      primitive (fun _ => same && decide (z=w))
  | .inr i, .inr j => primitive (fun _ => decide (i=j))
  | .inl _, .inr _ => .step fun _ => .done false
  | .inr _, .inl _ => .step fun _ => .done false

@[simp] theorem reducedEqTask_result [DecidableEq D.Component]
    (componentTest : D.Component → D.Component → FinTask Bool)
    (hcomponent : ∀ c d,(componentTest c d).result=decide (c=d))
    (i j : Normalization.ReducedCoordinate D n k) :
    (reducedEqTask componentTest i j).result = decide (i=j) := by
  rcases i with ⟨c,z⟩ | i <;> rcases j with ⟨d,w⟩ | j <;>
    simp [reducedEqTask,hcomponent,Prod.mk.injEq]

/-- Every retained-coordinate leaf performs its ordered search inside FinTask. -/
def variableTask {I : Type} [DecidableEq I] (E : Enumeration I)
    (eqTask : I → I → FinTask Bool) (heq : ∀ i j,(eqTask i j).result=decide (i=j))
    (d : ℕ) (hd : d=E.values.length) (right : Bool) (i : I) : FinTask (PolyExpr (d+d) 3) := do
  let j ← FiniteEnumeration.indexTaskWith E i eqTask heq
  primitive (fun _ => PolyExpr.var (if right then Fin.natAdd d (Fin.cast hd.symm j)
    else Fin.castAdd d (Fin.cast hd.symm j)))

@[simp] theorem variableTask_result {I : Type} [DecidableEq I] (E : Enumeration I)
    (eqTask : I → I → FinTask Bool) (heq : ∀ i j,(eqTask i j).result=decide (i=j))
    (d : ℕ) (hd : d=E.values.length) (right : Bool) (i : I) :
    (variableTask E eqTask heq d hd right i).result =
      PolyExpr.var (if right then Fin.natAdd d (Fin.cast hd.symm ((FiniteEnumeration.indexEquiv E).symm i))
        else Fin.castAdd d (Fin.cast hd.symm ((FiniteEnumeration.indexEquiv E).symm i))) := by
  simp [variableTask]

end Cover.CompilerCoordinateTasks
