import Cover.CodedGauges
import Cover.CompilerAstTasks

namespace Cover.CompilerGaugeTasks
open Cover.FinTask Cover.CompilerAstTasks Gen.QEEncoding Gen.ModelEncoding.Ordered
variable {G : Type} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {n : G → ℕ} {k v a : ℕ}
variable [DecidableEq D.Component]

/-- Pullback applies one coded permutation through its explicit transition tree. -/
def pullbackTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (row : GaugeRow E.components.values.length (k+1))
    (gc : G → D.Component) (eqTask : D.Component → D.Component → FinTask Bool)
    (heq : ∀ c d,(eqTask c d).result=decide (c=d)) :
    Coord (D := D) (n := n) (k := k) → FinTask (Coord (D := D) (n := n) (k := k))
  | .inl (c,z) => .step fun _ => do
      let w ← gaugeApplyTask E.components row c z eqTask heq
      primitive (fun _ => .inl (c,w))
  | .inr ⟨g,z,y⟩ => .step fun _ => do
      let w ← gaugeApplyTask E.components row (gc g) z eqTask heq
      primitive (fun _ => .inr ⟨g,w,y⟩)

@[simp] theorem pullbackTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (row : GaugeRow E.components.values.length (k+1))
    (gc : G → D.Component) (hgc : ∀ g,gc g=D.groupComponent g)
    (eqTask : D.Component → D.Component → FinTask Bool)
    (heq : ∀ c d,(eqTask c d).result=decide (c=d))
    (i : Coord (D := D) (n := n) (k := k)) :
    (pullbackTask E row gc eqTask heq i).result = E.coordinatePullback (row.denote E.components) i := by
  rw [E.coordinatePullback_correct]
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;>
    simp [pullbackTask,hgc,Gen.Geometry.coordinatePerm]

def distanceRowTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (row : GaugeRow E.components.values.length (k+1))
    (gc : G → D.Component) (eqTask : D.Component → D.Component → FinTask Bool)
    (heq : ∀ c d,(eqTask c d).result=decide (c=d))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a)) : FinTask (PolyExpr v a) := do
  let F ← legacySumTask (fun i => do
    let pn ← X i
    let p ← toLegacyTask pn
    let j ← pullbackTask E row gc eqTask heq i
    let qn ← X' j
    let q ← toLegacyTask qn
    let neg ← primitive (fun _ => PolynomialExpr.neg q)
    let diff ← primitive (fun _ => PolynomialExpr.add p neg)
    primitive (fun _ => PolynomialExpr.mul diff diff)) E.coordinates.values
  fromLegacyTask F

@[simp] theorem distanceRowTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (row : GaugeRow E.components.values.length (k+1))
    (gc : G → D.Component) (hgc : ∀ g,gc g=D.groupComponent g)
    (eqTask : D.Component → D.Component → FinTask Bool)
    (heq : ∀ c d,(eqTask c d).result=decide (c=d))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a)) :
    (distanceRowTask E row gc eqTask heq X X').result =
      Compiler.distance E (row.denote E.components) (fun i => (X i).result) (fun i => (X' i).result) := by
  simp [distanceRowTask,pullbackTask_result E row gc hgc,Compiler.distance,
    Gen.ModelEncoding.Ordered.distance,sumExpr,PolynomialExpr.square,PolynomialExpr.sub]

def farRowsTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (gc : G → D.Component) (eqTask : D.Component → D.Component → FinTask Bool)
    (heq : ∀ c d,(eqTask c d).result=decide (c=d))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := 3)) : FinTask (List (PolyExpr v 3)) := do
  let rows ← codedGaugeRowsTask E.components E.latent
  mapTask (fun row => do
    let p ← distanceRowTask E row gc eqTask heq X X'
    let neg ← primitive (fun _ => PolyExpr.neg (.scalar 2))
    primitive (fun _ => PolyExpr.add p neg)) rows

@[simp] theorem farRowsTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (gc : G → D.Component) (hgc : ∀ g,gc g=D.groupComponent g)
    (eqTask : D.Component → D.Component → FinTask Bool)
    (heq : ∀ c d,(eqTask c d).result=decide (c=d))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := 3)) :
    (farRowsTask E gc eqTask heq X X').result =
      (FiniteEnumeration.pi E.components (fun _ => FiniteEnumeration.permutations E.latent)).values.map
        (fun q => PolyExpr.sub (Compiler.distance E q (fun i => (X i).result) (fun i => (X' i).result)) (.scalar 2)) := by
  simp only [farRowsTask,FinTask.result_bindM,FinTask.mapTask_result,
    distanceRowTask_result E _ gc hgc,primitive_result]
  rw [←codedGaugeRowsTask_denote,List.map_map]
  rfl

end Cover.CompilerGaugeTasks
