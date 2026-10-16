import Cover.CompilerAstTasks

namespace Cover.CompilerLookupTasks
open Cover.FinTask Cover.CompilerAstTasks Gen.QEEncoding Gen.ModelEncoding.Ordered
variable {v a r : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {n : G → ℕ} {k : ℕ}

def edgeGroupsView (E : Compiler.Order (D := D) (n := n) (k := k))
    (groups : (e : D.Edge) → Enumeration (D.GroupAt e)) : Compiler.Order (D := D) (n := n) (k := k) :=
  { E with edgeGroups := groups }

/-- Edge-group enumeration is a task input; no edge-keyed family function is applied. -/
def observationLookupTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (groups : (e : D.Edge) → FinTask (Enumeration (D.GroupAt e)))
    (X : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a))
    (e : D.Edge) (x : D.Outcome (fun g => Fin (n g+1)) e) : FinTask (PolynomialExpr (v+a)) := do
  let gs ← groups e
  legacySumTask (fun z => do
    let wn ← X (.inl (D.component e,z))
    let w ← toLegacyTask wn
    let product ← legacyProdTask (fun g : D.GroupAt e => do
      let pn ← X (.inr ⟨g.val,z,x g⟩)
      toLegacyTask pn) gs.values
    primitive (fun _ => .mul w product)) E.latent.values

@[simp] theorem observationLookupTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (groups : (e : D.Edge) → FinTask (Enumeration (D.GroupAt e)))
    (X : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a))
    (e : D.Edge) (x : D.Outcome (fun g => Fin (n g+1)) e) :
    (observationLookupTask E groups X e x).result = Gen.ModelEncoding.Ordered.observation
      (edgeGroupsView E (fun e => (groups e).result)) (fun i => (X i).result.toLegacy) e x := by
  simp [observationLookupTask,edgeGroupsView,Gen.ModelEncoding.Ordered.observation,sumExpr,prodExpr]

def objectiveLookupTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (groups : (e : D.Edge) → FinTask (Enumeration (D.GroupAt e)))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a)) : FinTask (PolyExpr v a) := do
  let H ← legacySumTask (fun ex => do
    let p ← observationLookupTask E groups X ex.1 ex.2
    let q ← observationLookupTask E groups X' ex.1 ex.2
    let neg ← primitive (fun _ => PolynomialExpr.neg q)
    let diff ← primitive (fun _ => PolynomialExpr.add p neg)
    primitive (fun _ => PolynomialExpr.mul diff diff)) E.cells.values
  fromLegacyTask H

@[simp] theorem objectiveLookupTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (groups : (e : D.Edge) → FinTask (Enumeration (D.GroupAt e)))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a)) :
    (objectiveLookupTask E groups X X').result =
      Compiler.objective (edgeGroupsView E (fun e => (groups e).result))
        (fun i => (X i).result) (fun i => (X' i).result) := by
  simp [objectiveLookupTask,Compiler.objective,Gen.ModelEncoding.Ordered.H,sumExpr,
    PolynomialExpr.square,PolynomialExpr.sub,edgeGroupsView]

end Cover.CompilerLookupTasks
