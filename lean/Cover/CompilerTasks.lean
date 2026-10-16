import Cover.CompilerCoordinateTasks
import Cover.InputTasks
import Cover.CompilerInitializationTasks
import Cover.FlatComponentCache
import Cover.CompilerLookupTasks
import Cover.CompilerGaugeTasks
import Cover.CompilerRepresentationTasks

set_option maxHeartbeats 1600000
namespace Cover.CompilerTasks
open Cover.FinTask Cover.CompilerAstTasks Cover.CompilerCoordinateTasks Cover.CompilerLookupTasks Cover.CompilerGaugeTasks
variable {v : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {n : G → ℕ} {k : ℕ}

abbrev CT := CoordTask (D := D) (n := n) (k := k) (v := v) (a := 3)

def weightsTask (E : Compiler.Order (D := D) (n := n) (k := k)) (X : CT (D := D) (n := n) (k := k) (v := v)) : FinTask (List (PolyExpr v 3)) :=
  flatMapTask (fun c => mapTask (fun z => do
    let p ← X (.inl (c,z))
    let neg ← primitive (fun _ => PolyExpr.neg (.scalar 0))
    primitive (fun _ => PolyExpr.add p neg)) E.latent.values) E.components.values
@[simp] theorem weightsTask_result (E : Compiler.Order (D := D) (n := n) (k := k)) (X : CT (D := D) (n := n) (k := k) (v := v)) :
    (weightsTask E X).result = Compiler.weightConstraints E (.scalar 0) (fun i => (X i).result) := by
  simp [weightsTask,Compiler.weightConstraints,PolyExpr.sub]

def kernelsTask (E : Compiler.Order (D := D) (n := n) (k := k)) (X : CT (D := D) (n := n) (k := k) (v := v)) : FinTask (List (PolyExpr v 3)) :=
  flatMapTask (fun g => flatMapTask (fun z => mapTask (fun y => X (.inr ⟨g,z,y⟩))
    (E.outputs g).values) E.latent.values) E.groups.values
@[simp] theorem kernelsTask_result (E : Compiler.Order (D := D) (n := n) (k := k)) (X : CT (D := D) (n := n) (k := k) (v := v)) :
    (kernelsTask E X).result = Compiler.kernelConstraints E (fun i => (X i).result) := by
  simp [kernelsTask,Compiler.kernelConstraints]

/-- A proof-level view replacing only principal family lookup functions by their literal order. -/
def principalView (E : Compiler.Order (D := D) (n := n) (k := k)) : Compiler.Order (D := D) (n := n) (k := k) :=
  { E with principal := canonicalPrincipal E.principal }

def gramsTask (E : Compiler.Order (D := D) (n := n) (k := k)) (X : CT (D := D) (n := n) (k := k) (v := v)) : FinTask (List (PolyExpr v 3)) :=
  flatMapTask (fun g => principalSortedTask E.principal (gramTask E X g)) E.groups.values
@[simp] theorem gramsTask_result (E : Compiler.Order (D := D) (n := n) (k := k)) (X : CT (D := D) (n := n) (k := k) (v := v)) :
    (gramsTask E X).result = SquaredCompiler.gramConstraints (principalView E) (fun i => (X i).result) := by
  simp [gramsTask,SquaredCompiler.gramConstraints,principalView]
  rfl

def modelTask (E : Compiler.Order (D := D) (n := n) (k := k)) (X : CT (D := D) (n := n) (k := k) (v := v)) : FinTask (List (PolyExpr v 3)) := do
  let weights ← weightsTask E X
  let kernels ← kernelsTask E X
  let grams ← gramsTask E X
  let first ← appendTask weights kernels
  appendTask first grams
@[simp] theorem modelTask_result (E : Compiler.Order (D := D) (n := n) (k := k)) (X : CT (D := D) (n := n) (k := k) (v := v)) :
    (modelTask E X).result = SquaredCompiler.modelConstraints (principalView E) (fun i => (X i).result) := by
  simp [modelTask,SquaredCompiler.modelConstraints,principalView]
  rfl

def farTask (E : Compiler.Order (D := D) (n := n) (k := k)) (X X' : CT (D := D) (n := n) (k := k) (v := v)) : FinTask (List (PolyExpr v 3)) :=
  mapTask (fun q => do
    let p ← distanceTask E q X X'
    let neg ← primitive (fun _ => PolyExpr.neg (.scalar 2))
    primitive (fun _ => PolyExpr.add p neg)) E.gauges.values
@[simp] theorem farTask_result (E : Compiler.Order (D := D) (n := n) (k := k)) (X X' : CT (D := D) (n := n) (k := k) (v := v)) :
    (farTask E X X').result = SquaredCompiler.farConstraints E (fun i => (X i).result) (fun i => (X' i).result) := by
  simp [farTask,SquaredCompiler.farConstraints,PolyExpr.sub]

def pairedTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (X X' : CT (D := D) (n := n) (k := k) (v := v)) : FinTask (List (PolyExpr v 3)) := do
  let left ← modelTask E X
  let right ← modelTask E X'
  let far ← farTask E X X'
  let first ← appendTask left right
  appendTask first far
@[simp] theorem pairedTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (X X' : CT (D := D) (n := n) (k := k) (v := v)) :
    (pairedTask E X X').result =
      SquaredCompiler.modelConstraints (principalView E) (fun i => (X i).result) ++
      SquaredCompiler.modelConstraints (principalView E) (fun i => (X' i).result) ++
      SquaredCompiler.farConstraints (principalView E) (fun i => (X i).result) (fun i => (X' i).result) := by
  simp [pairedTask,principalView]
  rfl

def pairedRowsTask [DecidableEq D.Component]
    (E : Compiler.Order (D := D) (n := n) (k := k))
    (gc : G → D.Component) (_hgc : ∀ g,gc g=D.groupComponent g)
    (eqTask : D.Component → D.Component → FinTask Bool)
    (heq : ∀ c d,(eqTask c d).result=decide (c=d))
    (X X' : CT (D := D) (n := n) (k := k) (v := v)) : FinTask (List (PolyExpr v 3)) := do
  let left ← modelTask E X
  let right ← modelTask E X'
  let far ← farRowsTask E gc eqTask heq X X'
  let first ← appendTask left right
  appendTask first far

@[simp] theorem pairedRowsTask_result [DecidableEq D.Component]
    (E : Compiler.Order (D := D) (n := n) (k := k))
    (gc : G → D.Component) (hgc : ∀ g,gc g=D.groupComponent g)
    (eqTask : D.Component → D.Component → FinTask Bool)
    (heq : ∀ c d,(eqTask c d).result=decide (c=d))
    (X X' : CT (D := D) (n := n) (k := k) (v := v)) :
    (pairedRowsTask E gc hgc eqTask heq X X').result =
      SquaredCompiler.modelConstraints (principalView E) (fun i => (X i).result) ++
      SquaredCompiler.modelConstraints (principalView E) (fun i => (X' i).result) ++
      (FiniteEnumeration.pi E.components (fun _ => FiniteEnumeration.permutations E.latent)).values.map
        (fun q => PolyExpr.sub (Compiler.distance E q (fun i => (X i).result) (fun i => (X' i).result)) (.scalar 2)) := by
  simp [pairedRowsTask,farRowsTask_result E gc hgc]

def constraintsTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (u u' : Normalization.ReducedCoordinate D n k → PolyExpr v 3) : FinTask (List (PolyExpr v 3)) :=
  pairedTask E (coordinatesTask u) (coordinatesTask u')
@[simp] theorem constraintsTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (u u' : Normalization.ReducedCoordinate D n k → PolyExpr v 3) :
    (constraintsTask E u u').result = SquaredCompiler.constraints (principalView E) u u' := by
  simp [constraintsTask,SquaredCompiler.constraints]

@[simp] theorem principalView_modelOrdering (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    principalView (ConcreteCompiler.modelOrdering I h) = ConcreteCompiler.modelOrdering I h := rfl

@[simp] theorem canonical_gauge_values (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    [DecidableEq (FiniteDesign.toBaseline I h).Component] :
    (FiniteEnumeration.pi (ConcreteCompiler.modelOrdering I h).components
      (fun _ => FiniteEnumeration.permutations (ConcreteCompiler.modelOrdering I h).latent)).values =
      (ConcreteCompiler.modelOrdering I h).gauges.values := by
  unfold ConcreteCompiler.modelOrdering
  dsimp only
  congr 2 <;> exact Subsingleton.elim _ _

/-- The two Nat fields are stored runtime values, not thunks referring back to compilation. -/
structure CompiledData where
  n : ℕ
  constraintCount : ℕ
  constraints : List (PolyExpr n 3)
  count_eq : constraintCount = constraints.length
  objective : PolyExpr n 3

/-- Canonical specification only; capped execution calls compileTask instead. -/
def canonicalData (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) : CompiledData where
  n := ConcreteCompiler.dimension I h + ConcreteCompiler.dimension I h
  constraintCount := (ConcreteCompiler.constraints I h).length
  constraints := ConcreteCompiler.constraints I h
  count_eq := rfl
  objective := ConcreteCompiler.objective I h

/-- Exact internally stepped construction of all concrete model orderings. -/
def orderingInitializationTask (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    FinTask (Gen.ModelEncoding.Ordered.ModelOrdering (FiniteDesign.toBaseline I h)
      (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) :=
  CompilerInitializationTasks.modelOrderingTask I h
@[simp] theorem orderingInitializationTask_result (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    (orderingInitializationTask I h).result = ConcreteCompiler.modelOrdering I h :=
  CompilerInitializationTasks.modelOrderingTask_result I h

/-- Cached coordinate indexing: only the finite lookup is performed at each variable leaf. -/
def leftCached (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    (e : Fin (ConcreteCompiler.dimension I h) ≃
      Normalization.ReducedCoordinate (FiniteDesign.toBaseline I h) I.outputPred I.rankPred) :
    Normalization.ReducedCoordinate (FiniteDesign.toBaseline I h) I.outputPred I.rankPred →
      PolyExpr (ConcreteCompiler.dimension I h + ConcreteCompiler.dimension I h) 3 :=
  fun i => .var (Fin.castAdd (ConcreteCompiler.dimension I h) (e.symm i))

def rightCached (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) (d : ℕ)
    (hd : d = ConcreteCompiler.dimension I h)
    (e : Fin (ConcreteCompiler.dimension I h) ≃
      Normalization.ReducedCoordinate (FiniteDesign.toBaseline I h) I.outputPred I.rankPred) :
    Normalization.ReducedCoordinate (FiniteDesign.toBaseline I h) I.outputPred I.rankPred →
      PolyExpr (ConcreteCompiler.dimension I h + ConcreteCompiler.dimension I h) 3 :=
  fun i => .var ⟨d + (e.symm i).val, by rw [hd]; exact Nat.add_lt_add_left (e.symm i).isLt _⟩

@[simp] theorem leftCached_spec (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    leftCached I h (ConcreteCompiler.reducedEquiv I h) = ConcreteCompiler.leftVariables I h := rfl
@[simp] theorem rightCached_spec (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    rightCached I h (ConcreteCompiler.dimension I h) rfl (ConcreteCompiler.reducedEquiv I h) =
      ConcreteCompiler.rightVariables I h := rfl

/-- Connectivity, finite enumeration, polynomial construction and count scanning are
internally stepped. Ordered coordinate index scans and their bounded tuple tests are stepped.
Component equality scans a previously computed flat reachability table within tasks;
physical cost and allocation size are not asserted. -/
def compilePreparedUsingTask (I : FiniteDesign.Syntax) (_h : FiniteDesign.Valid I)
    (D : Ext.TripleDesign (Fin I.groups))
    (componentEq : DecidableEq D.Component)
    (E : Gen.ModelEncoding.Ordered.ModelOrdering D
      (fun g => Fin (I.outputPred g+1)) (I.rankPred+1))
    (red : Gen.ModelEncoding.Ordered.Enumeration
      (Normalization.ReducedCoordinate D I.outputPred I.rankPred))
    (edges : Gen.ModelEncoding.Ordered.Enumeration D.Edge)
    (table : FiniteDesign.FlatComponentTable D edges) :
    FinTask CompiledData := .step fun _ => do
  let _ : DecidableEq D.Component := componentEq
  let d ← certify (InputTasks.lengthTask red.values)
  have hd : d.val = red.values.length := d.property.trans (InputTasks.lengthTask_result red.values)
  let componentTest := FiniteDesign.componentEqTask D edges table
  have hcomponent := FiniteDesign.componentEqTask_result D edges table
  let gc ← certify (finFamilyTask (fun g : Fin I.groups =>
    FiniteDesign.groupComponentTask D edges g))
  have hgc (g) : gc.val g = D.groupComponent g := by
    rw [gc.property,finFamilyTask_result]
    exact (FiniteDesign.groupComponentTask_result _ _ g).trans (FiniteDesign.groupComponent_eq _ _ g)
  let eqTask := reducedEqTask componentTest
  have heq : ∀ i j,(eqTask i j).result=decide (i=j) :=
    reducedEqTask_result _ (FiniteDesign.componentEqTask_result _ _ _)
  let u := variableTask red eqTask heq d.val hd false
  let u' := variableTask red eqTask heq d.val hd true
  let X := coordinatesTaskM u
  let X' := coordinatesTaskM u'
  let gs ← pairedRowsTask E gc.val hgc componentTest hcomponent X X'
  let H ← objectiveLookupTask E (fun e => FiniteEnumeration.indicesTask E.groups e.val) X X' 
  let count ← certify (InputTasks.lengthTask gs)
  .step fun _ => .done {
    n := d.val+d.val
    constraintCount := count.val
    constraints := gs
    count_eq := count.property.trans (InputTasks.lengthTask_result gs)
    objective := H }


def compilePreparedTask (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    (componentEq : DecidableEq (FiniteDesign.toBaseline I h).Component)
    (E : Gen.ModelEncoding.Ordered.ModelOrdering (FiniteDesign.toBaseline I h)
      (fun g => Fin (I.outputPred g+1)) (I.rankPred+1))
    (red : Gen.ModelEncoding.Ordered.Enumeration
      (Normalization.ReducedCoordinate (FiniteDesign.toBaseline I h) I.outputPred I.rankPred))
    (edges : Gen.ModelEncoding.Ordered.Enumeration (FiniteDesign.toBaseline I h).Edge)
    (table : FiniteDesign.FlatComponentTable (FiniteDesign.toBaseline I h) edges) :
    FinTask CompiledData :=
  compilePreparedUsingTask I h (FiniteDesign.toBaseline I h) componentEq E red edges table

theorem compilePreparedTask_result (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    (edges : Gen.ModelEncoding.Ordered.Enumeration (FiniteDesign.toBaseline I h).Edge)
    (table : FiniteDesign.FlatComponentTable (FiniteDesign.toBaseline I h) edges) :
    (compilePreparedTask I h (FiniteDesign.componentDecidableEq (FiniteDesign.toBaseline I h))
      (ConcreteCompiler.modelOrdering I h) (ConcreteCompiler.reducedEnumeration I h) edges table).result =
      canonicalData I h := by
  simp only [compilePreparedTask,compilePreparedUsingTask,FinTask.result_step,FinTask.result_bindM]
  generalize hlenResult : (certify (InputTasks.lengthTask (ConcreteCompiler.reducedEnumeration I h).values)).result = counted
  obtain ⟨d,hd⟩ := counted
  have hlen : d = (ConcreteCompiler.reducedEnumeration I h).values.length :=
    hd.trans (InputTasks.lengthTask_result _)
  cases hlen
  simp only [primitive_result,FinTask.certify_result,InputTasks.lengthTask_result,
    pairedRowsTask_result,principalView_modelOrdering,canonical_gauge_values,objectiveLookupTask_result,
    FiniteEnumeration.indicesTask_result,coordinatesTaskM_result,
    variableTask_result,Bool.false_eq_true,ite_false,ite_true,Fin.cast_refl,FinTask.result_done]
  rfl


@[simp] theorem compilePreparedUsingTask_at_base (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    (eq : DecidableEq (FiniteDesign.toBaseline I h).Component)
    (E : Gen.ModelEncoding.Ordered.ModelOrdering (FiniteDesign.toBaseline I h)
      (fun g => Fin (I.outputPred g+1)) (I.rankPred+1))
    (red : Gen.ModelEncoding.Ordered.Enumeration
      (Normalization.ReducedCoordinate (FiniteDesign.toBaseline I h) I.outputPred I.rankPred))
    (edges : Gen.ModelEncoding.Ordered.Enumeration (FiniteDesign.toBaseline I h).Edge)
    (table : FiniteDesign.FlatComponentTable (FiniteDesign.toBaseline I h) edges) :
    compilePreparedUsingTask I h (FiniteDesign.toBaseline I h) eq E red edges table =
      compilePreparedTask I h eq E red edges table := by
  unfold compilePreparedTask
  rfl

def compileUsingBaselineTask (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    (D : Ext.TripleDesign (Fin I.groups)) (hD : D=FiniteDesign.toBaseline I h) : FinTask CompiledData := .step fun _ => do
  let initialized ← CompilerInitializationTasks.initializationForTask I h D hD
  let edges ← CompilerInitializationTasks.inputEdgesForTask I h D hD
  let table ← FiniteDesign.flatReachabilityTableTask D edges
  let red ← CompilerInitializationTasks.reducedForTask I h D hD initialized.1 initialized.2
  compilePreparedUsingTask I h D initialized.1 initialized.2 red edges table

theorem compileUsingBaselineTask_result (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    (D : Ext.TripleDesign (Fin I.groups)) (hD : D=FiniteDesign.toBaseline I h) :
    (compileUsingBaselineTask I h D hD).result=canonicalData I h := by
  cases hD
  simp only [compileUsingBaselineTask,FinTask.result_step,FinTask.result_bindM,
    CompilerInitializationTasks.initializationForTask_at_base,
    CompilerInitializationTasks.inputEdgesForTask_at_base,
    CompilerInitializationTasks.reducedForTask_at_base,
    CompilerInitializationTasks.initializationTask_result,CompilerInitializationTasks.reducedUsingTask_result,
    compilePreparedUsingTask_at_base,compilePreparedTask_result]

def compileTask (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) : FinTask CompiledData := .step fun _ => do
  let design ← FiniteDesign.directBaselineTask I h
  compileUsingBaselineTask I h design.val design.property

theorem compileTask_result (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    (compileTask I h).result = canonicalData I h := by
  simp only [compileTask,FinTask.result_step,FinTask.result_bindM,compileUsingBaselineTask_result]

/-- Consumers use cached dimensions; these identities are theorem-level interfaces only. -/
theorem compileTask_n (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    (compileTask I h).result.n = ConcreteCompiler.dimension I h + ConcreteCompiler.dimension I h := by
  rw [compileTask_result]; rfl

theorem compileTask_count (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    (compileTask I h).result.constraintCount = (ConcreteCompiler.constraints I h).length := by
  rw [compileTask_result]; rfl

end Cover.CompilerTasks
