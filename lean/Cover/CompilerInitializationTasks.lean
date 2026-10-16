import Cover.ConcreteCompiler
import Cover.EnumerationTasks
import Cover.DesignTasks
import Cover.ComponentCacheTasks
import Cover.InputTasks
import Cover.NativeFamilyTasks
import Cover.CompilerEnumerationTasks

set_option maxHeartbeats 2400000
namespace Cover.CompilerInitializationTasks
open Cover.FinTask Cover.FiniteEnumeration Cover.FiniteDesign Gen.ModelEncoding.Ordered Cover.CompilerEnumerationTasks

/-- Input edges are traversed in their supplied order; proof-only subtype wrappers do not change data. -/
def inputEdgesTask (I : Syntax) (h : Valid I) : FinTask (Enumeration (toBaseline I h).Edge) := do
  let marked ← certify (attachWithTask (fun e => e ∈ I.edges) I.edges (fun _ he => he))
  let es ← certify (mapTask (fun e : {e // e ∈ I.edges} => primitive (fun _ =>
    (⟨e.val,List.mem_toFinset.mpr e.property⟩ : (toBaseline I h).Edge))) marked.val)
  have he : es.val = (inputEdges I h).values := by
    rw [es.property,FinTask.mapTask_result,marked.property,attachWithTask_result]
    rfl
  .done ⟨es.val,he.symm ▸ (inputEdges I h).nodup,
    fun e => he.symm ▸ (inputEdges I h).complete e⟩
@[simp] theorem inputEdgesTask_result (I : Syntax) (h : Valid I) :
    (inputEdgesTask I h).result = inputEdges I h := by
  apply FiniteEnumeration.enumeration_ext
  simp [inputEdgesTask,inputEdges]

/-- All connectivity, product, permutation, principal-subset and cell construction phases
use their explicit internally stepped algorithms. Cached dependent families prevent regeneration. -/
def modelOrderingForTask (I : Syntax) (D : Ext.TripleDesign (Fin I.groups))
    (edges : Enumeration D.Edge)
    (componentEq : DecidableEq D.Component) :
    FinTask (ModelOrdering D (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) := .step fun _ => do
  let _ : DecidableEq D.Component := componentEq
  let cs ← componentsTask D edges
  let _ : Fintype D.Component := Fintype.ofList cs.values cs.complete
  let gs ← finEnumerationTask I.groups
  let zs ← finEnumerationTask (I.rankPred+1)
  let ys ← finFamilyTask (fun g : Fin I.groups => finEnumerationTask (I.outputPred g+1))
  let edgeGroups ← dependentTask edges (fun e => indicesTask gs e.val)
  let cells ← sigmaWithTask edges (fun e => do
    let groups ← indicesTask gs e.val
    piTask groups (fun g => ys g.val))
  let weights ← prodTask cs zs
  let kernelFamilies ← finFamilyTask (fun g : Fin I.groups => prodTask zs (ys g))
  let kernels ← sigmaTask gs kernelFamilies
  let coords ← FiniteEnumeration.sumTask weights kernels
  let permutations ← permutationEnumerationTask zs
  let gauges ← piTask cs (fun _ => permutations)
  let principal ← principalOrderingTask (I.rankPred+1)
  let gc ← certify (finFamilyTask (fun g : Fin I.groups => groupComponentTask D edges g))
  have hgc (g) : gc.val g = D.groupComponent g := by
    rw [gc.property,finFamilyTask_result]
    exact (groupComponentTask_result D edges g).trans (groupComponent_eq D edges g)
  .step fun _ => .done {
    components := cs
    groups := gs
    latent := zs
    outputs := ys
    edgeGroups := edgeGroups
    cells := cells
    coordinates := coords
    gauges := gauges
    principal := principal
    coordinatePullback := fun q i => match i with
      | .inl (c,z) => .inl (c,q c z)
      | .inr ⟨g,z,y⟩ => .inr ⟨g,q (gc.val g) z,y⟩
    coordinatePullback_correct := by
      intro q i
      rcases i with ⟨c,z⟩ | ⟨g,z,y⟩
      · rfl
      · simp only [hgc,Gen.Geometry.coordinatePerm,Equiv.coe_fn_mk] }


def modelOrderingWithEdgesTask (I : Syntax) (h : Valid I)
    (edges : Enumeration (toBaseline I h).Edge)
    (componentEq : DecidableEq (toBaseline I h).Component) :
    FinTask (ModelOrdering (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) :=
  modelOrderingForTask I (toBaseline I h) edges componentEq

theorem modelOrderingWithEdgesTask_result (I : Syntax) (h : Valid I) :
    (modelOrderingWithEdgesTask I h (inputEdges I h) (componentDecidableEq (toBaseline I h))).result = ConcreteCompiler.modelOrdering I h := by
  simp only [modelOrderingWithEdgesTask,modelOrderingForTask,FinTask.result_step,FinTask.result_bindM,inputEdgesTask_result,
    componentsTask_result,finEnumerationTask_result,finFamilyTask_result,dependentTask_result,indicesTask_result,
    piTask_result,sigmaTask_result,sigmaWithTask_result,prodTask_result,FiniteEnumeration.sumTask_result,
    permutationEnumerationTask_result,principalOrderingTask_result,FinTask.certify_result,
    groupComponentTask_result,FinTask.result_done]
  unfold ConcreteCompiler.modelOrdering
  congr 1
  all_goals first | (funext q i; rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;> rfl) | rfl | skip
  apply FiniteEnumeration.enumeration_ext
  unfold FiniteEnumeration.pi FiniteEnumeration.ofCover
  dsimp only
  congr 1 <;> first | rfl | exact Subsingleton.elim _ _

/-- The runtime equality dictionary travels with the ordering whose closures capture it. -/
def initializationTask (I : Syntax) (h : Valid I) :
    FinTask (DecidableEq (toBaseline I h).Component ×
      ModelOrdering (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) := .step fun _ => do
  let edges ← inputEdgesTask I h
  let componentEq ← componentDecidableEqTask (toBaseline I h) edges
  let ordering ← modelOrderingWithEdgesTask I h edges componentEq
  .done (componentEq,ordering)

theorem initializationTask_result (I : Syntax) (h : Valid I) :
    (initializationTask I h).result =
      (componentDecidableEq (toBaseline I h),ConcreteCompiler.modelOrdering I h) := by
  simp only [initializationTask,FinTask.result_step,FinTask.result_bindM,inputEdgesTask_result,
    componentDecidableEqTask_result,modelOrderingWithEdgesTask_result,FinTask.result_done]

def modelOrderingTask (I : Syntax) (h : Valid I) :
    FinTask (ModelOrdering (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) := do
  let initialized ← initializationTask I h
  .done initialized.2

theorem modelOrderingTask_result (I : Syntax) (h : Valid I) :
    (modelOrderingTask I h).result = ConcreteCompiler.modelOrdering I h := by
  simp only [modelOrderingTask,FinTask.result_bindM,initializationTask_result,FinTask.result_done]

/-- Reduced indexing reuses the already computed model ordering. -/
def reducedUsingTask (I : Syntax) (h : Valid I)
    (componentEq : DecidableEq (toBaseline I h).Component)
    (E : ModelOrdering (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) :
    FinTask (Enumeration (Normalization.ReducedCoordinate (toBaseline I h) I.outputPred I.rankPred)) := .step fun _ => do
  let _ : DecidableEq (toBaseline I h).Component := componentEq
  let latentPred ← finEnumerationTask I.rankPred
  let outputsPred ← finFamilyTask (fun g : Fin I.groups => finEnumerationTask (I.outputPred g))
  let weights ← prodTask E.components latentPred
  let kernelFamilies ← finFamilyTask (fun g : Fin I.groups => prodTask E.latent (outputsPred g))
  let kernels ← sigmaTask E.groups kernelFamilies
  FiniteEnumeration.sumTask weights kernels

theorem reducedUsingTask_result (I : Syntax) (h : Valid I) :
    (reducedUsingTask I h (componentDecidableEq (toBaseline I h)) (ConcreteCompiler.modelOrdering I h)).result =
      ConcreteCompiler.reducedEnumeration I h := by
  simp only [reducedUsingTask,FinTask.result_step,FinTask.result_bindM,
    finEnumerationTask_result,finFamilyTask_result,dependentTask_result,prodTask_result,sigmaTask_result,
    FiniteEnumeration.sumTask_result]
  rfl
def reducedWithOrderingTask (I : Syntax) (h : Valid I)
    (E : ModelOrdering (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) :=
  reducedUsingTask I h (componentDecidableEq (toBaseline I h)) E

theorem reducedWithOrderingTask_result (I : Syntax) (h : Valid I) :
    (reducedWithOrderingTask I h (ConcreteCompiler.modelOrdering I h)).result =
      ConcreteCompiler.reducedEnumeration I h := reducedUsingTask_result I h

end Cover.CompilerInitializationTasks
