import Cover.CompilerInitializationTasks
import Cover.BaselineRepresentation

set_option maxHeartbeats 2400000
namespace Cover.CompilerInitializationTasks
open Cover.FinTask Cover.FiniteEnumeration Cover.FiniteDesign Gen.ModelEncoding.Ordered Cover.CompilerEnumerationTasks

/-- Only erased edge-subtype proofs change in this transport. inputEdgesTask's
runtime traverses the raw list; it never constructs the baseline design. -/
def inputEdgesForTask (I : Syntax) (h : Valid I) (D : Ext.TripleDesign (Fin I.groups))
    (hD : D=toBaseline I h) : FinTask (Enumeration D.Edge) :=
  hD.symm ▸ inputEdgesTask I h

@[simp] theorem inputEdgesForTask_at_base (I : Syntax) (h : Valid I) :
    inputEdgesForTask I h (toBaseline I h) rfl = inputEdgesTask I h := rfl


@[simp] theorem modelOrderingForTask_at_base (I : Syntax) (h : Valid I)
    (edges : Enumeration (toBaseline I h).Edge) (eq : DecidableEq (toBaseline I h).Component) :
    modelOrderingForTask I (toBaseline I h) edges eq = modelOrderingWithEdgesTask I h edges eq := by
  unfold modelOrderingWithEdgesTask
  rfl

def initializationForTask (I : Syntax) (h : Valid I) (D : Ext.TripleDesign (Fin I.groups))
    (hD : D=toBaseline I h) :
    FinTask (DecidableEq D.Component × ModelOrdering D (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) :=
  .step fun _ => do
    let edges ← inputEdgesForTask I h D hD
    let componentEq ← componentDecidableEqTask D edges
    let ordering ← modelOrderingForTask I D edges componentEq
    .done (componentEq,ordering)

@[simp] theorem initializationForTask_at_base (I : Syntax) (h : Valid I) :
    initializationForTask I h (toBaseline I h) rfl = initializationTask I h := by
  simp only [initializationForTask,initializationTask,inputEdgesForTask_at_base,modelOrderingForTask_at_base]

/-- This transport changes only erased dependent types. reducedUsingTask's runtime
uses the supplied equality/ordering and raw scalar sizes; it does not rebuild D. -/
def reducedForTask (I : Syntax) (h : Valid I) (D : Ext.TripleDesign (Fin I.groups))
    (hD : D=toBaseline I h) (eq : DecidableEq D.Component)
    (E : ModelOrdering D (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) :
    FinTask (Enumeration (Normalization.ReducedCoordinate D I.outputPred I.rankPred)) := by
  cases hD
  exact reducedUsingTask I h eq E

@[simp] theorem reducedForTask_at_base (I : Syntax) (h : Valid I)
    (eq : DecidableEq (toBaseline I h).Component)
    (E : ModelOrdering (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1)) :
    reducedForTask I h (toBaseline I h) rfl eq E = reducedUsingTask I h eq E := rfl

end Cover.CompilerInitializationTasks
