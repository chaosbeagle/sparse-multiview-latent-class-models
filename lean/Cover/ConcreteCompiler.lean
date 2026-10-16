import Cover.FiniteDesign
import Cover.SquaredCompiler

set_option maxHeartbeats 800000
open scoped BigOperators
namespace Cover.ConcreteCompiler
open Gen.ModelEncoding.Ordered
open Cover.FiniteEnumeration Cover.FiniteDesign Cover.Compiler

/-- Actual design-to-ordering compiler, with every list generated from input data. -/
def modelOrdering (I : Syntax) (h : Valid I) :
    ModelOrdering (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) := by
  let D := toBaseline I h
  let edges : Enumeration D.Edge := inputEdges I h
  let cs := FiniteDesign.components D edges
  letI := FiniteDesign.componentDecidableEq D
  letI : Fintype D.Component := Fintype.ofList cs.values cs.complete
  let gs := finEnumeration I.groups
  let zs := finEnumeration (I.rankPred+1)
  let ys := fun g => finEnumeration (I.outputPred g+1)
  exact {
    components := cs
    groups := gs
    latent := zs
    outputs := ys
    edgeGroups := fun e => sorted
    cells := sigma edges (fun e => pi (sorted : Enumeration (D.GroupAt e)) (fun g => ys g.val))
    coordinates := sum (prod cs zs) (sigma gs (fun g => prod zs (ys g)))
    gauges := pi cs (fun _ => permutations zs)
    principal := principal (I.rankPred+1)
    coordinatePullback := fun q i => match i with
      | .inl (c,z) => .inl (c,q c z)
      | .inr ⟨g,z,y⟩ => .inr ⟨g,q (FiniteDesign.groupComponent D edges g) z,y⟩
    coordinatePullback_correct := by
      intro q i
      rcases i with ⟨c,z⟩ | ⟨g,z,y⟩
      · rfl
      · simp only [FiniteDesign.groupComponent_eq,Gen.Geometry.coordinatePerm,Equiv.coe_fn_mk,D] }

/-- Stored-coordinate enumeration uses the same component and group order as the compiler. -/
def reducedEnumeration (I : Syntax) (h : Valid I) :
    Enumeration (Normalization.ReducedCoordinate (toBaseline I h) I.outputPred I.rankPred) := by
  let D := toBaseline I h
  let E := modelOrdering I h
  letI := FiniteDesign.componentDecidableEq D
  exact sum (prod E.components (finEnumeration I.rankPred))
    (sigma E.groups (fun g => prod E.latent (finEnumeration (I.outputPred g))))

def dimension (I : Syntax) (h : Valid I) : ℕ := (reducedEnumeration I h).values.length

def reducedEquiv (I : Syntax) (h : Valid I) :
    Fin (dimension I h) ≃ Normalization.ReducedCoordinate (toBaseline I h) I.outputPred I.rankPred := by
  letI := FiniteDesign.componentDecidableEq (toBaseline I h)
  exact indexEquiv (reducedEnumeration I h)

def leftVariables (I : Syntax) (h : Valid I) :
    Normalization.ReducedCoordinate (toBaseline I h) I.outputPred I.rankPred →
      PolyExpr (dimension I h + dimension I h) 3 := fun i =>
  .var (Fin.castAdd (dimension I h) ((reducedEquiv I h).symm i))

def rightVariables (I : Syntax) (h : Valid I) :
    Normalization.ReducedCoordinate (toBaseline I h) I.outputPred I.rankPred →
      PolyExpr (dimension I h + dimension I h) 3 := fun i =>
  .var (Fin.natAdd (dimension I h) ((reducedEquiv I h).symm i))

def constraints (I : Syntax) (h : Valid I) : List (PolyExpr (dimension I h + dimension I h) 3) :=
  SquaredCompiler.constraints (modelOrdering I h) (leftVariables I h) (rightVariables I h)

def objective (I : Syntax) (h : Valid I) : PolyExpr (dimension I h + dimension I h) 3 :=
  Compiler.objective (modelOrdering I h)
    (expandNormalizedExpr _ _ _ (leftVariables I h))
    (expandNormalizedExpr _ _ _ (rightVariables I h))

noncomputable def expandLeft (I : Syntax) (h : Valid I)
    (x : Fin (dimension I h + dimension I h) → ℝ) :
    Normalization.Full (toBaseline I h) I.outputPred I.rankPred :=
  Normalization.expandNormalized _ _ _ (fun i => x (Fin.castAdd (dimension I h) ((reducedEquiv I h).symm i)))
noncomputable def expandRight (I : Syntax) (h : Valid I)
    (x : Fin (dimension I h + dimension I h) → ℝ) :
    Normalization.Full (toBaseline I h) I.outputPred I.rankPred :=
  Normalization.expandNormalized _ _ _ (fun i => x (Fin.natAdd (dimension I h) ((reducedEquiv I h).symm i)))

def projectPair (I : Syntax) (h : Valid I)
    (θ η : Normalization.Full (toBaseline I h) I.outputPred I.rankPred) :
    Fin (dimension I h + dimension I h) → ℝ :=
  Fin.addCases
    (fun j => Normalization.projectNormalized _ _ _ θ (reducedEquiv I h j))
    (fun j => Normalization.projectNormalized _ _ _ η (reducedEquiv I h j))

@[simp] theorem expandLeft_project (I : Syntax) (h : Valid I)
    (θ η : Normalization.Full (toBaseline I h) I.outputPred I.rankPred)
    (hθ : Gen.Geometry.Normalized (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) θ) :
    expandLeft I h (projectPair I h θ η) = θ := by
  simp only [expandLeft,projectPair,Fin.addCases_left,Equiv.apply_symm_apply]
  exact Normalization.expand_project _ _ _ θ hθ
@[simp] theorem expandRight_project (I : Syntax) (h : Valid I)
    (θ η : Normalization.Full (toBaseline I h) I.outputPred I.rankPred)
    (hη : Gen.Geometry.Normalized (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) η) :
    expandRight I h (projectPair I h θ η) = η := by
  simp only [expandRight,projectPair,Fin.addCases_right,Equiv.apply_symm_apply]
  exact Normalization.expand_project _ _ _ η hη

@[simp] theorem project_expand (I : Syntax) (h : Valid I)
    (x : Fin (dimension I h + dimension I h) → ℝ) :
    projectPair I h (expandLeft I h x) (expandRight I h x) = x := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [projectPair,expandLeft,expandRight,Fin.addCases_left,Fin.addCases_right,
      Normalization.project_expand,Equiv.symm_apply_apply]

theorem dimension_exact (I : Syntax) (h : Valid I) :
    dimension I h = Fintype.card (toBaseline I h).Component * I.rankPred +
      (I.rankPred+1) * ∑ g, I.outputPred g := by
  rw [dimension,FiniteEnumeration.length_eq_card,Normalization.reduced_dimension]

theorem pairDimension_pos (I : Syntax) (h : Valid I) : 0 < dimension I h + dimension I h := by
  have hp := Normalization.pair_dimension_pos (toBaseline I h) I.outputPred I.rankPred h.1
  rw [← FiniteEnumeration.length_eq_card (reducedEnumeration I h)] at hp
  simpa [dimension,two_mul] using hp

/-- All generated nonnegative constraints iff the expanded pair is an actual full-real far pair. -/
theorem coverEncoding_iff (I : Syntax) (h : Valid I) (w σ R : ℝ) (hR : 0 ≤ R)
    (x : Fin (dimension I h + dimension I h) → ℝ) :
    nonnegative (constraints I h) (SquaredCompiler.coefficients w σ R) x ↔
      expandLeft I h x ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ ∧
      expandRight I h x ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ ∧
      ∀ q : Gen.W (toBaseline I h) (I.rankPred+1), R ≤ ‖expandLeft I h x - q⁻¹ • expandRight I h x‖ := by
  exact SquaredCompiler.coverEncoding_iff (modelOrdering I h) (leftVariables I h) (rightVariables I h) w σ R x hR

theorem coverObjective_eval (I : Syntax) (h : Valid I) (cs : Fin 3 → ℝ)
    (x : Fin (dimension I h + dimension I h) → ℝ) :
    (objective I h).eval cs x =
      ‖Gen.Geometry.observation (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) (expandLeft I h x) -
        Gen.Geometry.observation (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) (expandRight I h x)‖^2 := by
  simp only [objective,Compiler.coverObjective_eval,eval_expandNormalizedExpr]
  rfl

/-- Every arbitrary real K pair projects into the exact closed pair cube. -/
theorem projectPair_mem_unitBox (I : Syntax) (h : Valid I) {w σ : ℝ} (hw : 0 ≤ w)
    (θ η : Normalization.Full (toBaseline I h) I.outputPred I.rankPred)
    (hθ : θ ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ)
    (hη : η ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ) :
    ∀ j, projectPair I h θ η j ∈ Set.Icc (0:ℝ) 1 := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [projectPair,Fin.addCases_left,Fin.addCases_right] using Normalization.project_K_mem_unitBox _ _ _ hw θ hθ (reducedEquiv I h i)
  · simpa only [projectPair,Fin.addCases_left,Fin.addCases_right] using Normalization.project_K_mem_unitBox _ _ _ hw η hη (reducedEquiv I h i)

/-- Full-real completeness includes unique representation, all boundaries, and unit-cube membership. -/
theorem every_farPair_unique (I : Syntax) (h : Valid I) {w σ R : ℝ} (hw : 0 ≤ w) (hR : 0 ≤ R)
    (θ η : Normalization.Full (toBaseline I h) I.outputPred I.rankPred)
    (hθ : θ ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ)
    (hη : η ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ)
    (hfar : ∀ q : Gen.W (toBaseline I h) (I.rankPred+1), R ≤ ‖θ - q⁻¹ • η‖) :
    ∃! x, (∀ j, x j ∈ Set.Icc (0:ℝ) 1) ∧
      nonnegative (constraints I h) (SquaredCompiler.coefficients w σ R) x ∧
      expandLeft I h x = θ ∧ expandRight I h x = η := by
  refine ⟨projectPair I h θ η, ?_, ?_⟩
  · refine ⟨projectPair_mem_unitBox I h hw θ η hθ hη, ?_,
      expandLeft_project I h θ η hθ.1, expandRight_project I h θ η hη.1⟩
    rw [coverEncoding_iff I h w σ R hR]
    simpa only [expandLeft_project I h θ η hθ.1,expandRight_project I h θ η hη.1] using ⟨hθ,hη,hfar⟩
  · intro x hx
    rw [← hx.2.2.1, ← hx.2.2.2]
    exact (project_expand I h x).symm
end Cover.ConcreteCompiler
