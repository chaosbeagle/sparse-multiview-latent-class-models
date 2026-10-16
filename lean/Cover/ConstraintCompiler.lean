import Cover.CompilerPrimitives

open scoped BigOperators
namespace Cover.Compiler
open Gen.ModelEncoding.Ordered Gen.PrincipalMinors
variable {v a : ℕ}

@[simp] theorem forall_enumeration {I : Type*} (E : Enumeration I) (P : I → Prop) :
    (∀ i ∈ E.values, P i) ↔ ∀ i, P i :=
  ⟨fun h i => h i (E.complete i),fun h i _ => h i⟩

def nonnegative (ps : List (PolyExpr v a)) (cs : Fin a → ℝ) (x : Fin v → ℝ) : Prop :=
  ∀ p ∈ ps, 0 ≤ p.eval cs x

@[simp] theorem nonnegative_append (ps qs : List (PolyExpr v a)) (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    nonnegative (ps ++ qs) cs x ↔ nonnegative ps cs x ∧ nonnegative qs cs x := by
  simp only [nonnegative,List.mem_append]; aesop

variable {I : Type*} [Fintype I] [DecidableEq I]
def determinant (E : Enumeration I) (P : Enumeration (Equiv.Perm I))
    (A : Matrix I I (PolyExpr v a)) : PolyExpr v a :=
  PolyExpr.fromLegacy (Gen.ModelEncoding.Ordered.determinant E P (fun i j => (A i j).toLegacy))
@[simp] theorem determinant_eval (E : Enumeration I) (P : Enumeration (Equiv.Perm I))
    (A : Matrix I I (PolyExpr v a)) (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    (determinant E P A).eval cs x = (Matrix.of fun i j => (A i j).eval cs x).det := by
  simp [determinant,Gen.ModelEncoding.Ordered.eval_determinant]

/-- Empty principal subsets are deliberately omitted, and all nonempty subsets retained. -/
def principalConstraints (E : PrincipalOrdering I) (A : Matrix I I (PolyExpr v a)) :
    List (PolyExpr v a) :=
  (E.subsets.values.filter (fun S => S ≠ ∅)).map (fun S =>
    determinant (E.indices S) (E.permutations S) (A.submatrix Subtype.val Subtype.val))

theorem principalConstraints_eval (E : PrincipalOrdering I) (A : Matrix I I (PolyExpr v a))
    (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    nonnegative (principalConstraints E A) cs x ↔ Nonnegative (fun i j => (A i j).eval cs x) := by
  simp only [nonnegative,principalConstraints,List.forall_mem_map,List.mem_filter,
    decide_eq_true_eq,and_imp,determinant_eval,Matrix.submatrix,Matrix.of_apply]
  constructor
  · intro h S
    by_cases hS : S = ∅
    · subst S; simp
    · exact h S (E.subsets.complete S) hS
  · intro h S _ _; exact h S

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {n : G → ℕ} {k : ℕ}
abbrev Order := ModelOrdering D (fun g => Fin (n g+1)) (k+1)

def gram (E : Order (D := D) (n := n) (k := k)) (σ : PolyExpr v a)
    (X : CoordinateExpr D n k (v := v) (a := a)) (g : G) :
    Matrix (Fin (k+1)) (Fin (k+1)) (PolyExpr v a) := fun z z' =>
  PolyExpr.fromLegacy (Gen.ModelEncoding.Ordered.gram (E.outputs g) σ.toLegacy
    (fun y z => (X (.inr ⟨g,z,y⟩)).toLegacy) z z')
@[simp] theorem gram_eval (E : Order (D := D) (n := n) (k := k)) (σ : PolyExpr v a)
    (X : CoordinateExpr D n k (v := v) (a := a)) (g : G)
    (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    (Matrix.of fun i j => (gram E σ X g i j).eval cs x) =
      Gen.Conditioned.gramDifference (σ.eval cs x) (fun y z => (X (.inr ⟨g,z,y⟩)).eval cs x) := by
  simp only [gram,PolyExpr.fromLegacy_eval]
  rw [Gen.ModelEncoding.Ordered.eval_gram]
  simp

def weightConstraints (E : Order (D := D) (n := n) (k := k)) (w : PolyExpr v a)
    (X : CoordinateExpr D n k (v := v) (a := a)) : List (PolyExpr v a) :=
  E.components.values.flatMap fun c => E.latent.values.map fun z => (X (.inl (c,z))).sub w

def kernelConstraints (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := a)) : List (PolyExpr v a) :=
  E.groups.values.flatMap fun g => E.latent.values.flatMap fun z =>
    (E.outputs g).values.map fun y => X (.inr ⟨g,z,y⟩)

def gramConstraints (E : Order (D := D) (n := n) (k := k)) (σ : PolyExpr v a)
    (X : CoordinateExpr D n k (v := v) (a := a)) : List (PolyExpr v a) :=
  E.groups.values.flatMap fun g => principalConstraints E.principal (gram E σ X g)

def modelConstraints (E : Order (D := D) (n := n) (k := k)) (w σ : PolyExpr v a)
    (X : CoordinateExpr D n k (v := v) (a := a)) : List (PolyExpr v a) :=
  weightConstraints E w X ++ kernelConstraints E X ++ gramConstraints E σ X

theorem weightConstraints_eval (E : Order (D := D) (n := n) (k := k)) (w : PolyExpr v a)
    (X : CoordinateExpr D n k (v := v) (a := a)) (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    nonnegative (weightConstraints E w X) cs x ↔
      ∀ c z, w.eval cs x ≤ (X (.inl (c,z))).eval cs x := by
  simp only [nonnegative,weightConstraints,List.forall_mem_flatMap,List.forall_mem_map,
    forall_enumeration,PolyExpr.eval_sub,sub_nonneg]

theorem kernelConstraints_eval (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := a)) (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    nonnegative (kernelConstraints E X) cs x ↔
      ∀ g z y, 0 ≤ (X (.inr ⟨g,z,y⟩)).eval cs x := by
  simp only [nonnegative,kernelConstraints,List.forall_mem_flatMap,List.forall_mem_map,
    forall_enumeration]

theorem gramConstraints_eval (E : Order (D := D) (n := n) (k := k)) (σ : PolyExpr v a)
    (X : CoordinateExpr D n k (v := v) (a := a)) (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    nonnegative (gramConstraints E σ X) cs x ↔
      ∀ g, Nonnegative (Gen.Conditioned.gramDifference (σ.eval cs x)
        (fun y z => (X (.inr ⟨g,z,y⟩)).eval cs x)) := by
  change (∀ p ∈ E.groups.values.flatMap (fun g => principalConstraints E.principal (gram E σ X g)), _) ↔ _
  simp only [List.forall_mem_flatMap]
  change (∀ g ∈ E.groups.values, nonnegative (principalConstraints E.principal (gram E σ X g)) cs x) ↔ _
  simp only [forall_enumeration,principalConstraints_eval]
  apply forall_congr'
  intro g
  change Nonnegative (Matrix.of fun i j => (gram E σ X g i j).eval cs x) ↔ _
  rw [gram_eval]

theorem modelConstraints_eval (E : Order (D := D) (n := n) (k := k)) (w σ : PolyExpr v a)
    (u : Normalization.ReducedCoordinate D n k → PolyExpr v a)
    (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    nonnegative (modelConstraints E w σ (expandNormalizedExpr D n k u)) cs x ↔
      Normalization.expandNormalized D n k (fun i => (u i).eval cs x) ∈
        Gen.Conditioned.K D (fun g => Fin (n g+1)) (k+1) (w.eval cs x) (σ.eval cs x) := by
  rw [Gen.PrincipalMinors.mem_K_iff_constraints]
  have hn := Normalization.expand_normalized D n k (fun i => (u i).eval cs x)
  rw [Gen.PrincipalMinors.KConstraints]
  simp only [hn,true_and]
  rw [← eval_expandNormalizedExpr D n k u cs x]
  simp only [modelConstraints,nonnegative_append,weightConstraints_eval,
    kernelConstraints_eval,gramConstraints_eval,evalCoordinates,and_assoc]

def farConstraints (E : Order (D := D) (n := n) (k := k)) (R : PolyExpr v a)
    (X X' : CoordinateExpr D n k (v := v) (a := a)) : List (PolyExpr v a) :=
  E.gauges.values.map fun q => (distance E q X X').sub R.square

theorem farConstraints_eval (E : Order (D := D) (n := n) (k := k)) (R : PolyExpr v a)
    (X X' : CoordinateExpr D n k (v := v) (a := a)) (cs : Fin a → ℝ) (x : Fin v → ℝ)
    (hR : 0 ≤ R.eval cs x) :
    nonnegative (farConstraints E R X X') cs x ↔
      ∀ q : Gen.W D (k+1), R.eval cs x ≤
        ‖evalCoordinates D n k X cs x - q⁻¹ • evalCoordinates D n k X' cs x‖ := by
  simp only [nonnegative,farConstraints,List.forall_mem_map,PolyExpr.eval_sub,
    PolyExpr.eval_square,distance_eval,sub_nonneg,forall_enumeration]
  apply forall_congr'
  intro q
  exact sq_le_sq₀ hR (norm_nonneg _)

/-- All constraints are regenerated from exact lists; no real-valued decisions occur. -/
def coverConstraints (E : Order (D := D) (n := n) (k := k)) (w σ R : PolyExpr v a)
    (u u' : Normalization.ReducedCoordinate D n k → PolyExpr v a) : List (PolyExpr v a) :=
  modelConstraints E w σ (expandNormalizedExpr D n k u) ++
  modelConstraints E w σ (expandNormalizedExpr D n k u') ++
  farConstraints E R (expandNormalizedExpr D n k u) (expandNormalizedExpr D n k u')

/-- Exact encoding on every real assignment, without rational-point or interior restrictions. -/
theorem coverEncoding_iff (E : Order (D := D) (n := n) (k := k)) (w σ R : PolyExpr v a)
    (u u' : Normalization.ReducedCoordinate D n k → PolyExpr v a)
    (cs : Fin a → ℝ) (x : Fin v → ℝ) (hR : 0 ≤ R.eval cs x) :
    nonnegative (coverConstraints E w σ R u u') cs x ↔
      Normalization.expandNormalized D n k (fun i => (u i).eval cs x) ∈
        Gen.Conditioned.K D (fun g => Fin (n g+1)) (k+1) (w.eval cs x) (σ.eval cs x) ∧
      Normalization.expandNormalized D n k (fun i => (u' i).eval cs x) ∈
        Gen.Conditioned.K D (fun g => Fin (n g+1)) (k+1) (w.eval cs x) (σ.eval cs x) ∧
      ∀ q : Gen.W D (k+1), R.eval cs x ≤
        ‖Normalization.expandNormalized D n k (fun i => (u i).eval cs x) -
          q⁻¹ • Normalization.expandNormalized D n k (fun i => (u' i).eval cs x)‖ := by
  simp only [coverConstraints,nonnegative_append,modelConstraints_eval,
    farConstraints_eval E R _ _ cs x hR,eval_expandNormalizedExpr,and_assoc]

end Cover.Compiler
