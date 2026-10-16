import Cover.ConstraintCompiler

open scoped BigOperators
namespace Cover.SquaredCompiler
open Cover.Compiler Gen.PrincipalMinors
variable {v : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {n : G → ℕ} {k : ℕ}

/-- Exactly the three frozen coefficient leaves, in their literal order. -/
noncomputable def coefficients (w σ R : ℝ) : Fin 3 → ℝ := ![w, σ^2, R^2]

def gram (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := 3)) (g : G) :
    Matrix (Fin (k+1)) (Fin (k+1)) (PolyExpr v 3) := fun z z' =>
  (sumExpr (E.outputs g) (fun y => .mul (X (.inr ⟨g,z,y⟩)) (X (.inr ⟨g,z',y⟩)))).sub
    (if z = z' then .scalar 1 else .rat 0)

theorem gram_eval (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := 3)) (g : G)
    (w σ R : ℝ) (x : Fin v → ℝ) :
    (Matrix.of fun z z' => (gram E X g z z').eval (coefficients w σ R) x) =
      Gen.Conditioned.gramDifference σ
        (fun y z => (X (.inr ⟨g,z,y⟩)).eval (coefficients w σ R) x) := by
  ext z z'
  simp only [gram,PolyExpr.eval_sub,eval_sumExpr,PolyExpr.eval,
    Gen.Conditioned.gramDifference,Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,Matrix.of_apply]
  split_ifs <;> simp [PolyExpr.eval,coefficients]

def gramConstraints (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := 3)) : List (PolyExpr v 3) :=
  E.groups.values.flatMap fun g => principalConstraints E.principal (gram E X g)

theorem gramConstraints_eval (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := 3)) (w σ R : ℝ) (x : Fin v → ℝ) :
    nonnegative (gramConstraints E X) (coefficients w σ R) x ↔
      ∀ g, Nonnegative (Gen.Conditioned.gramDifference σ
        (fun y z => (X (.inr ⟨g,z,y⟩)).eval (coefficients w σ R) x)) := by
  change (∀ p ∈ E.groups.values.flatMap (fun g => principalConstraints E.principal (gram E X g)), _) ↔ _
  simp only [List.forall_mem_flatMap]
  change (∀ g ∈ E.groups.values, nonnegative (principalConstraints E.principal (gram E X g)) (coefficients w σ R) x) ↔ _
  simp only [forall_enumeration,principalConstraints_eval]
  apply forall_congr'; intro g
  change Nonnegative (Matrix.of fun i j => (gram E X g i j).eval (coefficients w σ R) x) ↔ _
  rw [gram_eval]

def modelConstraints (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := 3)) : List (PolyExpr v 3) :=
  weightConstraints E (.scalar 0) X ++ kernelConstraints E X ++ gramConstraints E X

theorem modelConstraints_eval (E : Order (D := D) (n := n) (k := k))
    (u : Normalization.ReducedCoordinate D n k → PolyExpr v 3)
    (w σ R : ℝ) (x : Fin v → ℝ) :
    nonnegative (modelConstraints E (expandNormalizedExpr D n k u)) (coefficients w σ R) x ↔
      Normalization.expandNormalized D n k (fun i => (u i).eval (coefficients w σ R) x) ∈
        Gen.Conditioned.K D (fun g => Fin (n g+1)) (k+1) w σ := by
  rw [Gen.PrincipalMinors.mem_K_iff_constraints]
  have hn := Normalization.expand_normalized D n k (fun i => (u i).eval (coefficients w σ R) x)
  rw [Gen.PrincipalMinors.KConstraints]
  simp only [hn,true_and]
  rw [← eval_expandNormalizedExpr D n k u (coefficients w σ R) x]
  simp only [modelConstraints,nonnegative_append]
  rw [weightConstraints_eval,kernelConstraints_eval,gramConstraints_eval E _ w σ R x]
  simp only [evalCoordinates,and_assoc,PolyExpr.eval,coefficients,Matrix.cons_val_zero]

def farConstraints (E : Order (D := D) (n := n) (k := k))
    (X X' : CoordinateExpr D n k (v := v) (a := 3)) : List (PolyExpr v 3) :=
  E.gauges.values.map fun q => (distance E q X X').sub (.scalar 2)

theorem farConstraints_eval (E : Order (D := D) (n := n) (k := k))
    (X X' : CoordinateExpr D n k (v := v) (a := 3))
    (w σ R : ℝ) (x : Fin v → ℝ) (hR : 0 ≤ R) :
    nonnegative (farConstraints E X X') (coefficients w σ R) x ↔
      ∀ q : Gen.W D (k+1), R ≤
        ‖evalCoordinates D n k X (coefficients w σ R) x -
          q⁻¹ • evalCoordinates D n k X' (coefficients w σ R) x‖ := by
  simp only [nonnegative,farConstraints,List.forall_mem_map,PolyExpr.eval_sub,
    distance_eval,PolyExpr.eval,coefficients,Matrix.cons_val_two,
    sub_nonneg,forall_enumeration]
  apply forall_congr'; intro q
  exact sq_le_sq₀ hR (norm_nonneg _)

/-- Literal frozen compiler: w, sigma² and R² are the only named scalar leaves. -/
def constraints (E : Order (D := D) (n := n) (k := k))
    (u u' : Normalization.ReducedCoordinate D n k → PolyExpr v 3) : List (PolyExpr v 3) :=
  modelConstraints E (expandNormalizedExpr D n k u) ++
  modelConstraints E (expandNormalizedExpr D n k u') ++
  farConstraints E (expandNormalizedExpr D n k u) (expandNormalizedExpr D n k u')

theorem coverEncoding_iff (E : Order (D := D) (n := n) (k := k))
    (u u' : Normalization.ReducedCoordinate D n k → PolyExpr v 3)
    (w σ R : ℝ) (x : Fin v → ℝ) (hR : 0 ≤ R) :
    nonnegative (constraints E u u') (coefficients w σ R) x ↔
      Normalization.expandNormalized D n k (fun i => (u i).eval (coefficients w σ R) x) ∈
        Gen.Conditioned.K D (fun g => Fin (n g+1)) (k+1) w σ ∧
      Normalization.expandNormalized D n k (fun i => (u' i).eval (coefficients w σ R) x) ∈
        Gen.Conditioned.K D (fun g => Fin (n g+1)) (k+1) w σ ∧
      ∀ q : Gen.W D (k+1), R ≤
        ‖Normalization.expandNormalized D n k (fun i => (u i).eval (coefficients w σ R) x) -
          q⁻¹ • Normalization.expandNormalized D n k (fun i => (u' i).eval (coefficients w σ R) x)‖ := by
  simp only [constraints,nonnegative_append,modelConstraints_eval,
    farConstraints_eval E _ _ w σ R x hR,eval_expandNormalizedExpr,and_assoc]
end Cover.SquaredCompiler
