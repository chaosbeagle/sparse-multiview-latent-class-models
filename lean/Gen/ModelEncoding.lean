import Gen.PrincipalMinors
import Gen.QEEncoding

open scoped BigOperators Classical
open Matrix Gen.PrincipalMinors
noncomputable section
namespace Gen.ModelEncoding
variable {n : Type*} [Fintype n] [DecidableEq n]
section Syntax
open Gen.QEEncoding
variable {v : ℕ}

def exprProduct : List (PolynomialExpr v) → PolynomialExpr v
  | [] => .rational 1
  | p :: ps => .mul p (exprProduct ps)

@[simp] theorem eval_exprProduct (ps : List (PolynomialExpr v)) (x : Fin v → ℝ) :
    (exprProduct ps).eval x = (ps.map (fun p => p.eval x)).prod := by
  induction ps with
  | nil => simp [exprProduct,PolynomialExpr.eval]
  | cons p ps ih => simp [exprProduct,PolynomialExpr.eval,ih]

/-- Finite Leibniz determinant syntax. It never tests equality or signs of real inputs. -/
def determinantExpr (A : Matrix n n (PolynomialExpr v)) : PolynomialExpr v :=
  PolynomialExpr.sum ((Finset.univ : Finset (Equiv.Perm n)).toList.map fun π =>
    PolynomialExpr.mul (.rational ((Equiv.Perm.sign π : ℤ) : ℚ))
      (exprProduct ((Finset.univ : Finset n).toList.map fun i => A (π i) i)))

@[simp] theorem eval_determinantExpr (A : Matrix n n (PolynomialExpr v)) (x : Fin v → ℝ) :
    (determinantExpr A).eval x = (Matrix.of fun i j => (A i j).eval x).det := by
  simp [determinantExpr,PolynomialExpr.eval,Matrix.det_apply',List.map_map,Function.comp_def]

/-- Syntactically conjoin every principal-minor nonnegativity test. -/
def principalMinorsFormula (A : Matrix n n (PolynomialExpr v)) : Formula v :=
  Formula.all ((Finset.univ : Finset (Finset n)).toList.map fun (S : Finset n) =>
    Formula.le (.rational 0) (determinantExpr (A.submatrix (Subtype.val : S → n) (Subtype.val : S → n))))

theorem principalMinorsFormula_sound_complete
    (A : Matrix n n (PolynomialExpr v)) (x : Fin v → ℝ) :
    (principalMinorsFormula A).Holds x ↔ Nonnegative (fun i j => (A i j).eval x) := by
  simp [principalMinorsFormula,Formula.holds_all,Formula.Holds,PolynomialExpr.eval,
    Nonnegative,Matrix.submatrix]

theorem principalMinorsFormula_iff_posSemidef
    (A : Matrix n n (PolynomialExpr v)) (x : Fin v → ℝ)
    (hA : (Matrix.of fun i j => (A i j).eval x).IsHermitian) :
    (principalMinorsFormula A).Holds x ↔ (Matrix.of fun i j => (A i j).eval x).PosSemidef := by
  rw [principalMinorsFormula_sound_complete]
  exact (posSemidef_iff_principalMinors _ hA).symm

def finiteSumExpr {I : Type*} [Fintype I] (p : I → PolynomialExpr v) : PolynomialExpr v :=
  PolynomialExpr.sum (Finset.univ.toList.map p)
@[simp] theorem eval_finiteSumExpr {I : Type*} [Fintype I]
    (p : I → PolynomialExpr v) (x : Fin v → ℝ) :
    (finiteSumExpr p).eval x = ∑ i, (p i).eval x := by
  simp [finiteSumExpr,List.map_map,Function.comp_def]

def finiteProductExpr {I : Type*} [Fintype I] (p : I → PolynomialExpr v) : PolynomialExpr v :=
  exprProduct (Finset.univ.toList.map p)
@[simp] theorem eval_finiteProductExpr {I : Type*} [Fintype I]
    (p : I → PolynomialExpr v) (x : Fin v → ℝ) :
    (finiteProductExpr p).eval x = ∏ i, (p i).eval x := by
  simp [finiteProductExpr,List.map_map,Function.comp_def]

def finiteAll {I : Type*} [Fintype I] (p : I → Formula v) : Formula v :=
  Formula.all (Finset.univ.toList.map p)
@[simp] theorem holds_finiteAll {I : Type*} [Fintype I]
    (p : I → Formula v) (x : Fin v → ℝ) :
    (finiteAll p).Holds x ↔ ∀ i, (p i).Holds x := by
  simp [finiteAll,Formula.holds_all]

/-- Polynomial Gram matrix with an arbitrary symbolic margin expression. -/
def gramExpr {Z O : Type*} [Fintype Z] [Fintype O] [DecidableEq Z]
    (σ : PolynomialExpr v) (L : O → Z → PolynomialExpr v) : Matrix Z Z (PolynomialExpr v) :=
  fun z z' => (finiteSumExpr (fun y => PolynomialExpr.mul (L y z) (L y z'))).sub
    (if z = z' then σ.square else .rational 0)

@[simp] theorem eval_gramExpr {Z O : Type*} [Fintype Z] [Fintype O] [DecidableEq Z]
    (σ : PolynomialExpr v) (L : O → Z → PolynomialExpr v) (x : Fin v → ℝ) :
    (Matrix.of fun z z' => (gramExpr σ L z z').eval x) =
      Conditioned.gramDifference (σ.eval x) (fun y z => (L y z).eval x) := by
  ext z z'
  simp only [gramExpr,PolynomialExpr.eval_sub,eval_finiteSumExpr,PolynomialExpr.eval,
    Conditioned.gramDifference,Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,Matrix.of_apply]
  split_ifs <;> simp [PolynomialExpr.eval]

section Model
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- A polynomial expression for every original, non-redundant model coordinate. -/
abbrev CoordinateExpressions := Geometry.Coordinate D Y r → PolynomialExpr v

def evalCoordinates (X : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) : Geometry.Ambient D Y r :=
  WithLp.toLp 2 (fun i => (X i).eval a)

@[simp] theorem evalCoordinates_apply (X : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) (i) :
    evalCoordinates D Y r X a i = (X i).eval a := rfl

/-- Literal finite K formula: normalization, weight margin, kernel nonnegativity,
and every principal minor of each Gram-difference matrix. -/
def KFormula (w₀ σ : PolynomialExpr v) (X : CoordinateExpressions D Y r (v := v)) : Formula v :=
  .conjunction
    (.conjunction
      (finiteAll (fun c : D.Component => Formula.equal
        (finiteSumExpr (fun z : Fin r => X (.inl (c,z)))) (.rational 1)))
      (finiteAll (fun g : G => finiteAll (fun z : Fin r => Formula.equal
        (finiteSumExpr (fun y : Y g => X (.inr ⟨g,z,y⟩))) (.rational 1)))))
    (.conjunction
      (finiteAll (fun c : D.Component => finiteAll (fun z : Fin r => Formula.le w₀ (X (.inl (c,z))))))
      (.conjunction
        (finiteAll (fun g : G => finiteAll (fun z : Fin r => finiteAll (fun y : Y g =>
          Formula.le (.rational 0) (X (.inr ⟨g,z,y⟩))))))
        (finiteAll (fun g : G => principalMinorsFormula (gramExpr σ (fun y z => X (.inr ⟨g,z,y⟩)))))))

/-- Soundness and completeness hold for every real assignment, including boundary points. -/
theorem KFormula_sound_complete (w₀ σ : PolynomialExpr v)
    (X : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (KFormula D Y r w₀ σ X).Holds a ↔
      evalCoordinates D Y r X a ∈ Conditioned.K D Y r (w₀.eval a) (σ.eval a) := by
  rw [PrincipalMinors.mem_K_iff_constraints]
  simp only [KFormula,Formula.Holds,holds_finiteAll,eval_finiteSumExpr,PolynomialExpr.eval,
    principalMinorsFormula_sound_complete,PrincipalMinors.KConstraints,
    Geometry.Normalized,evalCoordinates_apply]
  have he (g : G) :
      Nonnegative (fun i j => (gramExpr σ (fun y z => X (.inr ⟨g,z,y⟩)) i j).eval a) ↔
        Nonnegative (Conditioned.gramDifference (σ.eval a) (fun y z => (X (.inr ⟨g,z,y⟩)).eval a)) := by
    rw [show (fun i j => (gramExpr σ (fun y z => X (.inr ⟨g,z,y⟩)) i j).eval a) =
      Conditioned.gramDifference (σ.eval a) (fun y z => (X (.inr ⟨g,z,y⟩)).eval a) from
        eval_gramExpr σ (fun y z => X (.inr ⟨g,z,y⟩)) a]
  simp only [he,Rat.cast_one,Rat.cast_zero]

/-- Direct variables for all original coordinates, possibly in a larger variable block
that also includes independent margin/coefficient variables. -/
def coordinateVariables (ι : Geometry.Coordinate D Y r ↪ Fin v) : CoordinateExpressions D Y r (v := v) :=
  fun i => .var (ι i)

/-- Every real parameter array is represented; no algebraic or grid restriction is imposed. -/
theorem evalCoordinateVariables_surjective (ι : Geometry.Coordinate D Y r ↪ Fin v) :
    Function.Surjective (evalCoordinates D Y r (coordinateVariables D Y r ι)) := by
  intro θ
  let a : Fin v → ℝ := fun j => if hj : ∃ i, ι i = j then θ hj.choose else 0
  refine ⟨a,?_⟩
  ext i
  change a (ι i) = θ i
  have hi : ∃ j, ι j = ι i := ⟨i,rfl⟩
  simp only [a,dif_pos hi]
  exact congrArg θ (ι.injective hi.choose_spec)

/-- The literal quartic mixture observation polynomial, on every actual edge cell. -/
def observationExpr (X : CoordinateExpressions D Y r (v := v))
    (e : D.Edge) (x : D.Outcome Y e) : PolynomialExpr v :=
  finiteSumExpr (fun z : Fin r => PolynomialExpr.mul (X (.inl (D.component e,z)))
    (finiteProductExpr (fun g : D.GroupAt e => X (.inr ⟨g.val,z,x g⟩))))

@[simp] theorem eval_observationExpr (X : CoordinateExpressions D Y r (v := v))
    (a : Fin v → ℝ) (e : D.Edge) (x : D.Outcome Y e) :
    (observationExpr D Y r X e x).eval a =
      Geometry.observation D Y r (evalCoordinates D Y r X a) ⟨e,x⟩ := by
  simp only [observationExpr,eval_finiteSumExpr,PolynomialExpr.eval,eval_finiteProductExpr]
  rfl

/-- H is the sum of squared differences of all actual edge-cell observation polynomials. -/
def observationLossExpr (X X' : CoordinateExpressions D Y r (v := v)) : PolynomialExpr v :=
  finiteSumExpr (fun ex : (e : D.Edge) × D.Outcome Y e =>
    ((observationExpr D Y r X ex.1 ex.2).sub (observationExpr D Y r X' ex.1 ex.2)).square)

theorem eval_observationLossExpr (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (observationLossExpr D Y r X X').eval a =
      ‖Geometry.observation D Y r (evalCoordinates D Y r X a) -
        Geometry.observation D Y r (evalCoordinates D Y r X' a)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [observationLossExpr,eval_finiteSumExpr,PolynomialExpr.eval_square,
    PolynomialExpr.eval_sub,eval_observationExpr,PiLp.sub_apply]

lemma inverse_action_apply (q : Gen.W D r) (x : Geometry.Ambient D Y r) (i) :
    (q⁻¹ • x) i = x (Geometry.coordinatePerm D Y r q i) := by
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;> rfl

/-- Complete entrywise squared distance after the paper's right pullback permutation. -/
def permutationDistanceExpr (q : Gen.W D r) (X X' : CoordinateExpressions D Y r (v := v)) : PolynomialExpr v :=
  finiteSumExpr (fun i : Geometry.Coordinate D Y r =>
    ((X i).sub (X' (Geometry.coordinatePerm D Y r q i))).square)

theorem eval_permutationDistanceExpr (q : Gen.W D r)
    (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (permutationDistanceExpr D Y r q X X').eval a =
      ‖evalCoordinates D Y r X a - q⁻¹ • evalCoordinates D Y r X' a‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [permutationDistanceExpr,eval_finiteSumExpr,PolynomialExpr.eval_square,
    PolynomialExpr.eval_sub,PiLp.sub_apply,inverse_action_apply,evalCoordinates_apply]

/-- Every member of W is tested; no best-alignment heuristic or partial list is used. -/
def allPermutationFarFormula (R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) : Formula v :=
  finiteAll (fun q : Gen.W D r => Formula.le R.square (permutationDistanceExpr D Y r q X X'))

theorem allPermutationFarFormula_sound_complete (R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (allPermutationFarFormula D Y r R X X').Holds a ↔
      ∀ q : Gen.W D r, (R.eval a)^2 ≤
        ‖evalCoordinates D Y r X a - q⁻¹ • evalCoordinates D Y r X' a‖^2 := by
  simp only [allPermutationFarFormula,holds_finiteAll,Formula.Holds,
    PolynomialExpr.eval_square,eval_permutationDistanceExpr]

/-- The squared far-pair inequalities preserve the weak radius threshold exactly. -/
theorem allPermutationFarFormula_iff_norm (R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) (hR : 0 ≤ R.eval a) :
    (allPermutationFarFormula D Y r R X X').Holds a ↔
      ∀ q : Gen.W D r, R.eval a ≤
        ‖evalCoordinates D Y r X a - q⁻¹ • evalCoordinates D Y r X' a‖ := by
  rw [allPermutationFarFormula_sound_complete]
  apply forall_congr'
  intro q
  exact sq_le_sq₀ hR (norm_nonneg _)

/-- The full real far-pair feasibility formula Q_R, with symbolic margins and radius. -/
def farPairFormula (w₀ σ R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) : Formula v :=
  .conjunction (KFormula D Y r w₀ σ X)
    (.conjunction (KFormula D Y r w₀ σ X') (allPermutationFarFormula D Y r R X X'))

theorem farPairFormula_sound_complete (w₀ σ R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (farPairFormula D Y r w₀ σ R X X').Holds a ↔
      evalCoordinates D Y r X a ∈ Conditioned.K D Y r (w₀.eval a) (σ.eval a) ∧
      evalCoordinates D Y r X' a ∈ Conditioned.K D Y r (w₀.eval a) (σ.eval a) ∧
      ∀ q : Gen.W D r, (R.eval a)^2 ≤
        ‖evalCoordinates D Y r X a - q⁻¹ • evalCoordinates D Y r X' a‖^2 := by
  simp only [farPairFormula,Formula.Holds,KFormula_sound_complete,
    allPermutationFarFormula_sound_complete]

end Model
end Syntax
end Gen.ModelEncoding
end

namespace Gen.ModelEncoding.Ordered
open Gen.QEEncoding
open Gen.PrincipalMinors
open Matrix

/-- Supplied literal ordering, with exact finite coverage and no duplicated terms. -/
structure Enumeration (I : Type*) where
  values : List I
  nodup : values.Nodup
  complete : ∀ i, i ∈ values

namespace Enumeration
variable {I : Type*} [Fintype I] (E : Enumeration I)
lemma sum_map {M : Type*} [AddCommMonoid M] (f : I → M) :
    (E.values.map f).sum = ∑ i, f i := by
  classical
  rw [← List.sum_toFinset f E.nodup]
  have he : E.values.toFinset = Finset.univ := by ext i; simp [E.complete i]
  rw [he]
lemma prod_map {M : Type*} [CommMonoid M] (f : I → M) :
    (E.values.map f).prod = ∏ i, f i := by
  classical
  rw [← List.prod_toFinset f E.nodup]
  have he : E.values.toFinset = Finset.univ := by ext i; simp [E.complete i]
  rw [he]
end Enumeration

variable {v : ℕ}
def product : List (PolynomialExpr v) → PolynomialExpr v
  | [] => .rational 1
  | p :: ps => .mul p (product ps)
@[simp] theorem eval_product (ps : List (PolynomialExpr v)) (a : Fin v → ℝ) :
    (product ps).eval a = (ps.map (fun p => p.eval a)).prod := by
  induction ps with
  | nil => simp [product,PolynomialExpr.eval]
  | cons p ps ih => simp [product,PolynomialExpr.eval,ih]

def sumExpr {I : Type*} (E : Enumeration I) (p : I → PolynomialExpr v) : PolynomialExpr v :=
  PolynomialExpr.sum (E.values.map p)
def prodExpr {I : Type*} (E : Enumeration I) (p : I → PolynomialExpr v) : PolynomialExpr v :=
  product (E.values.map p)
def all {I : Type*} (E : Enumeration I) (p : I → Formula v) : Formula v :=
  Formula.all (E.values.map p)
@[simp] theorem eval_sumExpr {I : Type*} [Fintype I]
    (E : Enumeration I) (p : I → PolynomialExpr v) (a : Fin v → ℝ) :
    (sumExpr E p).eval a = ∑ i, (p i).eval a := by
  simpa [sumExpr,List.map_map,Function.comp_def] using E.sum_map (fun i => (p i).eval a)
@[simp] theorem eval_prodExpr {I : Type*} [Fintype I]
    (E : Enumeration I) (p : I → PolynomialExpr v) (a : Fin v → ℝ) :
    (prodExpr E p).eval a = ∏ i, (p i).eval a := by
  simpa [prodExpr,List.map_map,Function.comp_def] using E.prod_map (fun i => (p i).eval a)
@[simp] theorem holds_all {I : Type*} (E : Enumeration I) (p : I → Formula v) (a : Fin v → ℝ) :
    (all E p).Holds a ↔ ∀ i, (p i).Holds a := by
  simp only [all,Formula.holds_all,List.forall_mem_map]
  exact ⟨fun h i => h i (E.complete i),fun h i _ => h i⟩

variable {n : Type*} [Fintype n] [DecidableEq n]
/-- All ordering choices needed by the finite principal-minor expansion are explicit input. -/
structure PrincipalOrdering (n : Type*) [DecidableEq n] where
  subsets : Enumeration (Finset n)
  indices : ∀ S : Finset n, Enumeration S
  permutations : ∀ S : Finset n, Enumeration (Equiv.Perm S)

def determinant (E : Enumeration n) (P : Enumeration (Equiv.Perm n))
    (A : Matrix n n (PolynomialExpr v)) : PolynomialExpr v :=
  sumExpr P (fun π => PolynomialExpr.mul (.rational ((Equiv.Perm.sign π : ℤ) : ℚ))
    (prodExpr E (fun i => A (π i) i)))

@[simp] theorem eval_determinant (E : Enumeration n) (P : Enumeration (Equiv.Perm n))
    (A : Matrix n n (PolynomialExpr v)) (a : Fin v → ℝ) :
    (determinant E P A).eval a = (Matrix.of fun i j => (A i j).eval a).det := by
  simp [determinant,PolynomialExpr.eval,Matrix.det_apply']

def principalFormula (E : PrincipalOrdering n) (A : Matrix n n (PolynomialExpr v)) : Formula v :=
  all E.subsets (fun S : Finset n => Formula.le (.rational 0)
    (determinant (E.indices S) (E.permutations S)
      (A.submatrix (Subtype.val : S → n) (Subtype.val : S → n))))

theorem principalFormula_sound_complete (E : PrincipalOrdering n)
    (A : Matrix n n (PolynomialExpr v)) (a : Fin v → ℝ) :
    (principalFormula E A).Holds a ↔ Nonnegative (fun i j => (A i j).eval a) := by
  simp [principalFormula,Formula.Holds,PolynomialExpr.eval,Nonnegative,Matrix.submatrix]

def gram {Z O : Type*} [DecidableEq Z] (EY : Enumeration O)
    (σ : PolynomialExpr v) (L : O → Z → PolynomialExpr v) : Matrix Z Z (PolynomialExpr v) :=
  fun z z' => (sumExpr EY (fun y => PolynomialExpr.mul (L y z) (L y z'))).sub
    (if z = z' then σ.square else .rational 0)

@[simp] theorem eval_gram {Z O : Type*} [Fintype Z] [Fintype O] [DecidableEq Z]
    (EY : Enumeration O) (σ : PolynomialExpr v) (L : O → Z → PolynomialExpr v) (a : Fin v → ℝ) :
    (Matrix.of fun z z' => (gram EY σ L z z').eval a) =
      Conditioned.gramDifference (σ.eval a) (fun y z => (L y z).eval a) := by
  ext z z'
  simp only [gram,PolynomialExpr.eval_sub,eval_sumExpr,PolynomialExpr.eval,
    Conditioned.gramDifference,Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,Matrix.of_apply]
  split_ifs <;> simp [PolynomialExpr.eval]

section Model
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- Literal finite model orderings. They may be supplied from the frozen encoded input;
none is chosen by the compiler, and every supplied list is checked complete. -/
structure ModelOrdering where
  components : Enumeration D.Component
  groups : Enumeration G
  latent : Enumeration (Fin r)
  outputs : ∀ g, Enumeration (Y g)
  edgeGroups : ∀ e : D.Edge, Enumeration (D.GroupAt e)
  cells : Enumeration ((e : D.Edge) × D.Outcome Y e)
  coordinates : Enumeration (Geometry.Coordinate D Y r)
  gauges : Enumeration (Gen.W D r)
  principal : PrincipalOrdering (Fin r)
  coordinatePullback : Gen.W D r → Geometry.Coordinate D Y r → Geometry.Coordinate D Y r
  coordinatePullback_correct : ∀ q i, coordinatePullback q i = Geometry.coordinatePerm D Y r q i

variable {D Y r}
/-- Computable K syntax using only the supplied lists, symbolic expressions and rational constants. -/
def K (E : ModelOrdering D Y r) (w₀ σ : PolynomialExpr v)
    (X : CoordinateExpressions D Y r (v := v)) : Formula v :=
  .conjunction
    (.conjunction
      (all E.components (fun c => Formula.equal
        (sumExpr E.latent (fun z => X (.inl (c,z)))) (.rational 1)))
      (all E.groups (fun g => all E.latent (fun z => Formula.equal
        (sumExpr (E.outputs g) (fun y => X (.inr ⟨g,z,y⟩))) (.rational 1)))))
    (.conjunction
      (all E.components (fun c => all E.latent (fun z => Formula.le w₀ (X (.inl (c,z))))))
      (.conjunction
        (all E.groups (fun g => all E.latent (fun z => all (E.outputs g) (fun y =>
          Formula.le (.rational 0) (X (.inr ⟨g,z,y⟩))))))
        (all E.groups (fun g => principalFormula E.principal (gram (E.outputs g) σ
          (fun y z => X (.inr ⟨g,z,y⟩)))))))

theorem K_sound_complete (E : ModelOrdering D Y r) (w₀ σ : PolynomialExpr v)
    (X : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (K E w₀ σ X).Holds a ↔
      evalCoordinates D Y r X a ∈ Conditioned.K D Y r (w₀.eval a) (σ.eval a) := by
  rw [PrincipalMinors.mem_K_iff_constraints]
  simp only [K,Formula.Holds,holds_all,eval_sumExpr,PolynomialExpr.eval,
    principalFormula_sound_complete,PrincipalMinors.KConstraints,
    Geometry.Normalized,evalCoordinates_apply]
  have he (g : G) :
      Nonnegative (fun i j => (gram (E.outputs g) σ (fun y z => X (.inr ⟨g,z,y⟩)) i j).eval a) ↔
        Nonnegative (Conditioned.gramDifference (σ.eval a) (fun y z => (X (.inr ⟨g,z,y⟩)).eval a)) := by
    rw [show (fun i j => (gram (E.outputs g) σ (fun y z => X (.inr ⟨g,z,y⟩)) i j).eval a) =
      Conditioned.gramDifference (σ.eval a) (fun y z => (X (.inr ⟨g,z,y⟩)).eval a) from
        eval_gram (E.outputs g) σ (fun y z => X (.inr ⟨g,z,y⟩)) a]
  simp only [he,Rat.cast_one,Rat.cast_zero]

def observation (E : ModelOrdering D Y r) (X : CoordinateExpressions D Y r (v := v))
    (e : D.Edge) (x : D.Outcome Y e) : PolynomialExpr v :=
  sumExpr E.latent (fun z => PolynomialExpr.mul (X (.inl (D.component e,z)))
    (prodExpr (E.edgeGroups e) (fun g => X (.inr ⟨g.val,z,x g⟩))))

@[simp] theorem eval_observation (E : ModelOrdering D Y r) (X : CoordinateExpressions D Y r (v := v))
    (a : Fin v → ℝ) (e : D.Edge) (x : D.Outcome Y e) :
    (observation E X e x).eval a =
      Geometry.observation D Y r (evalCoordinates D Y r X a) ⟨e,x⟩ := by
  simp only [observation,eval_sumExpr,PolynomialExpr.eval,eval_prodExpr]
  rfl

def H (E : ModelOrdering D Y r) (X X' : CoordinateExpressions D Y r (v := v)) : PolynomialExpr v :=
  sumExpr E.cells (fun ex => ((observation E X ex.1 ex.2).sub (observation E X' ex.1 ex.2)).square)

theorem H_eval (E : ModelOrdering D Y r) (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (H E X X').eval a =
      ‖Geometry.observation D Y r (evalCoordinates D Y r X a) -
        Geometry.observation D Y r (evalCoordinates D Y r X' a)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [H,eval_sumExpr,PolynomialExpr.eval_square,PolynomialExpr.eval_sub,
    eval_observation,PiLp.sub_apply]

def distance (E : ModelOrdering D Y r) (q : Gen.W D r)
    (X X' : CoordinateExpressions D Y r (v := v)) : PolynomialExpr v :=
  sumExpr E.coordinates (fun i => ((X i).sub (X' (E.coordinatePullback q i))).square)

theorem distance_eval (E : ModelOrdering D Y r) (q : Gen.W D r)
    (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (distance E q X X').eval a =
      ‖evalCoordinates D Y r X a - q⁻¹ • evalCoordinates D Y r X' a‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [distance,eval_sumExpr,PolynomialExpr.eval_square,PolynomialExpr.eval_sub,
    PiLp.sub_apply,inverse_action_apply,evalCoordinates_apply,E.coordinatePullback_correct]

def far (E : ModelOrdering D Y r) (R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) : Formula v :=
  all E.gauges (fun q => Formula.le R.square (distance E q X X'))

theorem far_sound_complete (E : ModelOrdering D Y r) (R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (far E R X X').Holds a ↔ ∀ q : Gen.W D r, (R.eval a)^2 ≤
      ‖evalCoordinates D Y r X a - q⁻¹ • evalCoordinates D Y r X' a‖^2 := by
  simp only [far,holds_all,Formula.Holds,PolynomialExpr.eval_square,distance_eval]

theorem far_iff_norm (E : ModelOrdering D Y r) (R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) (hR : 0 ≤ R.eval a) :
    (far E R X X').Holds a ↔ ∀ q : Gen.W D r, R.eval a ≤
      ‖evalCoordinates D Y r X a - q⁻¹ • evalCoordinates D Y r X' a‖ := by
  rw [far_sound_complete]
  apply forall_congr'
  intro q
  exact sq_le_sq₀ hR (norm_nonneg _)

def Q (E : ModelOrdering D Y r) (w₀ σ R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) : Formula v :=
  .conjunction (K E w₀ σ X) (.conjunction (K E w₀ σ X') (far E R X X'))

theorem Q_sound_complete (E : ModelOrdering D Y r) (w₀ σ R : PolynomialExpr v)
    (X X' : CoordinateExpressions D Y r (v := v)) (a : Fin v → ℝ) :
    (Q E w₀ σ R X X').Holds a ↔
      evalCoordinates D Y r X a ∈ Conditioned.K D Y r (w₀.eval a) (σ.eval a) ∧
      evalCoordinates D Y r X' a ∈ Conditioned.K D Y r (w₀.eval a) (σ.eval a) ∧
      ∀ q : Gen.W D r, (R.eval a)^2 ≤
        ‖evalCoordinates D Y r X a - q⁻¹ • evalCoordinates D Y r X' a‖^2 := by
  simp only [Q,Formula.Holds,K_sound_complete,far_sound_complete]

end Model
end Gen.ModelEncoding.Ordered
