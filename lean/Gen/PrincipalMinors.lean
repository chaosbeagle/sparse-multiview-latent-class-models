import Gen.Conditioned
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open scoped BigOperators Classical
open Matrix Polynomial
noncomputable section
namespace Gen.PrincipalMinors

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- All principal minors, including the empty minor, with non-strict inequalities. -/
def Nonnegative (A : Matrix n n ℝ) : Prop :=
  ∀ S : Finset n, 0 ≤ (A.submatrix (Subtype.val : S → n) (Subtype.val : S → n)).det

lemma nonnegative_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) : Nonnegative A := by
  intro S
  exact (hA.submatrix (Subtype.val : S → n)).det_nonneg

/-- No positive real can be a root of det(I+X A) when all principal minors are nonnegative.
This uses the exact principal-minor coefficient identity, including zero boundary minors. -/
lemma det_one_add_smul_pos {A : Matrix n n ℝ} (hm : Nonnegative A) (t : ℝ) (ht : 0 ≤ t) :
    0 < (1 + t • A).det := by
  let p : Polynomial ℝ := (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det
  have hc : ∀ k, 0 ≤ p.coeff k := by
    intro k
    rw [show p = (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det from rfl,
      Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    exact Finset.sum_nonneg fun S _ => hm S
  have hevaldet (u : ℝ) : p.eval u = (1 + u • A).det := by
    change (Polynomial.evalRingHom u) (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    change Polynomial.eval u ((if i = j then 1 else 0) + Polynomial.X * Polynomial.C (A i j)) =
      (if i = j then 1 else 0) + u * A i j
    split_ifs <;> simp <;> ring
  have hzero : p.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero,hevaldet]
    simp
  have heval : 1 ≤ p.eval t := by
    rw [Polynomial.eval_eq_sum_range]
    have he := Finset.single_le_sum
      (s := Finset.range (p.natDegree+1)) (f := fun k => p.coeff k * t^k)
      (fun k _ => mul_nonneg (hc k) (pow_nonneg ht k))
      (show 0 ∈ Finset.range (p.natDegree+1) by simp)
    simpa [hzero] using he
  rw [hevaldet] at heval
  linarith

/-- Exact closed-boundary principal-minor criterion for every finite real symmetric matrix. -/
theorem posSemidef_iff_principalMinors (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A.PosSemidef ↔ Nonnegative A := by
  constructor
  · exact nonnegative_of_posSemidef
  · intro hm
    apply hA.posSemidef_iff_eigenvalues_nonneg.mpr
    intro i
    by_contra hi
    have hi' : hA.eigenvalues i < 0 := lt_of_not_ge hi
    have hne : hA.eigenvalues i ≠ 0 := ne_of_lt hi'
    let t : ℝ := -(hA.eigenvalues i)⁻¹
    have ht : 0 < t := neg_pos.mpr (inv_lt_zero.mpr hi')
    have hd := det_one_add_smul_pos hm t ht.le
    have hu : IsUnit (1 + t • A) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (ne_of_gt hd))
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
    let v : n → ℝ := (hA.eigenvectorBasis i).ofLp
    have hv : A *ᵥ v = (hA.eigenvalues i) • v := hA.mulVec_eigenvectorBasis i
    have hz : (1 + t • A) *ᵥ v = 0 := by
      rw [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,hv]
      ext j
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,t]
      field_simp
      ring
    have hvzero : v = 0 := hinj (hz.trans (Matrix.mulVec_zero _).symm)
    apply hA.eigenvectorBasis.toBasis.ne_zero i
    ext j
    exact congrFun hvzero j

/-- Gram margins are exactly the finite, non-strict principal-minor inequalities. -/
theorem gramMargin_iff_principalMinors {Z O : Type*} [Fintype Z] [Fintype O] [DecidableEq Z]
    (σ : ℝ) (L : O → Z → ℝ) :
    Conditioned.GramMargin σ L ↔ Nonnegative (Conditioned.gramDifference σ L) := by
  rw [Conditioned.gramMargin_iff_posSemidef]
  exact posSemidef_iff_principalMinors _ (Conditioned.gramDifference_isHermitian σ L)

section ConditionedSet
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- Literal finite polynomial constraints for the full closed RATE conditioned set.
All principal subsets, not only leading minors, are included. -/
def KConstraints (w₀ σ : ℝ) (x : Geometry.Ambient D Y r) : Prop :=
  Geometry.Normalized D Y r x ∧
    (∀ c z, w₀ ≤ x (.inl (c,z))) ∧
    (∀ g z y, 0 ≤ x (.inr ⟨g,z,y⟩)) ∧
    ∀ g, Nonnegative (Conditioned.gramDifference σ (fun y z => x (.inr ⟨g,z,y⟩)))

/-- Exact full-real K encoding, preserving boundary zeros and every original coordinate. -/
theorem mem_K_iff_constraints (w₀ σ : ℝ) (x : Geometry.Ambient D Y r) :
    x ∈ Conditioned.K D Y r w₀ σ ↔ KConstraints D Y r w₀ σ x := by
  simp only [Conditioned.K,Set.mem_setOf_eq,KConstraints,gramMargin_iff_principalMinors]

end ConditionedSet
end Gen.PrincipalMinors
