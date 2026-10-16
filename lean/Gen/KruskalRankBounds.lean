import Gen.Graph
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Rank and sparse-support bounds for the general Kruskal uniqueness proof.
The source is Stegeman–Sidiropoulos (2007), equations (3.3)–(3.10).
The central permutation lemma is formalized separately. -/
noncomputable section
namespace Gen.KruskalRankBounds
open scoped BigOperators
open Module

/-- Finite-dimensional Sylvester inequality in additive form, avoiding truncated
natural-number subtraction. -/
theorem sylvester_linear {U V W : Type*}
    [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (f : V →ₗ[ℝ] W) (g : U →ₗ[ℝ] V) :
    finrank ℝ f.range + finrank ℝ g.range ≤
      finrank ℝ (f.comp g).range + finrank ℝ V := by
  let p := g.range
  have hker : finrank ℝ (f.domRestrict p).ker ≤ finrank ℝ f.ker := by
    calc
      _ = finrank ℝ (((f.domRestrict p).ker).map p.subtype) :=
        (Submodule.finrank_map_subtype_eq p _).symm
      _ ≤ _ := by
        apply Submodule.finrank_mono
        rintro v ⟨w, hw, rfl⟩
        exact hw
  have hdim := (f.domRestrict p).finrank_range_add_finrank_ker
  have hf := f.finrank_range_add_finrank_ker
  have hrange : (f.domRestrict p).range = (f.comp g).range := by
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
  rw [hrange] at hdim
  dsimp [p] at hdim hker
  omega

/-- Matrix form of Sylvester's rank inequality over real finite matrices. -/
theorem sylvester_matrix {X Z Y : Type*} [Fintype X] [Fintype Z] [Fintype Y]
    (A : Matrix X Z ℝ) (B : Matrix Z Y ℝ) :
    A.rank + B.rank ≤ (A * B).rank + Fintype.card Z := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_mul]
  simpa only [Module.finrank_pi] using sylvester_linear A.mulVecLin B.mulVecLin

#print axioms sylvester_matrix
section Columns
variable {Z X Y : Type*} [Fintype Z] [DecidableEq Z] [Fintype X] [Fintype Y]

def restrictColumns (A : X → Z → ℝ) (s : Finset Z) : Matrix X s ℝ := fun x z => A x z.val

/-- Independence of every k-subset implies independence of every smaller subset,
provided k is an actual possible column count. -/
theorem columnIndependent_mono (A : X → Z → ℝ) {k m : ℕ}
    (hA : Gen.ColumnKruskalIndependent A k) (hk : k ≤ Fintype.card Z) (hm : m ≤ k) :
    Gen.ColumnKruskalIndependent A m := by
  intro s hs
  obtain ⟨t,hst,_,ht⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ s) (hs ▸ hm) (by simpa using hk)
  have h := hA t ht
  let f : s → t := fun z => ⟨z.val, hst z.property⟩
  exact h.comp f (fun a b hab => Subtype.ext (congrArg (fun z : t => z.val) hab))

/-- Restricting to s columns retains rank at least min(|s|,k). -/
theorem restricted_rank_lower (A : X → Z → ℝ) {k : ℕ}
    (hA : Gen.ColumnKruskalIndependent A k) (hk : k ≤ Fintype.card Z) (s : Finset Z) :
    min s.card k ≤ (restrictColumns A s).rank := by
  classical
  obtain ⟨t,hts,ht⟩ := Finset.exists_subset_card_eq (min_le_left s.card k)
  have hI := columnIndependent_mono A hA hk (min_le_right s.card k) t ht
  have htr : (restrictColumns A t).rank = t.card := by
    rw [← Matrix.rank_transpose]
    convert! hI.rank_matrix using 1
    exact (Fintype.card_coe t).symm
  let f : t → s := fun z => ⟨z.val,hts z.property⟩
  calc
    min s.card k = (restrictColumns A t).rank := by rw [htr, ht]
    _ ≤ _ := Matrix.rank_submatrix_le (restrictColumns A s) id f

/-- Nonzero coordinates of the contracted third-mode coefficient vector. -/
def support (c : Z → ℝ) : Finset Z := Finset.univ.filter (fun z => c z ≠ 0)

/-- The matrix obtained by contracting one tensor mode. -/
def contraction (A : X → Z → ℝ) (B : Y → Z → ℝ) (c : Z → ℝ) : Matrix X Y ℝ :=
  fun x y => ∑ z, A x z * c z * B y z

theorem contraction_factorization (A : X → Z → ℝ) (B : Y → Z → ℝ) (c : Z → ℝ) :
    contraction A B c = restrictColumns A (support c) *
      Matrix.diagonal (fun z : support c => c z.val) * (restrictColumns B (support c)).transpose := by
  ext x y
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]
  simp only [contraction, Matrix.transpose_apply, restrictColumns]
  rw [Finset.sum_coe_sort (support c) (fun z => A x z * c z * B y z)]
  simp only [support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : c z = 0 <;> simp [h]

theorem support_card_le (c : Z → ℝ) : (support c).card ≤ Fintype.card Z :=
  Finset.card_le_univ _

/-- Contraction rank cannot exceed the number of nonzero coefficients. -/
theorem contraction_rank_upper (A : X → Z → ℝ) (B : Y → Z → ℝ) (c : Z → ℝ) :
    (contraction A B c).rank ≤ (support c).card := by
  rw [contraction_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_coe _))

/-- Sylvester lower bound on the contracted slice, with only reference k-rank
assumptions and the full support size of the contracting coefficient vector. -/
theorem contraction_rank_lower (A : X → Z → ℝ) (B : Y → Z → ℝ)
    (c : Z → ℝ) {kA kB : ℕ}
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hkA : kA ≤ Fintype.card Z) (hkB : kB ≤ Fintype.card Z) :
    min (support c).card kA + min (support c).card kB ≤
      (contraction A B c).rank + (support c).card := by
  classical
  let S := support c
  let D : Matrix S S ℝ := Matrix.diagonal (fun z => c z.val)
  have hD : IsUnit D.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun z _ => (Finset.mem_filter.mp z.property).2)
  have hSyl := sylvester_matrix (restrictColumns A S * D) (restrictColumns B S).transpose
  rw [Matrix.rank_mul_eq_left_of_isUnit_det D _ hD, Matrix.rank_transpose,
    Fintype.card_coe] at hSyl
  have hM : restrictColumns A S * D * (restrictColumns B S).transpose = contraction A B c :=
    (contraction_factorization A B c).symm
  rw [hM] at hSyl
  exact (add_le_add (restricted_rank_lower A hA hkA S)
    (restricted_rank_lower B hB hkB S)).trans hSyl

/-- The finite arithmetic step in equations (3.9)-(3.10). -/
theorem support_comparison_of_rank_bounds {R s t kA kB : ℕ}
    (hs : s ≤ R) (hkA : kA ≤ R) (hkB : kB ≤ R)
    (hlower : min s kA + min s kB ≤ t+s)
    (hbudget : t + R + 1 ≤ kA+kB) : s ≤ t := by
  omega

/-- Equality of contracted slices plus the sparse-support budget implies the
support inequality required by Kruskal's permutation lemma. -/
theorem sparse_support_comparison (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ)
    (c c' : Z → ℝ) {kA kB : ℕ}
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hkA : kA ≤ Fintype.card Z) (hkB : kB ≤ Fintype.card Z)
    (heq : contraction A B c = contraction A' B' c')
    (hbudget : (support c').card + Fintype.card Z + 1 ≤ kA+kB) :
    (support c).card ≤ (support c').card := by
  apply support_comparison_of_rank_bounds (support_card_le c) hkA hkB
  · have h := contraction_rank_lower A B c hA hB hkA hkB
    rw [heq] at h
    exact h.trans (Nat.add_le_add_right (contraction_rank_upper A' B' c') _)
  · exact hbudget

variable {T : Type*} [Fintype T]

/-- A third-mode contraction coefficient vector, in real dot-product notation. -/
def dotCoefficients (C : T → Z → ℝ) (a : T → ℝ) : Z → ℝ :=
  fun z => ∑ t, C t z * a t

/-- Raw unweighted tensor equality; positive mixture weights may be absorbed into A. -/
def TensorEqual (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : T → Z → ℝ) : Prop :=
  ∀ x y t, (∑ z, A x z * B y z * C t z) = ∑ z, A' x z * B' y z * C' t z

lemma contraction_dot_formula (A : X → Z → ℝ) (B : Y → Z → ℝ)
    (C : T → Z → ℝ) (a : T → ℝ) (x : X) (y : Y) :
    contraction A B (dotCoefficients C a) x y =
      ∑ t, a t * ∑ z, A x z * B y z * C t z := by
  simp only [contraction, dotCoefficients, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem TensorEqual.contraction_eq (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ)
    (C C' : T → Z → ℝ) (h : TensorEqual A A' B B' C C') (a : T → ℝ) :
    contraction A B (dotCoefficients C a) = contraction A' B' (dotCoefficients C' a) := by
  ext x y
  rw [contraction_dot_formula, contraction_dot_formula]
  change ∀ x y t, (∑ z, A x z * B y z * C t z) = ∑ z, A' x z * B' y z * C' t z at h
  simp_rw [h]

lemma support_zero_iff (c : Z → ℝ) : (support c).card = 0 ↔ ∀ z, c z = 0 := by
  classical
  rw [Finset.card_eq_zero]
  simp only [support, Finset.filter_eq_empty_iff, Finset.mem_univ, forall_const, not_not]

/-- Under k_A+k_B≥R+1, a zero competing contraction forces a zero reference
coefficient vector. This supplies the flattening injectivity needed before (3.4). -/
theorem zero_coefficients_of_tensor_equal
    (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : T → Z → ℝ)
    {kA kB : ℕ} (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hkA : kA ≤ Fintype.card Z) (hkB : kB ≤ Fintype.card Z)
    (hK : Fintype.card Z + 1 ≤ kA+kB) (h : TensorEqual A A' B B' C C')
    (a : T → ℝ) (ha : ∀ z, dotCoefficients C' a z = 0) :
    ∀ z, dotCoefficients C a z = 0 := by
  have hs' := (support_zero_iff (dotCoefficients C' a)).mpr ha
  have hs := sparse_support_comparison A A' B B' (dotCoefficients C a) (dotCoefficients C' a)
    hA hB hkA hkB (TensorEqual.contraction_eq A A' B B' C C' h a) (by omega)
  exact (support_zero_iff _).mp (by omega)

/-- Rank of the reference third factor cannot exceed the competing third-factor
rank, derived from tensor equality with no competitor k-rank restriction. -/
theorem reference_rank_le_competitor_rank
    (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : Matrix T Z ℝ)
    {kA kB : ℕ} (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hkA : kA ≤ Fintype.card Z) (hkB : kB ≤ Fintype.card Z)
    (hK : Fintype.card Z + 1 ≤ kA+kB) (h : TensorEqual A A' B B' C C') :
    C.rank ≤ C'.rank := by
  have hker : C'.transpose.mulVecLin.ker ≤ C.transpose.mulVecLin.ker := by
    intro a ha
    have hz : ∀ z, dotCoefficients C' a z = 0 := fun z => congrFun ha z
    have hzero := zero_coefficients_of_tensor_equal A A' B B' C C' hA hB hkA hkB hK h a hz
    exact funext hzero
  have hd := Submodule.finrank_mono hker
  have hr : C.rank + finrank ℝ C.transpose.mulVecLin.ker = Fintype.card T := by
    have hh := C.transpose.mulVecLin.finrank_range_add_finrank_ker
    change C.transpose.rank + _ = _ at hh
    simpa only [Matrix.rank_transpose, Module.finrank_pi] using hh
  have hr' : C'.rank + finrank ℝ C'.transpose.mulVecLin.ker = Fintype.card T := by
    have hh := C'.transpose.mulVecLin.finrank_range_add_finrank_ker
    change C'.transpose.rank + _ = _ at hh
    simpa only [Matrix.rank_transpose, Module.finrank_pi] using hh
  omega

/-- Complete sparse-support hypothesis for the third-factor permutation lemma,
from the original Kruskal inequality and unrestricted same-r tensor equality. -/
theorem kruskal_sparse_support
    (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : Matrix T Z ℝ)
    {kA kB kC : ℕ}
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hC : Gen.ColumnKruskalIndependent C kC)
    (hkA : kA ≤ Fintype.card Z) (hkB : kB ≤ Fintype.card Z) (hkC : kC ≤ Fintype.card Z)
    (hK : 2 * Fintype.card Z + 2 ≤ kA+kB+kC)
    (h : TensorEqual A A' B B' C C') (a : T → ℝ)
    (ha : (support (dotCoefficients C' a)).card ≤ Fintype.card Z - C'.rank + 1) :
    (support (dotCoefficients C a)).card ≤ (support (dotCoefficients C' a)).card := by
  have hAB : Fintype.card Z + 1 ≤ kA+kB := by omega
  have hr := reference_rank_le_competitor_rank A A' B B' C C' hA hB hkA hkB hAB h
  have hr' := C'.rank_le_card_width
  have hCr : kC ≤ C.rank := by
    have hh := restricted_rank_lower C hC hkC Finset.univ
    have hl : kC ≤ (restrictColumns C Finset.univ).rank := by
      simpa only [Finset.card_univ, Nat.min_eq_right hkC] using hh
    exact hl.trans (Matrix.rank_submatrix_le C id (Subtype.val : ↥(Finset.univ : Finset Z) → Z))
  apply sparse_support_comparison A A' B B' (dotCoefficients C a) (dotCoefficients C' a)
    hA hB hkA hkB (TensorEqual.contraction_eq A A' B B' C C' h a)
  omega

/-- The raw column Kruskal rank is bounded by the actual number of columns. -/
theorem columnKruskalRank_le (A : X → Z → ℝ) : Gen.columnKruskalRank A ≤ Fintype.card Z := by
  classical
  apply Finset.sup_le
  intro k hk
  have h := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  change k ≤ Fintype.card Z
  omega

/-- The finite maximum defining raw Kruskal rank is attained. -/
theorem columnKruskalRank_spec (A : X → Z → ℝ) :
    Gen.ColumnKruskalIndependent A (Gen.columnKruskalRank A) := by
  classical
  have h0 : Gen.ColumnKruskalIndependent A 0 := by
    intro s hs
    have he : s = ∅ := Finset.card_eq_zero.mp hs
    subst s
    exact linearIndependent_empty_type
  have hne : ((Finset.range (Fintype.card Z + 1)).filter (Gen.ColumnKruskalIndependent A)).Nonempty := by
    exact ⟨0, Finset.mem_filter.mpr ⟨by simp,h0⟩⟩
  obtain ⟨k,hk,heq⟩ := Finset.sup_mem_of_nonempty (f := id) hne
  unfold Gen.columnKruskalRank
  rw [← heq]
  exact (Finset.mem_filter.mp hk).2

/-- Sparse-support interface using the project's exact maximum-based Kruskal ranks. -/
theorem kruskalRank_sparse_support
    (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : Matrix T Z ℝ)
    (hK : 2 * Fintype.card Z + 2 ≤ Gen.columnKruskalRank A +
      Gen.columnKruskalRank B + Gen.columnKruskalRank C)
    (h : TensorEqual A A' B B' C C') (a : T → ℝ)
    (ha : (support (dotCoefficients C' a)).card ≤ Fintype.card Z - C'.rank + 1) :
    (support (dotCoefficients C a)).card ≤ (support (dotCoefficients C' a)).card :=
  kruskal_sparse_support A A' B B' C C'
    (columnKruskalRank_spec A) (columnKruskalRank_spec B) (columnKruskalRank_spec C)
    (columnKruskalRank_le A) (columnKruskalRank_le B) (columnKruskalRank_le C) hK h a ha

end Columns
#print axioms sparse_support_comparison
#print axioms kruskal_sparse_support
#print axioms kruskalRank_sparse_support
end Gen.KruskalRankBounds
