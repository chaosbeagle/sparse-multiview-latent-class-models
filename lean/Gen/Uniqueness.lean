import Gen.Graph
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-! Elementary local uniqueness for full-column-rank stochastic three-way models.
No rank assumption is imposed on the competing normalized decomposition. -/
namespace Gen.Uniqueness
open scoped BigOperators

variable {Z X Y T : Type*} [Fintype Z] [DecidableEq Z]
  [Fintype X] [Fintype Y] [Fintype T]

/-- A left dual of the column family. -/
def LeftDual (A : X → Z → ℝ) (L : Z → X → ℝ) : Prop :=
  ∀ i j, ∑ x, L i x * A x j = if i = j then 1 else 0

/-- Column normalization; nonnegativity is unnecessary for the algebraic lemma. -/
def Normalized (A : X → Z → ℝ) : Prop := ∀ j, ∑ x, A x j = 1

/-- A rank-one diagonal array has singleton support if both vectors are nonzero. -/
theorem rankOneDiagonal_support (u v : Z → ℝ)
    (hu : ∃ i, u i ≠ 0) (hv : ∃ i, v i ≠ 0)
    (hdiag : ∀ i k, i ≠ k → u i * v k = 0) :
    ∃ i, u i ≠ 0 ∧ v i ≠ 0 ∧
      (∀ k, k ≠ i → u k = 0) ∧ (∀ k, k ≠ i → v k = 0) := by
  obtain ⟨i, hi⟩ := hu
  obtain ⟨j, hj⟩ := hv
  have hij : i = j := by
    by_contra h
    exact (mul_ne_zero hi hj) (hdiag i j h)
  subst j
  refine ⟨i, hi, hj, ?_, ?_⟩
  · intro k hk
    exact (mul_eq_zero.mp (hdiag k i hk)).resolve_right hj
  · intro k hk
    exact (mul_eq_zero.mp (hdiag i k (Ne.symm hk))).resolve_left hi

/-- If both factors also sum to one, they are the same coordinate vector. -/
theorem rankOneDiagonal_normalized (u v : Z → ℝ)
    (hu : ∑ i, u i = 1) (hv : ∑ i, v i = 1)
    (hdiag : ∀ i k, i ≠ k → u i * v k = 0) :
    ∃ i, (∀ k, u k = if k = i then 1 else 0) ∧
      (∀ k, v k = if k = i then 1 else 0) := by
  have hu0 : ∃ i, u i ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hu
  have hv0 : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hv
  obtain ⟨i, hi, hj, huk, hvk⟩ := rankOneDiagonal_support u v hu0 hv0 hdiag
  have hui : u i = 1 := by
    rw [← hu]
    exact (Finset.sum_eq_single i (by intro b hb hbi; exact huk b hbi)
      (by simp)).symm
  have hvi : v i = 1 := by
    rw [← hv]
    exact (Finset.sum_eq_single i (by intro b hb hbi; exact hvk b hbi)
      (by simp)).symm
  refine ⟨i, ?_, ?_⟩
  · intro k
    by_cases h : k = i
    · subst k; simp [hui]
    · simp [h, huk k h]
  · intro k
    by_cases h : k = i
    · subst k; simp [hvi]
    · simp [h, hvk k h]

/-- Correct a left dual so it also preserves the normalization functional. -/
theorem exists_normalized_dual [Nonempty Z] (A : X → Z → ℝ)
    (hA : Normalized A) (L : Z → X → ℝ) (hL : LeftDual A L) :
    ∃ L' : Z → X → ℝ, LeftDual A L' ∧ ∀ x, ∑ i, L' i x = 1 := by
  classical
  change ∀ i j, ∑ x, L i x * A x j = if i = j then 1 else 0 at hL
  let z : Z := Classical.choice inferInstance
  let L' : Z → X → ℝ := fun i x => L i x + if i = z then 1 - ∑ k, L k x else 0
  refine ⟨L', ?_, ?_⟩
  · intro i j
    have hs : ∑ x, (1 - ∑ k, L k x) * A x j = 0 := by
      simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp [hL, hA j]
    dsimp [L']
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [hL]
    by_cases h : i = z <;> simp [h, hs]
  · intro x
    simp [L', Finset.sum_add_distrib]

/-- Algebraic three-way observation array. -/
def tensor (w : Z → ℝ) (A : X → Z → ℝ) (B : Y → Z → ℝ)
    (C : T → Z → ℝ) (x : X) (y : Y) (t : T) : ℝ :=
  ∑ j, w j * A x j * B y j * C t j

/-- Matrix contraction of a column family. -/
def contract (L : Z → X → ℝ) (A : X → Z → ℝ) : Z → Z → ℝ :=
  fun i j => ∑ x, L i x * A x j

lemma contract_normalized (L : Z → X → ℝ) (A : X → Z → ℝ)
    (hL : ∀ x, ∑ i, L i x = 1) (hA : Normalized A) :
    Normalized (contract L A) := by
  intro j
  simp only [contract]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hL, one_mul]
  exact hA j

lemma contract_tensor_first (L : Z → X → ℝ) (w : Z → ℝ)
    (A : X → Z → ℝ) (B : Y → Z → ℝ) (C : T → Z → ℝ) (i : Z) (y : Y) (t : T) :
    ∑ x, L i x * tensor w A B C x y t = tensor w (contract L A) B C i y t := by
  simp only [tensor, contract, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma contract_tensor_second (L : Z → Y → ℝ) (w : Z → ℝ)
    (A : X → Z → ℝ) (B : Y → Z → ℝ) (C : T → Z → ℝ) (x : X) (i : Z) (t : T) :
    ∑ y, L i y * tensor w A B C x y t = tensor w A (contract L B) C x i t := by
  simp only [tensor, contract, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  ring

lemma contract_tensor_third (L : Z → T → ℝ) (w : Z → ℝ)
    (A : X → Z → ℝ) (B : Y → Z → ℝ) (C : T → Z → ℝ) (x : X) (y : Y) (i : Z) :
    ∑ t, L i t * tensor w A B C x y t = tensor w A B (contract L C) x y i := by
  simp only [tensor, contract, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Pair marginal, with no probability assumptions hidden in its definition. -/
def pair (w : Z → ℝ) (A : X → Z → ℝ) (C : T → Z → ℝ) (x : X) (t : T) : ℝ :=
  ∑ j, w j * A x j * C t j

lemma tensor_marginal_second (w : Z → ℝ) (A : X → Z → ℝ)
    (B : Y → Z → ℝ) (C : T → Z → ℝ) (hB : Normalized B) (x : X) (t : T) :
    ∑ y, tensor w A B C x y t = pair w A C x t := by
  simp only [tensor, pair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    ∑ y, w j * A x j * B y j * C t j =
        w j * A x j * C t j * ∑ y, B y j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := by rw [hB]; ring

lemma contract_pair_first (L : Z → X → ℝ) (w : Z → ℝ)
    (A : X → Z → ℝ) (C : T → Z → ℝ) (i : Z) (t : T) :
    ∑ x, L i x * pair w A C x t = pair w (contract L A) C i t := by
  simp only [pair, contract, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma contract_pair_second (L : Z → T → ℝ) (w : Z → ℝ)
    (A : X → Z → ℝ) (C : T → Z → ℝ) (x : X) (i : Z) :
    ∑ t, L i t * pair w A C x t = pair w A (contract L C) x i := by
  simp only [pair, contract, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Equality of a full-rank pair marginal forces a left dual for an unrestricted
same-size competing second factor. This uses square one-sided-inverse algebra,
not an assumption on the competitor's rank. -/
theorem competitor_leftDual_of_pair
    (w w' : Z → ℝ) (A A' : X → Z → ℝ) (C C' : T → Z → ℝ)
    (LA : Z → X → ℝ) (LC : Z → T → ℝ)
    (hw : ∀ i, w i ≠ 0) (hLA : LeftDual A LA) (hLC : LeftDual C LC)
    (heq : ∀ x t, pair w A C x t = pair w' A' C' x t) :
    ∃ LC', LeftDual C' LC' := by
  classical
  let U : Matrix Z Z ℝ := contract LA A'
  let W : Matrix Z Z ℝ := contract LC C'
  let S : Matrix Z Z ℝ := fun i j => (w i)⁻¹ * w' j * U i j
  have hpair : ∀ i k, pair w' U W i k = if i = k then w i else 0 := by
    intro i k
    have h := congrArg (fun F : X → T → ℝ => ∑ t, LC k t * ∑ x, LA i x * F x t)
      (funext fun x => funext fun t => heq x t)
    simp_rw [contract_pair_first, contract_pair_second] at h
    rw [← h]
    change ∀ i j, ∑ x, LA i x * A x j = if i = j then 1 else 0 at hLA
    change ∀ i j, ∑ t, LC i t * C t j = if i = j then 1 else 0 at hLC
    simp [pair, contract, hLA, hLC]
    split_ifs with h <;> simp_all
  have hSW : S * W.transpose = 1 := by
    ext i k
    change ∑ j, ((w i)⁻¹ * w' j * U i j) * W k j = _
    calc
      _ = (w i)⁻¹ * pair w' U W i k := by
        simp only [pair, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hpair]; by_cases h : i = k <;> simp [h, Matrix.one_apply, hw]
  have hWS : W.transpose * S = 1 := mul_eq_one_comm.mp hSW
  have hSW' : S.transpose * W = 1 := by
    simpa using congrArg Matrix.transpose hWS
  refine ⟨S.transpose * (show Matrix Z T ℝ from LC), ?_⟩
  intro i j
  have hmat : (S.transpose * (show Matrix Z T ℝ from LC)) * (show Matrix T Z ℝ from C') = (1 : Matrix Z Z ℝ) := by
    rw [Matrix.mul_assoc]
    exact hSW'
  exact congrFun (congrFun hmat i) j

lemma tensor_marginal_third (w : Z → ℝ) (A : X → Z → ℝ)
    (B : Y → Z → ℝ) (C : T → Z → ℝ) (hC : Normalized C) (x : X) (y : Y) :
    ∑ t, tensor w A B C x y t = pair w A B x y := by
  simp only [tensor, pair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, hC, mul_one]

lemma tensor_marginal_first (w : Z → ℝ) (A : X → Z → ℝ)
    (B : Y → Z → ℝ) (C : T → Z → ℝ) (hA : Normalized A) (y : Y) (t : T) :
    ∑ x, tensor w A B C x y t = pair w B C y t := by
  simp only [tensor, pair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    ∑ x, w j * A x j * B y j * C t j =
        w j * B y j * C t j * ∑ x, A x j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by rw [hA]; ring

lemma tensor_two_duals (w : Z → ℝ) (A : X → Z → ℝ)
    (B : Y → Z → ℝ) (C : T → Z → ℝ)
    (LA : Z → X → ℝ) (LB : Z → Y → ℝ)
    (hLA : LeftDual A LA) (hLB : LeftDual B LB) (i k : Z) (t : T) :
    tensor w (contract LA A) (contract LB B) C i k t =
      if i = k then w i * C t i else 0 := by
  change ∀ i j, ∑ x, LA i x * A x j = if i = j then 1 else 0 at hLA
  change ∀ i j, ∑ y, LB i y * B y j = if i = j then 1 else 0 at hLB
  simp [tensor, contract, hLA, hLB]
  split_ifs with h <;> simp_all

lemma recover_factor_of_pair
    (w w' : Z → ℝ) (A A' : X → Z → ℝ) (C C' : T → Z → ℝ)
    (LC : Z → T → ℝ) (hLC : LeftDual C LC) (hw : ∀ j, w j ≠ 0)
    (q : Equiv.Perm Z) (hw' : ∀ j, w' j = w (q j))
    (hC' : ∀ t j, C' t j = C t (q j))
    (heq : ∀ x t, pair w A C x t = pair w' A' C' x t) :
    ∀ x j, A' x j = A x (q j) := by
  intro x j
  have h := congrArg (fun f : T → ℝ => ∑ t, LC (q j) t * f t)
    (funext fun t => heq x t)
  simp_rw [contract_pair_second] at h
  have hLC' : ∀ i k, contract LC C' i k = if i = q k then 1 else 0 := by
    intro i k
    simp only [contract, hC']
    exact hLC i (q k)
  change ∀ i j, ∑ t, LC i t * C t j = if i = j then 1 else 0 at hLC
  simp only [pair] at h
  simp_rw [hLC'] at h
  simp [contract, hLC, q.injective.eq_iff, hw'] at h
  exact (h.resolve_right (hw (q j))).symm

/-- Full-column-rank local uniqueness, stated first using explicit reference duals.
The competitor is arbitrary apart from normalization and nonzero weights. -/
theorem fullRank_unique_of_duals [Nonempty Z]
    (w w' : Z → ℝ) (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ)
    (C C' : T → Z → ℝ)
    (hA : Normalized A) (hA' : Normalized A')
    (hB : Normalized B) (hB' : Normalized B')
    (hC : Normalized C) (hC' : Normalized C')
    (hw : ∀ j, w j ≠ 0) (hw' : ∀ j, w' j ≠ 0)
    (LA : Z → X → ℝ) (LB : Z → Y → ℝ) (LC : Z → T → ℝ)
    (hLA : LeftDual A LA) (hLB : LeftDual B LB) (hLC : LeftDual C LC)
    (heq : ∀ x y t, tensor w A B C x y t = tensor w' A' B' C' x y t) :
    ∃ q : Equiv.Perm Z, (∀ j, w' j = w (q j)) ∧
      (∀ x j, A' x j = A x (q j)) ∧
      (∀ y j, B' y j = B y (q j)) ∧ (∀ t j, C' t j = C t (q j)) := by
  classical
  obtain ⟨LA, hLA, hnLA⟩ := exists_normalized_dual A hA LA hLA
  obtain ⟨LB, hLB, hnLB⟩ := exists_normalized_dual B hB LB hLB
  have hac : ∀ x t, pair w A C x t = pair w' A' C' x t := by
    intro x t
    have h := congrArg (fun f : Y → ℝ => ∑ y, f y) (funext fun y => heq x y t)
    simpa only [tensor_marginal_second _ _ _ _ hB,
      tensor_marginal_second _ _ _ _ hB'] using h
  obtain ⟨LC', hLC'⟩ := competitor_leftDual_of_pair w w' A A' C C' LA LC hw hLA hLC hac
  let U := contract LA A'
  let V := contract LB B'
  have hUn : Normalized U := contract_normalized LA A' hnLA hA'
  have hVn : Normalized V := contract_normalized LB B' hnLB hB'
  have hdiag : ∀ i k t, tensor w' U V C' i k t =
      if i = k then w i * C t i else 0 := by
    intro i k t
    have h := congrArg (fun f : X → Y → ℝ => ∑ y, LB k y * ∑ x, LA i x * f x y)
      (funext fun x => funext fun y => heq x y t)
    simp_rw [contract_tensor_first, contract_tensor_second] at h
    rw [← h]
    exact tensor_two_duals w A B C LA LB hLA hLB i k t
  have hoff : ∀ j i k, i ≠ k → U i j * V k j = 0 := by
    intro j i k hik
    have h := congrArg (fun f : T → ℝ => ∑ t, LC' j t * f t)
      (funext fun t => hdiag i k t)
    rw [contract_tensor_third] at h
    change ∀ i j, ∑ t, LC' i t * C' t j = if i = j then 1 else 0 at hLC'
    simp [tensor, contract, hLC', hik] at h
    rcases h with (h | h) | h
    · exact (hw' j h).elim
    · simp [h]
    · simp [h]
  choose pi hU hV using fun j => rankOneDiagonal_normalized (fun i => U i j)
    (fun i => V i j) (hUn j) (hVn j) (hoff j)
  have hpi : Function.Surjective pi := by
    intro i
    by_contra hn
    push Not at hn
    have hz : ∀ t, w i * C t i = 0 := by
      intro t
      have h := hdiag i i t
      have hzero : tensor w' U V C' i i t = 0 := by
        simp only [tensor, hU]
        simp [fun j => Ne.symm (hn j)]
      simpa [hzero] using h.symm
    have hs := congrArg (fun f : T → ℝ => ∑ t, f t) (funext hz)
    simpa [← Finset.mul_sum, hC i, hw i] using hs
  let q : Equiv.Perm Z := Equiv.ofBijective pi ⟨Finite.injective_iff_surjective.mpr hpi, hpi⟩
  have hscale : ∀ j t, w' j * C' t j = w (q j) * C t (q j) := by
    intro j t
    have h := hdiag (q j) (q j) t
    have hp : Function.Injective pi := q.injective
    simpa [tensor, hU, hV, q, hp.eq_iff] using h
  have hweight : ∀ j, w' j = w (q j) := by
    intro j
    have h := congrArg (fun f : T → ℝ => ∑ t, f t) (funext (hscale j))
    simpa [← Finset.mul_sum, hC j, hC' j, hC (q j)] using h
  have hthird : ∀ t j, C' t j = C t (q j) := by
    intro t j
    have h := hscale j t
    rw [hweight j] at h
    exact mul_left_cancel₀ (hw (q j)) h
  refine ⟨q, hweight, recover_factor_of_pair w w' A A' C C' LC hLC hw q hweight hthird hac, ?_, hthird⟩
  apply recover_factor_of_pair w w' B B' C C' LC hLC hw q hweight hthird
  intro y t
  have h := congrArg (fun f : X → ℝ => ∑ x, f x) (funext fun x => heq x y t)
  simpa only [tensor_marginal_first _ _ _ _ hA,
    tensor_marginal_first _ _ _ _ hA'] using h

/-- Ordinary linear independence of the reference columns supplies the duals. -/
theorem exists_leftDual_of_linearIndependent (A : X → Z → ℝ)
    (hA : LinearIndependent ℝ (fun j x => A x j)) : ∃ L, LeftDual A L := by
  classical
  let M : Matrix X Z ℝ := A
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff.mpr hA
  obtain ⟨g, hg⟩ := M.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have hmat : LinearMap.toMatrix' g * M = 1 := by
    have h := congrArg (LinearMap.toMatrix' (R := ℝ)) hg
    simpa only [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using h
  intro i j
  exact congrFun (congrFun hmat i) j

/-- Elementary uniqueness against unrestricted same-cardinality normalized
competitors. In particular this applies to positive stochastic mixtures.
Only the reference column families have a rank hypothesis. -/
theorem fullColumnRank_unique [Nonempty Z]
    (w w' : Z → ℝ) (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ)
    (C C' : T → Z → ℝ)
    (hA : Normalized A) (hA' : Normalized A')
    (hB : Normalized B) (hB' : Normalized B')
    (hC : Normalized C) (hC' : Normalized C')
    (hw : ∀ j, 0 < w j) (hw' : ∀ j, 0 < w' j)
    (hAr : LinearIndependent ℝ (fun j x => A x j))
    (hBr : LinearIndependent ℝ (fun j y => B y j))
    (hCr : LinearIndependent ℝ (fun j t => C t j))
    (heq : ∀ x y t, tensor w A B C x y t = tensor w' A' B' C' x y t) :
    ∃ q : Equiv.Perm Z, (∀ j, w' j = w (q j)) ∧
      (∀ x j, A' x j = A x (q j)) ∧
      (∀ y j, B' y j = B y (q j)) ∧ (∀ t j, C' t j = C t (q j)) := by
  obtain ⟨LA, hLA⟩ := exists_leftDual_of_linearIndependent A hAr
  obtain ⟨LB, hLB⟩ := exists_leftDual_of_linearIndependent B hBr
  obtain ⟨LC, hLC⟩ := exists_leftDual_of_linearIndependent C hCr
  exact fullRank_unique_of_duals w w' A A' B B' C C' hA hA' hB hB' hC hC'
    (fun j => ne_of_gt (hw j)) (fun j => ne_of_gt (hw' j)) LA LB LC hLA hLB hLC heq

#print axioms fullColumnRank_unique

end Gen.Uniqueness

namespace Gen
open scoped BigOperators
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {Y : G → Type*} [∀ g, Fintype (Y g)] {r : ℕ}

/-- Full column rank on each complete real kernel, with no restriction on comparisons. -/
def FullColumnRank (θ : Parameter D Y r) : Prop :=
  ∀ g, LinearIndependent ℝ (fun z : Fin r => fun y => θ.kernel g y z)

theorem fullColumnRank_distinctColumns (θ : Parameter D Y r) (hrank : FullColumnRank θ) :
    DistinctColumns θ := fun g => (hrank g).injective

/-- The elementary tensor theorem supplies GEN-D05 local rigidity for RATE's
full-column-rank subclass. This is independent of general Kruskal uniqueness. -/
theorem localRigid_of_fullColumnRank (θ : Parameter D Y r) (hr : 0 < r)
    (hrank : FullColumnRank θ) (e : D.Edge) : LocalRigid θ e := by
  classical
  letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let s : Fin 3 ≃ D.GroupAt e := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, D.edge_card e.val e.property])
  intro η ho
  have hT : ∀ (x : Y (s 0).val) (y : Y (s 1).val) (t : Y (s 2).val),
      Uniqueness.tensor (θ.weight (D.component e))
        (θ.kernel (s 0).val) (θ.kernel (s 1).val) (θ.kernel (s 2).val) x y t =
      Uniqueness.tensor η.weight (η.kernel (s 0)) (η.kernel (s 1)) (η.kernel (s 2)) x y t := by
    intro x y t
    let f : (i : Fin 3) → Y (s i).val :=
      Fin.cons x (Fin.cons y (Fin.cons t (fun i => Fin.elim0 i)))
    let o : D.Outcome Y e := Equiv.piCongrLeft (fun g : D.GroupAt e => Y g.val) s f
    have hf : ∀ i, o (s i) = f i := by intro i; simp [o]
    have hp (K : (g : D.GroupAt e) → Y g.val → Fin r → ℝ) (z : Fin r) :
        (∏ g, K g (o g) z) = K (s 0) x z * K (s 1) y z * K (s 2) t z := by
      rw [← s.prod_comp (fun g => K g (o g) z)]
      simp_rw [hf]
      rw [Fin.prod_univ_three]
      rfl
    have h := ho o
    simp only [LocalSystem.observation, Parameter.observation_formula] at h
    simp_rw [hp] at h
    simpa only [Uniqueness.tensor, mul_assoc] using h.symm
  obtain ⟨q, hw, hA, hB, hC⟩ := Uniqueness.fullColumnRank_unique
    (θ.weight (D.component e)) η.weight
    (θ.kernel (s 0).val) (η.kernel (s 0))
    (θ.kernel (s 1).val) (η.kernel (s 1))
    (θ.kernel (s 2).val) (η.kernel (s 2))
    (θ.kernel_total (s 0).val) (η.kernel_total (s 0))
    (θ.kernel_total (s 1).val) (η.kernel_total (s 1))
    (θ.kernel_total (s 2).val) (η.kernel_total (s 2))
    (θ.weight_pos (D.component e)) η.weight_pos
    (hrank (s 0).val) (hrank (s 1).val) (hrank (s 2).val) hT
  refine ⟨q, hw, ?_⟩
  intro g
  obtain ⟨i, rfl⟩ := s.surjective g
  fin_cases i
  · exact hA
  · exact hB
  · exact hC

/-- RATE-D3's global algebraic core, even against the whole unrestricted Xi_r.
There is a separate permutation for each edge-intersection component. -/
theorem fullColumnRank_fiber_eq_component_orbit (θ : Parameter D Y r) (hr : 0 < r)
    (hrank : FullColumnRank θ) :
    fiber D Y r θ (fun _ => True) = orbit D Y r θ ⊤ :=
  fiber_eq_component_orbit_of_localRigid θ (localRigid_of_fullColumnRank θ hr hrank)
    (fullColumnRank_distinctColumns θ hrank)

theorem fullColumnRank_observation_eq_iff (θ η : Parameter D Y r) (hr : 0 < r)
    (hrank : FullColumnRank θ) :
    (∀ e x, η.observation e x = θ.observation e x) ↔ ∃ q : W D r, η = θ.permute q := by
  have h := fullColumnRank_fiber_eq_component_orbit θ hr hrank
  constructor
  · intro ho
    have hf : η ∈ fiber D Y r θ (fun _ => True) := ⟨ho, trivial⟩
    rw [h] at hf
    obtain ⟨q, _, hq⟩ := hf
    exact ⟨q, hq⟩
  · rintro ⟨q, rfl⟩
    exact θ.permute_observation q

#print axioms localRigid_of_fullColumnRank
#print axioms fullColumnRank_observation_eq_iff
end Gen
