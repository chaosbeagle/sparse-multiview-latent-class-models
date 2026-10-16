import Gen.Uniqueness
import Gen.Geometry
import Gen.Hessian
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Exact local Jacobian contractions and sharp dimension-free-in-r estimates. -/
set_option maxHeartbeats 1000000

namespace Gen.Jacobian
open scoped BigOperators
open Gen.Uniqueness
variable {Z X Y T : Type*} [Fintype Z] [DecidableEq Z]
  [Fintype X] [Fintype Y] [Fintype T]

/-- The directional derivative of the four-factor local observation polynomial. -/
def localDerivative (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ) (x : X) (y : Y) (t : T) : ℝ :=
  tensor dw A B C x y t + tensor w dA B C x y t +
    tensor w A dB C x y t + tensor w A B dC x y t

/-- Selected diagonal slice after contracting the second and third modes. -/
def selectedSlice (LB : Z → Y → ℝ) (LC : Z → T → ℝ)
    (J : X → Y → T → ℝ) (z : Z) (x : X) : ℝ :=
  ∑ y, LB z y * ∑ t, LC z t * J x y t

theorem selectedSlice_identity
    (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ)
    (LB : Z → Y → ℝ) (LC : Z → T → ℝ)
    (hLB : LeftDual B LB) (hLC : LeftDual C LC) (z : Z) (x : X) :
    selectedSlice LB LC (localDerivative w dw A dA B dB C dC) z x =
      w z * dA x z +
      (dw z + w z * contract LB dB z z + w z * contract LC dC z z) * A x z := by
  simp only [selectedSlice, localDerivative, mul_add, Finset.sum_add_distrib]
  simp_rw [contract_tensor_third, contract_tensor_second]
  change ∀ i j, ∑ y, LB i y * B y j = if i = j then 1 else 0 at hLB
  change ∀ i j, ∑ t, LC i t * C t j = if i = j then 1 else 0 at hLC
  simp [tensor, contract, hLB, hLC]
  ring

/-- Homogeneous column normalization removes the undetermined scalar direction. -/
theorem normalized_column_recovery
    (a da t : X → ℝ) (w α : ℝ)
    (ha : ∑ x, a x = 1) (hda : ∑ x, da x = 0)
    (ht : ∀ x, t x = w * da x + α * a x) :
    (∑ x, t x = α) ∧ ∀ x, w * da x = t x - a x * ∑ y, t y := by
  have hs : ∑ x, t x = α := by
    simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum, hda, ha]
    ring
  exact ⟨hs, fun x => by rw [hs, ht]; ring⟩

/-- The actual normalized kernel tangent is recovered from diagonal contracted slices. -/
theorem selectedSlice_recovery
    (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ)
    (LB : Z → Y → ℝ) (LC : Z → T → ℝ)
    (hA : Gen.Uniqueness.Normalized A) (hdA : ∀ z, ∑ x, dA x z = 0)
    (hLB : LeftDual B LB) (hLC : LeftDual C LC) (z : Z) (x : X) :
    w z * dA x z =
      selectedSlice LB LC (localDerivative w dw A dA B dB C dC) z x -
        A x z * ∑ y, selectedSlice LB LC (localDerivative w dw A dA B dB C dC) z y := by
  exact (normalized_column_recovery (fun x => A x z) (fun x => dA x z)
    (selectedSlice LB LC (localDerivative w dw A dA B dB C dC) z)
    (w z) (dw z + w z * contract LB dB z z + w z * contract LC dC z z)
    (hA z) (hdA z) (selectedSlice_identity w dw A dA B dB C dC LB LC hLB hLC z)).2 x

/-- Full diagonal triple contraction gives the literal weight-tangent identity. -/
theorem diagonal_weight_identity
    (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ)
    (LA : Z → X → ℝ) (LB : Z → Y → ℝ) (LC : Z → T → ℝ)
    (hLA : LeftDual A LA) (hLB : LeftDual B LB) (hLC : LeftDual C LC) (z : Z) :
    (∑ x, LA z x * selectedSlice LB LC (localDerivative w dw A dA B dB C dC) z x) =
      dw z + w z * (contract LA dA z z + contract LB dB z z + contract LC dC z z) := by
  simp_rw [selectedSlice_identity w dw A dA B dB C dC LB LC hLB hLC z]
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : (∑ x, LA z x * (w z * dA x z)) = w z * contract LA dA z z := by
    simp only [contract, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have h2 : ∀ c : ℝ, (∑ x, LA z x * (c * A x z)) = c := by
    intro c
    calc
      _ = c * ∑ x, LA z x * A x z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = c := by rw [hLA]; simp
  rw [h1, h2]
  ring

#print axioms selectedSlice_recovery
#print axioms diagonal_weight_identity
/-- Euclidean matrix action, retaining sum-of-squares norms. -/
def euclideanMul (A : X → Z → ℝ) : EuclideanSpace ℝ Z →ₗ[ℝ] EuclideanSpace ℝ X where
  toFun v := WithLp.toLp 2 (fun x => ∑ z, A x z * v z)
  map_add' u v := by ext x; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext x; simp [Finset.mul_sum, mul_assoc, mul_left_comm]

/-- A lower Euclidean singular-value bound gives an actual bounded left inverse
by orthogonal projection onto the range. No inverse-bound oracle is assumed. -/
theorem exists_bounded_leftInverse
    (M : EuclideanSpace ℝ Z →ₗ[ℝ] EuclideanSpace ℝ X)
    (σ : ℝ) (hσ : 0 < σ) (hM : ∀ v, σ * ‖v‖ ≤ ‖M v‖) :
    ∃ L : EuclideanSpace ℝ X →ₗ[ℝ] EuclideanSpace ℝ Z,
      (∀ v, L (M v) = v) ∧ ∀ v, ‖L v‖ ≤ σ⁻¹ * ‖v‖ := by
  classical
  have hinj : Function.Injective M := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h := hM v
    rw [hv, norm_zero] at h
    have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp this
  let E := LinearEquiv.ofInjective M hinj
  let P := M.range.orthogonalProjectionOnto
  let L : EuclideanSpace ℝ X →ₗ[ℝ] EuclideanSpace ℝ Z := E.symm.toLinearMap.comp P.toLinearMap
  have hML : ∀ v, M (L v) = (P v : EuclideanSpace ℝ X) := by
    intro v
    exact congrArg Subtype.val (E.apply_symm_apply (P v))
  refine ⟨L, ?_, ?_⟩
  · intro v
    change E.symm (P (M v)) = v
    have hp : P (M v) = E v := by
      change M.range.orthogonalProjectionOnto (↑(E v)) = E v
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (E v)
    rw [hp, E.symm_apply_apply]
  · intro v
    have h := hM (L v)
    rw [hML] at h
    have hp : ‖P v‖ ≤ ‖v‖ := by
      calc
        ‖P v‖ ≤ ‖P‖ * ‖v‖ := P.le_opNorm v
        _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
          M.range.orthogonalProjectionOnto_norm_le (norm_nonneg v)
        _ = ‖v‖ := one_mul _
    have h' : σ * ‖L v‖ ≤ ‖v‖ := h.trans hp
    exact (le_inv_mul_iff₀ hσ).mpr h'

/-- The matrix version of the bounded Euclidean pseudoinverse. -/
theorem exists_bounded_dual (A : X → Z → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hGram : ∀ v : Z → ℝ, σ ^ 2 * (∑ z, (v z) ^ 2) ≤
      ∑ x, (∑ z, A x z * v z) ^ 2) :
    ∃ Λ : Z → X → ℝ, LeftDual A Λ ∧
      ∀ v : X → ℝ, (∑ z, (∑ x, Λ z x * v x) ^ 2) ≤ σ⁻¹ ^ 2 * ∑ x, (v x) ^ 2 := by
  classical
  let M := euclideanMul A
  have hM : ∀ v, σ * ‖v‖ ≤ ‖M v‖ := by
    intro v
    have h := hGram v.ofLp
    have hsq : (σ * ‖v‖) ^ 2 ≤ ‖M v‖ ^ 2 := by
      simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, M, euclideanMul,
        LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp] using h
    exact (sq_le_sq₀ (mul_nonneg hσ.le (norm_nonneg _)) (norm_nonneg _)).mp hsq
  obtain ⟨L, hLM, hLnorm⟩ := exists_bounded_leftInverse M σ hσ hM
  let F : (X → ℝ) →ₗ[ℝ] (Z → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Z → ℝ)).toLinearMap.comp
      (L.comp (WithLp.linearEquiv 2 ℝ (X → ℝ)).symm.toLinearMap)
  let Λ : Matrix Z X ℝ := LinearMap.toMatrix' F
  have hΛ (v : X → ℝ) (i : Z) : (∑ x, Λ i x * v x) = L (WithLp.toLp 2 v) i := by
    exact congrFun (LinearMap.toMatrix'_mulVec F v) i
  refine ⟨Λ, ?_, ?_⟩
  · intro i j
    rw [hΛ]
    have hv : WithLp.toLp 2 (fun x => A x j) = M (EuclideanSpace.single j 1) := by
      ext x
      simp [M, euclideanMul]
    rw [hv, hLM]
    simp [eq_comm]
  · intro v
    have h := hLnorm (WithLp.toLp 2 v)
    have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hσ.le) (norm_nonneg _)) |>.mpr h
    simpa only [EuclideanSpace.real_norm_sq_eq, mul_pow, hΛ,
      WithLp.ofLp_toLp] using hsq

#print axioms exists_bounded_dual
/-- Summation as a Euclidean functional has norm at most sqrt of the alphabet size. -/
theorem abs_sum_le_sqrt_card_mul_norm (v : X → ℝ) :
    |∑ x, v x| ≤ Real.sqrt (Fintype.card X) * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ X)‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : X => (1 : ℝ))
    (fun x => |v x|)
  have hs : Real.sqrt (∑ x, (v x)^2) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ X)‖ := by
    rw [← EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v), Real.sqrt_sq (norm_nonneg _)]
  have h' : ∑ x, |v x| ≤ Real.sqrt (Fintype.card X) *
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ X)‖ := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, sq_abs, hs] using h
  exact (Finset.abs_sum_le_sum_abs _ _).trans h'

/-- Exact normalized-column estimate underlying the literal a_g. -/
theorem normalized_column_square_bound
    (a da t : X → ℝ) (w w0 : ℝ) (hw0 : 0 < w0) (hw : w0 ≤ w)
    (ha : ∀ x, 0 ≤ a x) (hat : ∑ x, a x = 1)
    (hrec : ∀ x, w * da x = t x - a x * ∑ y, t y) :
    ∑ x, (da x)^2 ≤ ((1 + Real.sqrt (Fintype.card X)) / w0)^2 * ∑ x, (t x)^2 := by
  let av : EuclideanSpace ℝ X := WithLp.toLp 2 a
  let dv : EuclideanSpace ℝ X := WithLp.toLp 2 da
  let tv : EuclideanSpace ℝ X := WithLp.toLp 2 t
  have hav : ‖av‖ ≤ 1 := by
    have h := Gen.Constants.probability_square_sum_le_one a ha hat
    have hsq : ‖av‖^2 ≤ (1:ℝ)^2 := by
      simpa [EuclideanSpace.real_norm_sq_eq, av] using h
    exact (sq_le_sq₀ (norm_nonneg av) zero_le_one).mp hsq
  have hvec : w • dv = tv - (∑ y, t y) • av := by
    ext x
    simpa [av, dv, tv, mul_comm] using hrec x
  have hwpos : 0 < w := hw0.trans_le hw
  have hn : w * ‖dv‖ ≤ (1 + Real.sqrt (Fintype.card X)) * ‖tv‖ := by
    calc
      w * ‖dv‖ = ‖w • dv‖ := by rw [norm_smul, Real.norm_of_nonneg hwpos.le]
      _ = ‖tv - (∑ y, t y) • av‖ := congrArg norm hvec
      _ ≤ ‖tv‖ + ‖(∑ y, t y) • av‖ := norm_sub_le _ _
      _ = ‖tv‖ + |∑ y, t y| * ‖av‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖tv‖ + (Real.sqrt (Fintype.card X) * ‖tv‖) * 1 := by
        apply add_le_add_right
        exact mul_le_mul (abs_sum_le_sqrt_card_mul_norm t) hav (norm_nonneg av)
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg tv))
      _ = _ := by ring
  have hn' : ‖dv‖ ≤ ((1 + Real.sqrt (Fintype.card X)) / w0) * ‖tv‖ := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hw0).mpr
    have h : ‖dv‖ * w0 ≤ (1 + Real.sqrt (Fintype.card X)) * ‖tv‖ := by
      calc
        ‖dv‖ * w0 ≤ ‖dv‖ * w := mul_le_mul_of_nonneg_left hw (norm_nonneg dv)
        _ ≤ _ := by simpa [mul_comm] using hn
    simpa [div_mul_eq_mul_div] using h
  have hn2 := (sq_le_sq₀ (norm_nonneg dv) (by positivity :
    0 ≤ ((1 + Real.sqrt (Fintype.card X)) / w0) * ‖tv‖)).mpr hn'
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, dv, tv, WithLp.ofLp_toLp] using hn2

/-- Diagonal mode-(2,3) slice selection has no latent-count penalty. -/
theorem selectedSlice_square_bound
    (LB : Z → Y → ℝ) (LC : Z → T → ℝ) (J : X → Y → T → ℝ)
    (b c : ℝ)
    (hB : ∀ v : Y → ℝ, (∑ i, (∑ y, LB i y * v y)^2) ≤ b^2 * ∑ y, (v y)^2)
    (hC : ∀ v : T → ℝ, (∑ k, (∑ t, LC k t * v t)^2) ≤ c^2 * ∑ t, (v t)^2) :
    (∑ z, ∑ x, (selectedSlice LB LC J z x)^2) ≤
      b^2 * c^2 * ∑ x, ∑ y, ∑ t, (J x y t)^2 := by
  have hx (x : X) : (∑ i, ∑ k, (∑ y, LB i y * ∑ t, LC k t * J x y t)^2) ≤
      b^2 * c^2 * ∑ y, ∑ t, (J x y t)^2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ k, b^2 * ∑ y, (∑ t, LC k t * J x y t)^2 := by
        exact Finset.sum_le_sum (fun k hk => hB (fun y => ∑ t, LC k t * J x y t))
      _ = b^2 * ∑ y, ∑ k, (∑ t, LC k t * J x y t)^2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ b^2 * ∑ y, c^2 * ∑ t, (J x y t)^2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
        exact Finset.sum_le_sum (fun y hy => hC (J x y))
      _ = _ := by rw [← Finset.mul_sum]; ring
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ x, ∑ i, ∑ k, (∑ y, LB i y * ∑ t, LC k t * J x y t)^2 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro i _
      exact Finset.single_le_sum (f := fun k : Z => (∑ y, LB i y * ∑ t, LC k t * J x y t)^2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ x, b^2 * c^2 * ∑ y, ∑ t, (J x y t)^2 :=
      Finset.sum_le_sum (fun x _ => hx x)
    _ = _ := by rw [← Finset.mul_sum]

#print axioms normalized_column_square_bound
#print axioms selectedSlice_square_bound
/-- Literal a_g squared Frobenius estimate, with actual Gram-margin hypotheses
and no assumed inverse or contraction bounds. There is no factor r. -/
theorem kernel_tangent_square_bound
    (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ)
    (w0 σ : ℝ) (hw0 : 0 < w0) (hσ : 0 < σ) (hw : ∀ z, w0 ≤ w z)
    (hA : Gen.Uniqueness.Normalized A) (hAnonneg : ∀ x z, 0 ≤ A x z)
    (hdA : ∀ z, ∑ x, dA x z = 0)
    (hB : ∀ v : Z → ℝ, σ^2 * (∑ z, (v z)^2) ≤ ∑ y, (∑ z, B y z * v z)^2)
    (hC : ∀ v : Z → ℝ, σ^2 * (∑ z, (v z)^2) ≤ ∑ t, (∑ z, C t z * v z)^2) :
    (∑ z, ∑ x, (dA x z)^2) ≤
      ((1 + Real.sqrt (Fintype.card X)) / (w0 * σ^2))^2 *
        ∑ x, ∑ y, ∑ t, (localDerivative w dw A dA B dB C dC x y t)^2 := by
  obtain ⟨LB, hLB, hBn⟩ := exists_bounded_dual B σ hσ hB
  obtain ⟨LC, hLC, hCn⟩ := exists_bounded_dual C σ hσ hC
  let J := localDerivative w dw A dA B dB C dC
  let k := (1 + Real.sqrt (Fintype.card X)) / w0
  calc
    _ ≤ ∑ z, k^2 * ∑ x, (selectedSlice LB LC J z x)^2 := by
      apply Finset.sum_le_sum
      intro z _
      exact normalized_column_square_bound (fun x => A x z) (fun x => dA x z)
        (selectedSlice LB LC J z) (w z) w0 hw0 (hw z)
        (fun x => hAnonneg x z) (hA z)
        (selectedSlice_recovery w dw A dA B dB C dC LB LC hA hdA hLB hLC z)
    _ = k^2 * ∑ z, ∑ x, (selectedSlice LB LC J z x)^2 := by rw [Finset.mul_sum]
    _ ≤ k^2 * (σ⁻¹^2 * σ⁻¹^2 * ∑ x, ∑ y, ∑ t, (J x y t)^2) :=
      mul_le_mul_of_nonneg_left (selectedSlice_square_bound LB LC J σ⁻¹ σ⁻¹ hBn hCn) (sq_nonneg k)
    _ = _ := by dsimp [k, J]; field_simp

/-- A diagonal selection after one additional contraction has operator cost only
one further σ⁻¹, not sqrt r. -/
theorem diagonal_triple_square_bound
    (LA : Z → X → ℝ) (LB : Z → Y → ℝ) (LC : Z → T → ℝ)
    (J : X → Y → T → ℝ) (a b c : ℝ)
    (hA : ∀ v : X → ℝ, (∑ i, (∑ x, LA i x * v x)^2) ≤ a^2 * ∑ x, (v x)^2)
    (hB : ∀ v : Y → ℝ, (∑ i, (∑ y, LB i y * v y)^2) ≤ b^2 * ∑ y, (v y)^2)
    (hC : ∀ v : T → ℝ, (∑ i, (∑ t, LC i t * v t)^2) ≤ c^2 * ∑ t, (v t)^2) :
    (∑ z, (∑ x, LA z x * selectedSlice LB LC J z x)^2) ≤
      a^2 * b^2 * c^2 * ∑ x, ∑ y, ∑ t, (J x y t)^2 := by
  calc
    _ ≤ ∑ z, a^2 * ∑ x, (selectedSlice LB LC J z x)^2 := by
      apply Finset.sum_le_sum
      intro z _
      calc
        _ ≤ ∑ i, (∑ x, LA i x * selectedSlice LB LC J z x)^2 :=
          Finset.single_le_sum (f := fun i => (∑ x, LA i x * selectedSlice LB LC J z x)^2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ z)
        _ ≤ _ := hA (selectedSlice LB LC J z)
    _ = a^2 * ∑ z, ∑ x, (selectedSlice LB LC J z x)^2 := by rw [Finset.mul_sum]
    _ ≤ a^2 * (b^2 * c^2 * ∑ x, ∑ y, ∑ t, (J x y t)^2) :=
      mul_le_mul_of_nonneg_left (selectedSlice_square_bound LB LC J b c hB hC) (sq_nonneg a)
    _ = _ := by ring

/-- Weighted diagonal contraction of one kernel tangent. -/
theorem weighted_diagonal_square_bound (L : Z → X → ℝ) (dA : X → Z → ℝ)
    (w : Z → ℝ) (c : ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (hL : ∀ v : X → ℝ, (∑ i, (∑ x, L i x * v x)^2) ≤ c^2 * ∑ x, (v x)^2) :
    (∑ z, (w z * contract L dA z z)^2) ≤ c^2 * ∑ z, ∑ x, (dA x z)^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  calc
    _ ≤ (contract L dA z z)^2 := by
      have hw2 : (w z)^2 ≤ 1 := by nlinarith [(hw z).1, (hw z).2]
      rw [mul_pow]
      nlinarith [sq_nonneg (contract L dA z z)]
    _ ≤ ∑ i, (∑ x, L i x * dA x z)^2 :=
      Finset.single_le_sum (f := fun i => (∑ x, L i x * dA x z)^2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ z)
    _ ≤ _ := hL (fun x => dA x z)

#print axioms kernel_tangent_square_bound
#print axioms diagonal_triple_square_bound
lemma tensor_swap_first_second (w : Z → ℝ) (A : X → Z → ℝ)
    (B : Y → Z → ℝ) (C : T → Z → ℝ) (x : X) (y : Y) (t : T) :
    tensor w A B C x y t = tensor w B A C y x t := by
  unfold tensor
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma tensor_cycle (w : Z → ℝ) (A : X → Z → ℝ)
    (B : Y → Z → ℝ) (C : T → Z → ℝ) (x : X) (y : Y) (t : T) :
    tensor w A B C x y t = tensor w C A B t x y := by
  unfold tensor
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma localDerivative_swap_first_second
    (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ) (x : X) (y : Y) (t : T) :
    localDerivative w dw B dB A dA C dC y x t =
      localDerivative w dw A dA B dB C dC x y t := by
  unfold localDerivative
  rw [tensor_swap_first_second dw B A C y x t,
    tensor_swap_first_second w dB A C y x t,
    tensor_swap_first_second w B dA C y x t,
    tensor_swap_first_second w B A dC y x t]
  ring

lemma localDerivative_cycle
    (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ) (x : X) (y : Y) (t : T) :
    localDerivative w dw C dC A dA B dB t x y =
      localDerivative w dw A dA B dB C dC x y t := by
  unfold localDerivative
  rw [← tensor_cycle dw A B C x y t, ← tensor_cycle w A B dC x y t,
    ← tensor_cycle w dA B C x y t, ← tensor_cycle w A dB C x y t]
  ring

/-- All three literal a_g estimates from the exact local derivative. -/
theorem all_kernel_tangent_square_bounds
    (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ)
    (w0 σ : ℝ) (hw0 : 0 < w0) (hσ : 0 < σ) (hw : ∀ z, w0 ≤ w z)
    (hA : Gen.Uniqueness.Normalized A) (hAnonneg : ∀ x z, 0 ≤ A x z)
    (hB : Gen.Uniqueness.Normalized B) (hBnonneg : ∀ y z, 0 ≤ B y z)
    (hC : Gen.Uniqueness.Normalized C) (hCnonneg : ∀ t z, 0 ≤ C t z)
    (hdA : ∀ z, ∑ x, dA x z = 0) (hdB : ∀ z, ∑ y, dB y z = 0)
    (hdC : ∀ z, ∑ t, dC t z = 0)
    (hGA : ∀ v : Z → ℝ, σ^2 * (∑ z, (v z)^2) ≤ ∑ x, (∑ z, A x z * v z)^2)
    (hGB : ∀ v : Z → ℝ, σ^2 * (∑ z, (v z)^2) ≤ ∑ y, (∑ z, B y z * v z)^2)
    (hGC : ∀ v : Z → ℝ, σ^2 * (∑ z, (v z)^2) ≤ ∑ t, (∑ z, C t z * v z)^2) :
    let J2 := ∑ x, ∑ y, ∑ t, (localDerivative w dw A dA B dB C dC x y t)^2
    ((∑ z, ∑ x, (dA x z)^2) ≤ ((1+Real.sqrt (Fintype.card X))/(w0*σ^2))^2 * J2) ∧
    ((∑ z, ∑ y, (dB y z)^2) ≤ ((1+Real.sqrt (Fintype.card Y))/(w0*σ^2))^2 * J2) ∧
    ((∑ z, ∑ t, (dC t z)^2) ≤ ((1+Real.sqrt (Fintype.card T))/(w0*σ^2))^2 * J2) := by
  dsimp only
  refine ⟨kernel_tangent_square_bound w dw A dA B dB C dC w0 σ hw0 hσ hw hA hAnonneg hdA hGB hGC, ?_, ?_⟩
  · have h := kernel_tangent_square_bound w dw B dB A dA C dC w0 σ hw0 hσ hw hB hBnonneg hdB hGA hGC
    simp_rw [localDerivative_swap_first_second w dw A dA B dB C dC] at h
    rwa [Finset.sum_comm (f := fun y x => ∑ t, (localDerivative w dw A dA B dB C dC x y t)^2)] at h
  · have h := kernel_tangent_square_bound w dw C dC A dA B dB w0 σ hw0 hσ hw hC hCnonneg hdC hGA hGB
    simp_rw [localDerivative_cycle w dw A dA B dB C dC] at h
    have heq : (∑ t, ∑ x, ∑ y, (localDerivative w dw A dA B dB C dC x y t)^2) =
        ∑ x, ∑ y, ∑ t, (localDerivative w dw A dA B dB C dC x y t)^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    rwa [heq] at h

lemma norm_le_of_square_sum_le {I : Type*} [Fintype I] (v : I → ℝ) (c E : ℝ)
    (hc : 0 ≤ c) (hE : 0 ≤ E) (h : ∑ i, (v i)^2 ≤ c^2 * E^2) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ I)‖ ≤ c * E := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc hE)).mp
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_toLp] using h

/-- Norm consequence of the triple-diagonal contraction estimate. -/
lemma norm_diagonal_triple_le
    (LA : Z → X → ℝ) (LB : Z → Y → ℝ) (LC : Z → T → ℝ)
    (J : X → Y → T → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hA : ∀ v : X → ℝ, (∑ i, (∑ x, LA i x * v x)^2) ≤ σ⁻¹^2 * ∑ x, (v x)^2)
    (hB : ∀ v : Y → ℝ, (∑ i, (∑ y, LB i y * v y)^2) ≤ σ⁻¹^2 * ∑ y, (v y)^2)
    (hC : ∀ v : T → ℝ, (∑ i, (∑ t, LC i t * v t)^2) ≤ σ⁻¹^2 * ∑ t, (v t)^2) :
    ‖(WithLp.toLp 2 (fun z => ∑ x, LA z x * selectedSlice LB LC J z x) : EuclideanSpace ℝ Z)‖ ≤
      σ⁻¹^3 * Real.sqrt (∑ x, ∑ y, ∑ t, (J x y t)^2) := by
  apply norm_le_of_square_sum_le _ _ _ (by positivity) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by positivity)]
  have h := diagonal_triple_square_bound LA LB LC J σ⁻¹ σ⁻¹ σ⁻¹ hA hB hC
  convert h using 1 <;> ring

/-- Weighted kernel diagonal norm after substituting a squared a_g estimate. -/
lemma norm_weighted_diagonal_le (L : Z → X → ℝ) (dA : X → Z → ℝ)
    (w : Z → ℝ) (σ a E : ℝ) (hσ : 0 < σ) (ha : 0 ≤ a) (hE : 0 ≤ E)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (hL : ∀ v : X → ℝ, (∑ i, (∑ x, L i x * v x)^2) ≤ σ⁻¹^2 * ∑ x, (v x)^2)
    (hdA : (∑ z, ∑ x, (dA x z)^2) ≤ a^2 * E^2) :
    ‖(WithLp.toLp 2 (fun z => w z * contract L dA z z) : EuclideanSpace ℝ Z)‖ ≤
      (σ⁻¹ * a) * E := by
  apply norm_le_of_square_sum_le _ _ _ (mul_nonneg (inv_nonneg.mpr hσ.le) ha) hE
  calc
    _ ≤ σ⁻¹^2 * ∑ z, ∑ x, (dA x z)^2 := weighted_diagonal_square_bound L dA w σ⁻¹ hw hL
    _ ≤ σ⁻¹^2 * (a^2 * E^2) := mul_le_mul_of_nonneg_left hdA (sq_nonneg _)
    _ = _ := by ring

#print axioms all_kernel_tangent_square_bounds
/-- Exact weight estimate after combining its diagonal identity with the three
already-proved kernel estimates. -/
theorem weight_tangent_bound_of_kernel_bounds
    (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ)
    (LA : Z → X → ℝ) (LB : Z → Y → ℝ) (LC : Z → T → ℝ)
    (hLA : LeftDual A LA) (hLB : LeftDual B LB) (hLC : LeftDual C LC)
    (σ a b c : ℝ) (hσ : 0 < σ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (hLnA : ∀ v : X → ℝ, (∑ i, (∑ x, LA i x * v x)^2) ≤ σ⁻¹^2 * ∑ x, (v x)^2)
    (hLnB : ∀ v : Y → ℝ, (∑ i, (∑ y, LB i y * v y)^2) ≤ σ⁻¹^2 * ∑ y, (v y)^2)
    (hLnC : ∀ v : T → ℝ, (∑ i, (∑ t, LC i t * v t)^2) ≤ σ⁻¹^2 * ∑ t, (v t)^2)
    (hA : (∑ z, ∑ x, (dA x z)^2) ≤ a^2 * ∑ x, ∑ y, ∑ t,
      (localDerivative w dw A dA B dB C dC x y t)^2)
    (hB : (∑ z, ∑ y, (dB y z)^2) ≤ b^2 * ∑ x, ∑ y, ∑ t,
      (localDerivative w dw A dA B dB C dC x y t)^2)
    (hC : (∑ z, ∑ t, (dC t z)^2) ≤ c^2 * ∑ x, ∑ y, ∑ t,
      (localDerivative w dw A dA B dB C dC x y t)^2) :
    (∑ z, (dw z)^2) ≤ (σ⁻¹^3 + σ⁻¹ * (a+b+c))^2 *
      ∑ x, ∑ y, ∑ t, (localDerivative w dw A dA B dB C dC x y t)^2 := by
  let J := localDerivative w dw A dA B dB C dC
  let E : ℝ := Real.sqrt (∑ x, ∑ y, ∑ t, (J x y t)^2)
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hE2 : E^2 = ∑ x, ∑ y, ∑ t, (J x y t)^2 := Real.sq_sqrt (by positivity)
  let dv : EuclideanSpace ℝ Z := WithLp.toLp 2 dw
  let vA : EuclideanSpace ℝ Z := WithLp.toLp 2 (fun z => w z * contract LA dA z z)
  let vB : EuclideanSpace ℝ Z := WithLp.toLp 2 (fun z => w z * contract LB dB z z)
  let vC : EuclideanSpace ℝ Z := WithLp.toLp 2 (fun z => w z * contract LC dC z z)
  let diag : EuclideanSpace ℝ Z := WithLp.toLp 2 (fun z => ∑ x, LA z x * selectedSlice LB LC J z x)
  have hd : ‖diag‖ ≤ σ⁻¹^3 * E := norm_diagonal_triple_le LA LB LC J σ hσ hLnA hLnB hLnC
  have hvA : ‖vA‖ ≤ (σ⁻¹ * a) * E :=
    norm_weighted_diagonal_le LA dA w σ a E hσ ha hE hw hLnA (by rwa [hE2])
  have hvB : ‖vB‖ ≤ (σ⁻¹ * b) * E :=
    norm_weighted_diagonal_le LB dB w σ b E hσ hb hE hw hLnB (by rwa [hE2])
  have hvC : ‖vC‖ ≤ (σ⁻¹ * c) * E :=
    norm_weighted_diagonal_le LC dC w σ c E hσ hc hE hw hLnC (by rwa [hE2])
  have heq : dv = diag - (vA + vB + vC) := by
    ext z
    change dw z = (∑ x, LA z x * selectedSlice LB LC J z x) -
      (w z * contract LA dA z z + w z * contract LB dB z z + w z * contract LC dC z z)
    rw [diagonal_weight_identity w dw A dA B dB C dC LA LB LC hLA hLB hLC z]
    ring
  have hn : ‖dv‖ ≤ (σ⁻¹^3 + σ⁻¹ * (a+b+c)) * E := by
    calc
      ‖dv‖ = ‖diag - (vA + vB + vC)‖ := congrArg norm heq
      _ ≤ ‖diag‖ + (‖vA‖ + ‖vB‖ + ‖vC‖) := by
        have h1 := norm_sub_le diag (vA + vB + vC)
        have h2 := norm_add_le (vA + vB) vC
        have h3 := norm_add_le vA vB
        linarith
      _ ≤ σ⁻¹^3 * E + ((σ⁻¹*a)*E + (σ⁻¹*b)*E + (σ⁻¹*c)*E) := by linarith
      _ = _ := by ring
  have hn2 := (sq_le_sq₀ (norm_nonneg dv) (by positivity :
    0 ≤ (σ⁻¹^3 + σ⁻¹*(a+b+c))*E)).mpr hn
  simpa only [mul_pow, hE2, EuclideanSpace.real_norm_sq_eq, dv, WithLp.ofLp_toLp] using hn2

/-- Literal b_e squared bound for a three-group edge, derived entirely from
stochastic normalization, Gram margins and the full tangent constraints. -/
theorem weight_tangent_square_bound
    (w dw : Z → ℝ) (A dA : X → Z → ℝ)
    (B dB : Y → Z → ℝ) (C dC : T → Z → ℝ)
    (w0 σ : ℝ) (hw0 : 0 < w0) (hσ : 0 < σ) (hw : ∀ z, w0 ≤ w z)
    (hwt : ∑ z, w z = 1)
    (hA : Gen.Uniqueness.Normalized A) (hAnonneg : ∀ x z, 0 ≤ A x z)
    (hB : Gen.Uniqueness.Normalized B) (hBnonneg : ∀ y z, 0 ≤ B y z)
    (hC : Gen.Uniqueness.Normalized C) (hCnonneg : ∀ t z, 0 ≤ C t z)
    (hdA : ∀ z, ∑ x, dA x z = 0) (hdB : ∀ z, ∑ y, dB y z = 0)
    (hdC : ∀ z, ∑ t, dC t z = 0)
    (hGA : ∀ v : Z → ℝ, σ^2 * (∑ z, (v z)^2) ≤ ∑ x, (∑ z, A x z * v z)^2)
    (hGB : ∀ v : Z → ℝ, σ^2 * (∑ z, (v z)^2) ≤ ∑ y, (∑ z, B y z * v z)^2)
    (hGC : ∀ v : Z → ℝ, σ^2 * (∑ z, (v z)^2) ≤ ∑ t, (∑ z, C t z * v z)^2) :
    (∑ z, (dw z)^2) ≤
      (σ⁻¹^3 + σ⁻¹ *
        ((1+Real.sqrt (Fintype.card X))/(w0*σ^2) +
         (1+Real.sqrt (Fintype.card Y))/(w0*σ^2) +
         (1+Real.sqrt (Fintype.card T))/(w0*σ^2)))^2 *
      ∑ x, ∑ y, ∑ t, (localDerivative w dw A dA B dB C dC x y t)^2 := by
  obtain ⟨LA,hLA,hLnA⟩ := exists_bounded_dual A σ hσ hGA
  obtain ⟨LB,hLB,hLnB⟩ := exists_bounded_dual B σ hσ hGB
  obtain ⟨LC,hLC,hLnC⟩ := exists_bounded_dual C σ hσ hGC
  obtain ⟨hAk,hBk,hCk⟩ := all_kernel_tangent_square_bounds w dw A dA B dB C dC
    w0 σ hw0 hσ hw hA hAnonneg hB hBnonneg hC hCnonneg hdA hdB hdC hGA hGB hGC
  apply weight_tangent_bound_of_kernel_bounds w dw A dA B dB C dC LA LB LC hLA hLB hLC
    σ _ _ _ hσ (by positivity) (by positivity) (by positivity) _ hLnA hLnB hLnC hAk hBk hCk
  intro z
  have hwn : ∀ z, 0 ≤ w z := fun z => (hw0.trans_le (hw z)).le
  exact ⟨hwn z, Gen.Constants.probability_coord_le_one w hwn hwt z⟩

#print axioms weight_tangent_square_bound
section Graph
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- Exact complete-coordinate component weights. -/
def weightBlock (x : Geometry.Ambient D Y r) (c : D.Component) (z : Fin r) : ℝ := x (.inl (c,z))
/-- Exact complete-coordinate group kernel. -/
def kernelBlock (x : Geometry.Ambient D Y r) (g : G) (y : Y g) (z : Fin r) : ℝ := x (.inr ⟨g,z,y⟩)

/-- A chosen ordering of one edge is used only for local three-way calculations. -/
def edgeDerivative (x v : Geometry.Ambient D Y r) (e : D.Edge)
    (s : Fin 3 ≃ D.GroupAt e) : Y (s 0).val → Y (s 1).val → Y (s 2).val → ℝ :=
  localDerivative (weightBlock D Y r x (D.component e)) (weightBlock D Y r v (D.component e))
    (kernelBlock D Y r x (s 0).val) (kernelBlock D Y r v (s 0).val)
    (kernelBlock D Y r x (s 1).val) (kernelBlock D Y r v (s 1).val)
    (kernelBlock D Y r x (s 2).val) (kernelBlock D Y r v (s 2).val)

/-- Bridge from the genuine complete-coordinate Frechet derivative to the
three-way local derivative used in the contraction proof. -/
theorem fderiv_edge_formula (x v : Geometry.Ambient D Y r) (e : D.Edge)
    (o : D.Outcome Y e) :
    (fderiv ℝ (Geometry.observation D Y r) x v) ⟨e,o⟩ =
      edgeDerivative D Y r x v e (Hessian.edgeEnumeration D e)
        (o (Hessian.edgeEnumeration D e 0)) (o (Hessian.edgeEnumeration D e 1))
        (o (Hessian.edgeEnumeration D e 2)) := by
  rw [Hessian.observation_first_derivative_cell]
  have hfin : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  simp only [Hessian.productD, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, EuclideanSpace.coe_proj]
  simp only [edgeDerivative, localDerivative, tensor]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have hi0 : Hessian.cellIndex D Y r e o z 0 = .inl (D.component e,z) := rfl
  have hi1 : Hessian.cellIndex D Y r e o z 1 =
      .inr ⟨(Hessian.edgeEnumeration D e 0).val,z,o (Hessian.edgeEnumeration D e 0)⟩ := rfl
  have hi2 : Hessian.cellIndex D Y r e o z 2 =
      .inr ⟨(Hessian.edgeEnumeration D e 1).val,z,o (Hessian.edgeEnumeration D e 1)⟩ := rfl
  have hi3 : Hessian.cellIndex D Y r e o z 3 =
      .inr ⟨(Hessian.edgeEnumeration D e 2).val,z,o (Hessian.edgeEnumeration D e 2)⟩ := rfl
  have he1 : ({0,1,2,3} : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have he2 : ({0,1,2,3} : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have he3 : ({0,1,2,3} : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  simp [hfin, he1, he2, he3, hi0, hi1, hi2, hi3, weightBlock, kernelBlock]
  ring

/-- Dependent three-coordinate product, used only to reindex the full outcome sum. -/
def triplePiEquiv (P : Fin 3 → Type*) : ((i : Fin 3) → P i) ≃ P 0 × P 1 × P 2 where
  toFun f := ⟨f 0,f 1,f 2⟩
  invFun p := Fin.cons p.1 (Fin.cons p.2.1 (Fin.cons p.2.2 (fun i => Fin.elim0 i)))
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl

def edgeOutcomeEquiv (e : D.Edge) (s : Fin 3 ≃ D.GroupAt e) :
    D.Outcome Y e ≃ Y (s 0).val × Y (s 1).val × Y (s 2).val :=
  (Equiv.piCongrLeft (fun g : D.GroupAt e => Y g.val) s).symm.trans
    (triplePiEquiv (fun i => Y (s i).val))

/-- Reindexing preserves every observation cell and its exact Euclidean square. -/
theorem edge_derivative_square_sum (x v : Geometry.Ambient D Y r) (e : D.Edge) :
    (∑ o, ((fderiv ℝ (Geometry.observation D Y r) x v) ⟨e,o⟩)^2) =
      ∑ a, ∑ b, ∑ c, (edgeDerivative D Y r x v e (Hessian.edgeEnumeration D e) a b c)^2 := by
  let s := Hessian.edgeEnumeration D e
  let q := edgeOutcomeEquiv D Y e s
  let J := edgeDerivative D Y r x v e s
  calc
    _ = ∑ o, (J (q o).1 (q o).2.1 (q o).2.2)^2 := by
      apply Finset.sum_congr rfl
      intro o _
      rw [fderiv_edge_formula D Y r x v e o]
      rfl
    _ = ∑ p : Y (s 0).val × Y (s 1).val × Y (s 2).val, (J p.1 p.2.1 p.2.2)^2 := by
      exact @Equiv.sum_comp _ _ ℝ _ _ _ q (fun p => (J p.1 p.2.1 p.2.2)^2)
    _ = _ := by simp only [Fintype.sum_prod_type]; rfl

/-- All local kernel estimates expressed directly in the full global coordinate array. -/
theorem edge_kernel_bounds (θ : Gen.Parameter D Y r) (v : Geometry.Ambient D Y r)
    (hv : v ∈ Geometry.tangent D Y r) (w0 σ : ℝ) (hw0 : 0 < w0) (hσ : 0 < σ)
    (hw : ∀ c z, w0 ≤ θ.weight c z)
    (hG : ∀ g (a : Fin r → ℝ), σ^2 * (∑ z, (a z)^2) ≤
      ∑ y, (∑ z, θ.kernel g y z * a z)^2)
    (e : D.Edge) (g : D.GroupAt e) :
    (∑ z, ∑ y, (v (.inr ⟨g.val,z,y⟩))^2) ≤
      (Gen.Constants.a (fun g => Fintype.card (Y g)) w0 σ g.val)^2 *
        ∑ o, ((fderiv ℝ (Geometry.observation D Y r) (Geometry.embed D Y r θ) v) ⟨e,o⟩)^2 := by
  let s := Hessian.edgeEnumeration D e
  have h := all_kernel_tangent_square_bounds
    (θ.weight (D.component e)) (weightBlock D Y r v (D.component e))
    (θ.kernel (s 0).val) (kernelBlock D Y r v (s 0).val)
    (θ.kernel (s 1).val) (kernelBlock D Y r v (s 1).val)
    (θ.kernel (s 2).val) (kernelBlock D Y r v (s 2).val)
    w0 σ hw0 hσ (hw (D.component e))
    (θ.kernel_total (s 0).val) (θ.kernel_nonneg (s 0).val)
    (θ.kernel_total (s 1).val) (θ.kernel_nonneg (s 1).val)
    (θ.kernel_total (s 2).val) (θ.kernel_nonneg (s 2).val)
    (hv.2 (s 0).val) (hv.2 (s 1).val) (hv.2 (s 2).val)
    (hG (s 0).val) (hG (s 1).val) (hG (s 2).val)
  rw [edge_derivative_square_sum]
  change _ ≤ _ * ∑ a, ∑ b, ∑ c, (edgeDerivative D Y r (Geometry.embed D Y r θ) v e s a b c)^2
  obtain ⟨i, rfl⟩ := s.surjective g
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- Literal b_e bound directly for the true full-coordinate observation derivative. -/
theorem edge_weight_bound (θ : Gen.Parameter D Y r) (v : Geometry.Ambient D Y r)
    (hv : v ∈ Geometry.tangent D Y r) (w0 σ : ℝ) (hw0 : 0 < w0) (hσ : 0 < σ)
    (hw : ∀ c z, w0 ≤ θ.weight c z)
    (hG : ∀ g (a : Fin r → ℝ), σ^2 * (∑ z, (a z)^2) ≤
      ∑ y, (∑ z, θ.kernel g y z * a z)^2)
    (e : D.Edge) :
    (∑ z, (v (.inl (D.component e,z)))^2) ≤
      (Gen.Constants.b (fun e : D.Edge => e.val) (fun g => Fintype.card (Y g)) w0 σ e)^2 *
        ∑ o, ((fderiv ℝ (Geometry.observation D Y r) (Geometry.embed D Y r θ) v) ⟨e,o⟩)^2 := by
  let s := Hessian.edgeEnumeration D e
  have h := weight_tangent_square_bound
    (θ.weight (D.component e)) (weightBlock D Y r v (D.component e))
    (θ.kernel (s 0).val) (kernelBlock D Y r v (s 0).val)
    (θ.kernel (s 1).val) (kernelBlock D Y r v (s 1).val)
    (θ.kernel (s 2).val) (kernelBlock D Y r v (s 2).val)
    w0 σ hw0 hσ (hw (D.component e)) (θ.weight_total (D.component e))
    (θ.kernel_total (s 0).val) (θ.kernel_nonneg (s 0).val)
    (θ.kernel_total (s 1).val) (θ.kernel_nonneg (s 1).val)
    (θ.kernel_total (s 2).val) (θ.kernel_nonneg (s 2).val)
    (hv.2 (s 0).val) (hv.2 (s 1).val) (hv.2 (s 2).val)
    (hG (s 0).val) (hG (s 1).val) (hG (s 2).val)
  rw [edge_derivative_square_sum]
  have hs : (∑ g ∈ e.val, Gen.Constants.a (fun g => Fintype.card (Y g)) w0 σ g) =
      Gen.Constants.a (fun g => Fintype.card (Y g)) w0 σ (s 0).val +
      Gen.Constants.a (fun g => Fintype.card (Y g)) w0 σ (s 1).val +
      Gen.Constants.a (fun g => Fintype.card (Y g)) w0 σ (s 2).val := by
    rw [← Finset.sum_coe_sort]
    rw [← s.sum_comp (fun g : D.GroupAt e => Gen.Constants.a (fun g => Fintype.card (Y g)) w0 σ g.val)]
    exact Fin.sum_univ_three _
  dsimp only [Gen.Constants.b]
  rw [hs]
  exact h

local instance edgeNonempty : Nonempty D.Edge := D.edge_nonempty

/-- One edge controls its weight block and all three complete kernel blocks. -/
theorem edge_parameter_square_bound (θ : Gen.Parameter D Y r) (v : Geometry.Ambient D Y r)
    (hv : v ∈ Geometry.tangent D Y r) (w0 σ : ℝ) (hw0 : 0 < w0) (hσ : 0 < σ)
    (hw : ∀ c z, w0 ≤ θ.weight c z)
    (hG : ∀ g (a : Fin r → ℝ), σ^2 * (∑ z, (a z)^2) ≤
      ∑ y, (∑ z, θ.kernel g y z * a z)^2)
    (e : D.Edge) :
    (∑ z, (v (.inl (D.component e,z)))^2) +
      (∑ g ∈ e.val, ∑ z, ∑ y, (v (.inr ⟨g,z,y⟩))^2) ≤
      (Gen.Constants.B (fun e : D.Edge => e.val) (fun g => Fintype.card (Y g)) w0 σ)^2 *
        ∑ o, ((fderiv ℝ (Geometry.observation D Y r) (Geometry.embed D Y r θ) v) ⟨e,o⟩)^2 := by
  let n := fun g => Fintype.card (Y g)
  let J2 := ∑ o, ((fderiv ℝ (Geometry.observation D Y r) (Geometry.embed D Y r θ) v) ⟨e,o⟩)^2
  have hlocal : (∑ z, (v (.inl (D.component e,z)))^2) +
      (∑ g ∈ e.val, ∑ z, ∑ y, (v (.inr ⟨g,z,y⟩))^2) ≤
      ((Gen.Constants.b (fun e : D.Edge => e.val) n w0 σ e)^2 +
        ∑ g ∈ e.val, (Gen.Constants.a n w0 σ g)^2) * J2 := by
    calc
      _ ≤ (Gen.Constants.b (fun e : D.Edge => e.val) n w0 σ e)^2 * J2 +
          ∑ g ∈ e.val, (Gen.Constants.a n w0 σ g)^2 * J2 := by
        apply add_le_add (edge_weight_bound D Y r θ v hv w0 σ hw0 hσ hw hG e)
        apply Finset.sum_le_sum
        intro g hg
        exact edge_kernel_bounds D Y r θ v hv w0 σ hw0 hσ hw hG e ⟨g,hg⟩
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hedge := Gen.Constants.edge_bound_le_B (fun e : D.Edge => e.val) n w0 σ e
  have hsq : (Gen.Constants.b (fun e : D.Edge => e.val) n w0 σ e)^2 +
      (∑ g ∈ e.val, (Gen.Constants.a n w0 σ g)^2) ≤
      (Gen.Constants.B (fun e : D.Edge => e.val) n w0 σ)^2 := by
    have hb := Gen.Constants.B_pos (fun e : D.Edge => e.val) n hw0 hσ
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _) hb.le).mpr hedge
    rwa [Real.sq_sqrt (by positivity)] at h
  exact hlocal.trans (mul_le_mul_of_nonneg_right hsq (by dsimp [J2]; positivity))

/-- Literal RATE-D2 lower singular bound on the exact homogeneous normalization
space, with global component weights and group kernels counted once. -/
theorem observation_jacobian_lower_bound (θ : Gen.Parameter D Y r) (v : Geometry.Ambient D Y r)
    (hv : v ∈ Geometry.tangent D Y r) (w0 σ : ℝ) (hw0 : 0 < w0) (hσ : 0 < σ)
    (hw : ∀ c z, w0 ≤ θ.weight c z)
    (hG : ∀ g (a : Fin r → ℝ), σ^2 * (∑ z, (a z)^2) ≤
      ∑ y, (∑ z, θ.kernel g y z * a z)^2) :
    Gen.Constants.kappa (fun e : D.Edge => e.val) (fun g => Fintype.card (Y g)) w0 σ * ‖v‖ ≤
      ‖fderiv ℝ (Geometry.observation D Y r) (Geometry.embed D Y r θ) v‖ := by
  classical
  let W2 := fun c : D.Component => ∑ z, (v (.inl (c,z)))^2
  let K2 := fun g : G => ∑ z, ∑ y, (v (.inr ⟨g,z,y⟩))^2
  let B := Gen.Constants.B (fun e : D.Edge => e.val) (fun g => Fintype.card (Y g)) w0 σ
  let J := fderiv ℝ (Geometry.observation D Y r) (Geometry.embed D Y r θ) v
  have hwcover : (∑ c, W2 c) ≤ ∑ e : D.Edge, W2 (D.component e) := by
    have h := Gen.Constants.covered_sum_le_sum_sum
      (fun e : D.Edge => {D.component e})
      (fun c => ⟨Gen.componentEdge c, by simp⟩) W2 (by intro c; dsimp [W2]; positivity)
    simpa using h
  have hkcover : (∑ g, K2 g) ≤ ∑ e : D.Edge, ∑ g ∈ e.val, K2 g :=
    Gen.Constants.covered_sum_le_sum_sum (fun e : D.Edge => e.val)
      (fun g => ⟨D.incident g, D.mem_incident g⟩) K2 (by intro g; dsimp [K2]; positivity)
  have hvnorm : ‖v‖^2 = (∑ c, W2 c) + ∑ g, K2 g := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma, W2, K2]
  have hJnorm : ‖J‖^2 = ∑ e, ∑ o, (J ⟨e,o⟩)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sigma]
  have hs : ‖v‖^2 ≤ B^2 * ‖J‖^2 := by
    rw [hvnorm, hJnorm]
    calc
      _ ≤ (∑ e : D.Edge, W2 (D.component e)) + ∑ e : D.Edge, ∑ g ∈ e.val, K2 g :=
        add_le_add hwcover hkcover
      _ = ∑ e : D.Edge, (W2 (D.component e) + ∑ g ∈ e.val, K2 g) :=
        Finset.sum_add_distrib.symm
      _ ≤ ∑ e : D.Edge, B^2 * ∑ o, (J ⟨e,o⟩)^2 := by
        apply Finset.sum_le_sum
        intro e _
        exact edge_parameter_square_bound D Y r θ v hv w0 σ hw0 hσ hw hG e
      _ = _ := by rw [Finset.mul_sum]
  exact Gen.Constants.inverse_from_squared_bound (norm_nonneg _) (norm_nonneg _)
    (Gen.Constants.B_pos (fun e : D.Edge => e.val) (fun g => Fintype.card (Y g)) hw0 hσ) hs

end Graph
#print axioms fderiv_edge_formula
#print axioms observation_jacobian_lower_bound
end Gen.Jacobian
