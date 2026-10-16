import Gen.Geometry
import Gen.RateBridge

open scoped BigOperators Classical
noncomputable section
namespace Gen.Hessian

/-- Finite Schur bound in literal Euclidean norms, with no latent-count factor. -/
theorem bilinear_row_column_bound {I : Type*} [Fintype I]
    (H : I → I → ℝ) (u v : EuclideanSpace ℝ I) {M : ℝ} (hM : 0 ≤ M)
    (hrow : ∀ i, ∑ j, |H i j| ≤ M) (hcol : ∀ j, ∑ i, |H i j| ≤ M) :
    |∑ i, ∑ j, H i j * u i * v j| ≤ M * ‖u‖ * ‖v‖ := by
  let a : I × I → ℝ := fun ij => Real.sqrt |H ij.1 ij.2| * |u ij.1|
  let b : I × I → ℝ := fun ij => Real.sqrt |H ij.1 ij.2| * |v ij.2|
  have ha : (∑ ij, a ij ^ 2) ≤ M * ‖u‖ ^ 2 := by
    simp only [a, mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs, Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul]
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
  have hb : (∑ ij, b ij ^ 2) ≤ M * ‖v‖ ^ 2 := by
    simp only [b, mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _))
  have hab : (∑ ij, a ij * b ij) ^ 2 ≤ M ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
    have hprod := mul_le_mul ha hb (Finset.sum_nonneg (fun ij _ => sq_nonneg (b ij)))
      (mul_nonneg hM (sq_nonneg ‖u‖))
    nlinarith
  have hn : ∑ ij, a ij * b ij ≤ M * ‖u‖ * ‖v‖ := by
    have hnM : 0 ≤ M * ‖u‖ * ‖v‖ := by positivity
    nlinarith
  calc
    |∑ i, ∑ j, H i j * u i * v j| ≤ ∑ i, ∑ j, |H i j * u i * v j| := by
      calc
        _ ≤ ∑ i, |∑ j, H i j * u i * v j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ ij, a ij * b ij := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [a,b]
      rw [abs_mul, abs_mul]
      calc
        |H i j| * |u i| * |v j| = (Real.sqrt |H i j|) ^ 2 * |u i| * |v j| := by
          rw [Real.sq_sqrt (abs_nonneg (H i j))]
        _ = _ := by ring
    _ ≤ _ := hn

section Products
variable {A Z I : Type*} [Fintype A] [Fintype Z] [Fintype I] [DecidableEq I]
abbrev Vector := EuclideanSpace ℝ A

def productSum (idx : Z → I → A) (x : Vector (A := A)) : ℝ :=
  ∑ z, ∏ i, x (idx z i)
def productD (idx : Z → I → A) (x : Vector (A := A)) : Vector (A := A) →L[ℝ] ℝ :=
  ∑ z, ∑ i, (∏ j ∈ Finset.univ.erase i, x (idx z j)) • EuclideanSpace.proj (𝕜 := ℝ) (idx z i)
def productD2 (idx : Z → I → A) (x : Vector (A := A)) :
    Vector (A := A) →L[ℝ] (Vector (A := A) →L[ℝ] ℝ) :=
  ∑ z, ∑ i, (∑ j ∈ Finset.univ.erase i,
    (∏ k ∈ (Finset.univ.erase i).erase j, x (idx z k)) • EuclideanSpace.proj (𝕜 := ℝ) (idx z j)).smulRight
      (EuclideanSpace.proj (𝕜 := ℝ) (idx z i))

theorem product_hasFDerivAt (idx : Z → I → A) (x : Vector (A := A)) :
    HasFDerivAt (productSum idx) (productD idx x) x := by
  apply HasFDerivAt.fun_sum
  intro z _
  exact HasFDerivAt.finsetProd (fun i _ => by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) (idx z i)).hasFDerivAt (x := x))

theorem productD_hasFDerivAt (idx : Z → I → A) (x : Vector (A := A)) :
    HasFDerivAt (productD idx) (productD2 idx x) x := by
  apply HasFDerivAt.fun_sum
  intro z _
  apply HasFDerivAt.fun_sum
  intro i _
  have hp := HasFDerivAt.finsetProd (u := Finset.univ.erase i) (x := x)
    (g := fun j (x : Vector (A := A)) => x (idx z j))
    (g' := fun j => EuclideanSpace.proj (𝕜 := ℝ) (idx z j))
    (fun j _ => by simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) (idx z j)).hasFDerivAt (x := x))
  convert! hp.smul (hasFDerivAt_const (EuclideanSpace.proj (𝕜 := ℝ) (idx z i)) x) using 1
  simp only [smul_zero, zero_add]

/-- The explicit second derivative, over all ambient directions and all real x. -/
theorem productD2_apply (idx : Z → I → A) (x u v : Vector (A := A)) :
    productD2 idx x u v = ∑ z, ∑ i, ∑ j ∈ Finset.univ.erase i,
      (∏ k ∈ (Finset.univ.erase i).erase j, x (idx z k)) * u (idx z j) * v (idx z i) := by
  simp only [productD2, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, EuclideanSpace.coe_proj, Finset.sum_mul]

end Products

section Quartic
variable {A Z : Type*} [Fintype A] [Fintype Z]

def quarticH (idx : Z → Fin 4 → A) (x : Vector (A := A)) (s t : Z × Fin 4) : ℝ :=
  if s.1 = t.1 then
    if s.2 = t.2 then 0 else ∏ k ∈ (Finset.univ.erase s.2).erase t.2, x (idx s.1 k)
  else 0

lemma quarticH_symmetric (idx : Z → Fin 4 → A) (x : Vector (A := A)) (s t : Z × Fin 4) :
    quarticH idx x s t = quarticH idx x t s := by
  rcases s with ⟨z,i⟩; rcases t with ⟨w,j⟩
  by_cases h : z = w
  · subst w
    by_cases hij : i = j
    · subst j; simp [quarticH]
    · simp only [quarticH, if_true, if_neg hij, if_neg (Ne.symm hij)]
      congr 1
      ext k
      simp [and_comm, and_left_comm]
  · simp [quarticH, h, Ne.symm h]

lemma quartic_coefficient_bound (idx : Z → Fin 4 → A) (x : Vector (A := A))
    (hx : ∀ z i, |x (idx z i)| ≤ 2) (z : Z) (i j : Fin 4) (hij : i ≠ j) :
    |∏ k ∈ (Finset.univ.erase i).erase j, x (idx z k)| ≤ 4 := by
  have hj : j ∈ (Finset.univ : Finset (Fin 4)).erase i := by simp [hij, Ne.symm hij]
  calc
    |∏ k ∈ (Finset.univ.erase i).erase j, x (idx z k)| =
        ∏ k ∈ (Finset.univ.erase i).erase j, |x (idx z k)| := Finset.abs_prod _ _
    _ ≤ ∏ _k ∈ (Finset.univ.erase i).erase j, (2:ℝ) :=
      Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k _ => hx z k)
    _ = 4 := by
      rw [Finset.prod_const, Finset.card_erase_of_mem hj,
        Finset.card_erase_of_mem (Finset.mem_univ i)]
      norm_num

lemma quarticH_row_bound (idx : Z → Fin 4 → A) (x : Vector (A := A))
    (hx : ∀ z i, |x (idx z i)| ≤ 2) (s : Z × Fin 4) :
    ∑ t, |quarticH idx x s t| ≤ 12 := by
  rcases s with ⟨z,i⟩
  simp only [Fintype.sum_prod_type]
  have hz : (∑ w, ∑ j : Fin 4, |quarticH idx x (z,i) (w,j)|) =
      ∑ j : Fin 4, |if i = j then (0:ℝ) else
        ∏ k ∈ (Finset.univ.erase i).erase j, x (idx z k)| := by
    rw [Finset.sum_eq_single z]
    · simp [quarticH]
    · intro w _ hw; simp [quarticH, Ne.symm hw]
    · simp
  rw [hz]
  calc
    _ ≤ ∑ j : Fin 4, if i = j then (0:ℝ) else 4 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp [hij]
      · simpa [hij] using quartic_coefficient_bound idx x hx z i j hij
    _ = 12 := by
      have hite (j : Fin 4) : (if i = j then (0:ℝ) else 4) =
          4 - (if i = j then 4 else 0) := by split_ifs <;> norm_num
      simp_rw [hite, Finset.sum_sub_distrib]
      norm_num

lemma quarticH_col_bound (idx : Z → Fin 4 → A) (x : Vector (A := A))
    (hx : ∀ z i, |x (idx z i)| ≤ 2) (t : Z × Fin 4) :
    ∑ s, |quarticH idx x s t| ≤ 12 := by
  simp_rw [quarticH_symmetric idx x _ t]
  exact quarticH_row_bound idx x hx t

/-- Coordinate restriction is contractive when no coordinate is duplicated. -/
lemma restriction_norm_le {B : Type*} [Fintype B] (f : B → A)
    (hf : Function.Injective f) (u : Vector (A := A)) :
    ‖(WithLp.toLp 2 (fun b => u (f b)) : EuclideanSpace ℝ B)‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ b, u (f b) ^ 2) = ∑ a ∈ Finset.univ.image f, u a ^ 2 := by
      rw [Finset.sum_image]
      exact fun a _ b _ hab => hf hab
    _ ≤ ∑ a, u a ^ 2 := Finset.sum_le_univ_sum_of_nonneg (fun a => sq_nonneg _)

lemma productD2_eq_block (idx : Z → Fin 4 → A) (x u v : Vector (A := A)) :
    productD2 idx x u v = ∑ s : Z × Fin 4, ∑ t : Z × Fin 4,
      quarticH idx x s t * u (idx s.1 s.2) * v (idx t.1 t.2) := by
  rw [productD2_apply]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  have hr : (∑ i : Fin 4, ∑ w : Z, ∑ j : Fin 4,
      quarticH idx x (z,i) (w,j) * u (idx z i) * v (idx w j)) =
      ∑ i : Fin 4, ∑ j : Fin 4, (if i = j then (0:ℝ) else
        ∏ k ∈ (Finset.univ.erase i).erase j, x (idx z k)) * u (idx z i) * v (idx z j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single z]
    · simp [quarticH]
    · intro w _ hw; simp [quarticH, Ne.symm hw]
    · simp
  rw [hr, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [ite_true, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hji := (Finset.mem_erase.mp hj).1
  simp only [if_neg hji]
  have hs : (Finset.univ.erase j).erase i = (Finset.univ.erase i).erase j := by
    ext k; simp [and_comm, and_left_comm]
  rw [hs]

/-- The exact scalar quartic Hessian bound 12, uniform in latent count and valid
    for negative off-simplex coordinates satisfying |x_i|≤2. -/
theorem quartic_hessian_bound (idx : Z → Fin 4 → A)
    (hinj : Function.Injective (fun s : Z × Fin 4 => idx s.1 s.2))
    (x u v : Vector (A := A)) (hx : ∀ z i, |x (idx z i)| ≤ 2) :
    ‖productD2 idx x u v‖ ≤ 12 * ‖u‖ * ‖v‖ := by
  let u' : EuclideanSpace ℝ (Z × Fin 4) := WithLp.toLp 2 (fun s => u (idx s.1 s.2))
  let v' : EuclideanSpace ℝ (Z × Fin 4) := WithLp.toLp 2 (fun s => v (idx s.1 s.2))
  have h := bilinear_row_column_bound (quarticH idx x) u' v' (by norm_num : (0:ℝ) ≤ 12)
    (quarticH_row_bound idx x hx) (quarticH_col_bound idx x hx)
  rw [Real.norm_eq_abs, productD2_eq_block]
  change |∑ s, ∑ t, quarticH idx x s t * u' s * v' t| ≤ _
  calc
    _ ≤ 12 * ‖u'‖ * ‖v'‖ := h
    _ ≤ 12 * ‖u‖ * ‖v‖ := by
      gcongr
      · exact restriction_norm_le _ hinj u
      · exact restriction_norm_le _ hinj v

end Quartic

section Observation
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- Enumerating a triple changes no mathematical observation coordinates. -/
def edgeEnumeration (e : D.Edge) : Fin 3 ≃ D.GroupAt e :=
  (Fintype.equivFinOfCardEq (by simpa [Ext.TripleDesign.GroupAt] using D.edge_card e.val e.property)).symm

def cellIndex (e : D.Edge) (y : D.Outcome Y e) (z : Fin r) : Fin 4 → Gen.Geometry.Coordinate D Y r :=
  Fin.cases (.inl (D.component e,z))
    (fun i => .inr ⟨(edgeEnumeration D e i).val,z,y (edgeEnumeration D e i)⟩)

lemma cellIndex_injective (e : D.Edge) (y : D.Outcome Y e) :
    Function.Injective (fun p : Fin r × Fin 4 => cellIndex D Y r e y p.1 p.2) := by
  rintro ⟨z,i⟩ ⟨w,j⟩ h
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      have he : (D.component e,z) = (D.component e,w) := Sum.inl.inj h
      exact Prod.ext (congrArg Prod.snd he) rfl
    | succ j => simp [cellIndex] at h
  | succ i =>
    cases j using Fin.cases with
    | zero => simp [cellIndex] at h
    | succ j =>
      have he := Sum.inr.inj h
      have hg : (edgeEnumeration D e i).val = (edgeEnumeration D e j).val := congrArg Sigma.fst he
      have hij : i = j := (edgeEnumeration D e).injective (Subtype.ext hg)
      subst j
      have hz : z = w := by
        have hh := congrArg (fun a : (g : G) × (Fin r × Y g) => a.2.1) he
        exact hh
      exact Prod.ext hz rfl

lemma observation_cell_as_product (x : Gen.Geometry.Ambient D Y r)
    (e : D.Edge) (y : D.Outcome Y e) :
    Gen.Geometry.observation D Y r x ⟨e,y⟩ = productSum (cellIndex D Y r e y) x := by
  change (∑ z, x (.inl (D.component e,z)) * ∏ g : D.GroupAt e,
    x (.inr ⟨g.val,z,y g⟩)) = ∑ z, ∏ i, x (cellIndex D Y r e y z i)
  apply Finset.sum_congr rfl
  intro z _
  rw [Fin.prod_univ_succ]
  change x (.inl (D.component e,z)) * (∏ g : D.GroupAt e, x (.inr ⟨g.val,z,y g⟩)) =
    x (.inl (D.component e,z)) * (∏ i : Fin 3, x (.inr ⟨(edgeEnumeration D e i).val,z,y (edgeEnumeration D e i)⟩))
  congr 1
  exact ((edgeEnumeration D e).prod_comp
    (fun g : D.GroupAt e => x (.inr ⟨g.val,z,y g⟩))).symm

lemma stochastic_coordinate_bounds (θ : Gen.Parameter D Y r) (i : Gen.Geometry.Coordinate D Y r) :
    0 ≤ Gen.Geometry.embed D Y r θ i ∧ Gen.Geometry.embed D Y r θ i ≤ 1 := by
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩
  · exact ⟨(θ.weight_pos c z).le, Gen.Constants.probability_coord_le_one _
      (fun z => (θ.weight_pos c z).le) (θ.weight_total c) z⟩
  · exact ⟨θ.kernel_nonneg g y z, Gen.Constants.probability_coord_le_one _
      (fun y => θ.kernel_nonneg g y z) (θ.kernel_total g z) y⟩

/-- The whole ambient unit ball, including negative nonstochastic x, has |x_i|≤2. -/
lemma affine_ball_coordinate_bound (θ : Gen.Parameter D Y r) (x : Gen.Geometry.Ambient D Y r)
    (hx : ‖x - Gen.Geometry.embed D Y r θ‖ ≤ 1) (i : Gen.Geometry.Coordinate D Y r) :
    |x i| ≤ 2 := by
  have hcoord := PiLp.norm_apply_le (x - Gen.Geometry.embed D Y r θ) i
  change |x i - Gen.Geometry.embed D Y r θ i| ≤ ‖x - Gen.Geometry.embed D Y r θ‖ at hcoord
  have hb := stochastic_coordinate_bounds D Y r θ i
  have htri := abs_add_le (x i - Gen.Geometry.embed D Y r θ i) (Gen.Geometry.embed D Y r θ i)
  rw [sub_add_cancel, abs_of_nonneg hb.1] at htri
  linarith

/-- The first derivative coordinate of the original observation polynomial. -/
lemma observation_first_derivative_cell (x u : Gen.Geometry.Ambient D Y r)
    (e : D.Edge) (y : D.Outcome Y e) :
    (fderiv ℝ (Gen.Geometry.observation D Y r) x u) ⟨e,y⟩ =
      productD (cellIndex D Y r e y) x u := by
  let P : Gen.Geometry.ObservationSpace D Y →L[ℝ] ℝ := EuclideanSpace.proj ⟨e,y⟩
  have h := P.hasFDerivAt.comp x (Gen.RateBridge.observation_hasFDerivAt D Y r x)
  have hfun : (P ∘ Gen.Geometry.observation D Y r) = productSum (cellIndex D Y r e y) := by
    funext b; exact observation_cell_as_product D Y r b e y
  rw [hfun] at h
  have heq := h.unique (product_hasFDerivAt _ _)
  exact congrArg (fun L => L u) heq

/-- The computed scalar Hessian is the coordinate of the genuine second Frechet
    derivative of the original full observation map. -/
lemma observation_second_derivative_cell (x u v : Gen.Geometry.Ambient D Y r)
    (e : D.Edge) (y : D.Outcome Y e) :
    (fderiv ℝ (fderiv ℝ (Gen.Geometry.observation D Y r)) x u v) ⟨e,y⟩ =
      productD2 (cellIndex D Y r e y) x u v := by
  let P : Gen.Geometry.ObservationSpace D Y →L[ℝ] ℝ := EuclideanSpace.proj ⟨e,y⟩
  have hfirst (a : Gen.Geometry.Ambient D Y r) :
      P.comp (fderiv ℝ (Gen.Geometry.observation D Y r) a) =
        productD (cellIndex D Y r e y) a := by
    have h := P.hasFDerivAt.comp a (Gen.RateBridge.observation_hasFDerivAt D Y r a)
    have hfun : (P ∘ Gen.Geometry.observation D Y r) = productSum (cellIndex D Y r e y) := by
      funext b; exact observation_cell_as_product D Y r b e y
    rw [hfun] at h
    exact h.unique (product_hasFDerivAt _ _)
  let C := ContinuousLinearMap.compL ℝ (Gen.Geometry.Ambient D Y r)
    (Gen.Geometry.ObservationSpace D Y) ℝ P
  have hsecond := C.hasFDerivAt.comp x (Gen.RateBridge.observation_derivative_hasFDerivAt D Y r x)
  have hfun : (C ∘ fderiv ℝ (Gen.Geometry.observation D Y r)) =
      productD (cellIndex D Y r e y) := funext hfirst
  rw [hfun] at hsecond
  have heq := hsecond.unique (productD_hasFDerivAt _ _)
  exact congrArg (fun L => L u v) heq

/-- Literal RATE-D2 Hessian constant, on the full ambient unit ball. Its restriction
    to A0 and V is immediate and does not exclude zero kernels or negative x. -/
theorem observation_hessian_bound (θ : Gen.Parameter D Y r)
    (x u v : Gen.Geometry.Ambient D Y r)
    (hx : ‖x - Gen.Geometry.embed D Y r θ‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (Gen.Geometry.observation D Y r)) x u v‖ ≤
      (12 * Real.sqrt (Fintype.card ((e : D.Edge) × D.Outcome Y e))) * ‖u‖ * ‖v‖ := by
  have hcell (ex : (e : D.Edge) × D.Outcome Y e) :
      |(fderiv ℝ (fderiv ℝ (Gen.Geometry.observation D Y r)) x u v) ex| ≤ 12 * ‖u‖ * ‖v‖ := by
    rcases ex with ⟨e,y⟩
    rw [observation_second_derivative_cell D Y r]
    exact quartic_hessian_bound _ (cellIndex_injective D Y r e y) x u v
      (fun z i => affine_ball_coordinate_bound D Y r θ x hx _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _ex : (e : D.Edge) × D.Outcome Y e, (12 * ‖u‖ * ‖v‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro ex _
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hcell ex)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring

end Observation

end Gen.Hessian
