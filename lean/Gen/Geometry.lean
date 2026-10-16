import Gen.Graph
import Gen.Constants
import Gen.Rates

open scoped BigOperators Classical
noncomputable section
namespace Gen.Geometry

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- Each component weight and each group kernel entry occurs exactly once. -/
abbrev Coordinate := (D.Component × Fin r) ⊕ ((g : G) × (Fin r × Y g))
abbrev Ambient := EuclideanSpace ℝ (Coordinate D Y r)
abbrev ObservationSpace := EuclideanSpace ℝ ((e : D.Edge) × D.Outcome Y e)

def embed (θ : Gen.Parameter D Y r) : Ambient D Y r :=
  WithLp.toLp 2 (fun i => match i with
    | Sum.inl (c,z) => θ.weight c z
    | Sum.inr ⟨g,z,y⟩ => θ.kernel g y z)

@[simp] theorem embed_weight (θ : Gen.Parameter D Y r) (c) (z) :
    embed D Y r θ (.inl (c,z)) = θ.weight c z := rfl
@[simp] theorem embed_kernel (θ : Gen.Parameter D Y r) (g) (z) (y) :
    embed D Y r θ (.inr ⟨g,z,y⟩) = θ.kernel g y z := rfl

theorem embed_injective : Function.Injective (embed D Y r) := by
  intro θ η h
  apply Gen.Parameter.ext
  · funext c z; exact congrArg (fun x : Ambient D Y r => x (.inl (c,z))) h
  · funext g y z; exact congrArg (fun x : Ambient D Y r => x (.inr ⟨g,z,y⟩)) h

/-- Literal paper sum-of-squares metric, with no Pi supremum norm substituted. -/
theorem norm_sq_sub_embed (θ η : Gen.Parameter D Y r) :
    ‖embed D Y r θ - embed D Y r η‖ ^ 2 =
      (∑ c, ∑ z, (θ.weight c z - η.weight c z) ^ 2) +
      ∑ g, ∑ z, ∑ y, (θ.kernel g y z - η.kernel g y z) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma, embed]

/-- Coordinate permutation inducing the exact componentwise latent relabeling. -/
def coordinatePerm (q : Gen.W D r) : Equiv.Perm (Coordinate D Y r) where
  toFun i := match i with
    | Sum.inl (c,z) => Sum.inl (c,q c z)
    | Sum.inr ⟨g,z,y⟩ => Sum.inr ⟨g,q (D.groupComponent g) z,y⟩
  invFun i := match i with
    | Sum.inl (c,z) => Sum.inl (c,(q c).symm z)
    | Sum.inr ⟨g,z,y⟩ => Sum.inr ⟨g,(q (D.groupComponent g)).symm z,y⟩
  left_inv := by rintro (⟨c,z⟩ | ⟨g,z,y⟩) <;> simp
  right_inv := by rintro (⟨c,z⟩ | ⟨g,z,y⟩) <;> simp

/-- Library left action uses inverse pullback; the next bridge makes this explicit. -/
def actionLinear (q : Gen.W D r) : Ambient D Y r ≃ₗᵢ[ℝ] Ambient D Y r :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (coordinatePerm D Y r q)

instance ambientMulAction : MulAction (Gen.W D r) (Ambient D Y r) where
  smul q x := actionLinear D Y r q x
  one_smul x := by
    ext i
    rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;> rfl
  mul_smul q p x := by
    ext i
    rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;> rfl

instance ambientIsometric : IsIsometricSMul (Gen.W D r) (Ambient D Y r) where
  isometry_smul q := (actionLinear D Y r q).isometry

/-- The original paper right pullback is not silently commuted or changed. -/
theorem embed_permute (θ : Gen.Parameter D Y r) (q : Gen.W D r) :
    embed D Y r (θ.permute q) = q⁻¹ • embed D Y r θ := by
  ext i
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;> rfl

/-- Affine normalization constraints are imposed on every block. -/
def Normalized (x : Ambient D Y r) : Prop :=
  (∀ c, ∑ z, x (.inl (c,z)) = 1) ∧
  ∀ g z, ∑ y, x (.inr ⟨g,z,y⟩) = 1

/-- The full homogeneous normalization tangent space. -/
def tangent : Submodule ℝ (Ambient D Y r) where
  carrier v := (∀ c, ∑ z, v (.inl (c,z)) = 0) ∧
    ∀ g z, ∑ y, v (.inr ⟨g,z,y⟩) = 0
  zero_mem' := by
    constructor
    · intro c; simp
    · intro g z; simp
  add_mem' := by
    rintro u v ⟨hu,huk⟩ ⟨hv,hvk⟩
    constructor
    · intro c; simp [Finset.sum_add_distrib, hu, hv]
    · intro g z; simp [Finset.sum_add_distrib, huk, hvk]
  smul_mem' := by
    rintro a v ⟨hv,hvk⟩
    constructor
    · intro c; simp [← Finset.mul_sum, hv]
    · intro g z; simp [← Finset.mul_sum, hvk]

theorem embed_normalized (θ : Gen.Parameter D Y r) : Normalized D Y r (embed D Y r θ) :=
  ⟨θ.weight_total, θ.kernel_total⟩

theorem sub_mem_tangent {x y : Ambient D Y r}
    (hx : Normalized D Y r x) (hy : Normalized D Y r y) :
    x-y ∈ tangent D Y r := by
  constructor
  · intro c; simp [Finset.sum_sub_distrib, hx.1 c, hy.1 c]
  · intro g z; simp [Finset.sum_sub_distrib, hx.2 g z, hy.2 g z]

/-- The actual observation polynomial on the complete ambient real vector space. -/
def observation (x : Ambient D Y r) : ObservationSpace D Y :=
  WithLp.toLp 2 (fun ex => ∑ z, x (.inl (D.component ex.1,z)) *
    ∏ g : D.GroupAt ex.1, x (.inr ⟨g.val,z,ex.2 g⟩))

theorem observation_embed (θ : Gen.Parameter D Y r) :
    observation D Y r (embed D Y r θ) =
      Gen.Rates.stack (fun e => θ.observation e) := rfl

/-- Every cell is a quartic polynomial; smoothness holds off the simplex as well. -/
theorem observation_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n (observation D Y r) := by
  rw [contDiff_piLp]
  intro ex
  change ContDiff ℝ n (fun x : Ambient D Y r => ∑ z,
    x (.inl (D.component ex.1,z)) * ∏ g : D.GroupAt ex.1, x (.inr ⟨g.val,z,ex.2 g⟩))
  fun_prop

theorem observation_continuous : Continuous (observation D Y r) :=
  (observation_contDiff D Y r 0).continuous

/-- Full stochastic block diameter, counting components and kernels only once. -/
theorem parameter_diameter (θ η : Gen.Parameter D Y r) :
    ‖embed D Y r θ - embed D Y r η‖ ≤
      Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) := by
  have hs : ‖embed D Y r θ - embed D Y r η‖ ^ 2 ≤
      2 * ((Fintype.card D.Component : ℝ) + r * Fintype.card G) := by
    rw [norm_sq_sub_embed]
    calc
      _ ≤ (∑ _c : D.Component, (2:ℝ)) + ∑ _g : G, ∑ _z : Fin r, (2:ℝ) := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro c _
          exact Gen.Constants.probability_distance_square_sum_le_two _ _
            (fun z => (θ.weight_pos c z).le) (fun z => (η.weight_pos c z).le)
            (θ.weight_total c) (η.weight_total c)
        · apply Finset.sum_le_sum
          intro g _
          apply Finset.sum_le_sum
          intro z _
          exact Gen.Constants.probability_distance_square_sum_le_two _ _
            (fun y => θ.kernel_nonneg g y z) (fun y => η.kernel_nonneg g y z)
            (θ.kernel_total g z) (η.kernel_total g z)
      _ = _ := by simp; ring
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2 hs

end Gen.Geometry
