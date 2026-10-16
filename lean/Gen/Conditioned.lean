import Gen.Geometry
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped BigOperators Classical
noncomputable section
namespace Gen.Conditioned

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- The exact quadratic Gram lower margin, allowing zero kernel entries. -/
def GramMargin {Z O : Type*} [Fintype Z] [Fintype O] (σ : ℝ) (L : O → Z → ℝ) : Prop :=
  ∀ v : Z → ℝ, σ ^ 2 * (∑ z, (v z) ^ 2) ≤ ∑ y, (∑ z, L y z * v z) ^ 2

/-- RATE-D1's full closed real coordinate set. -/
def K (w₀ σ : ℝ) : Set (Geometry.Ambient D Y r) :=
  {x | Geometry.Normalized D Y r x ∧
    (∀ c z, w₀ ≤ x (.inl (c,z))) ∧
    (∀ g z y, 0 ≤ x (.inr ⟨g,z,y⟩)) ∧
    ∀ g, GramMargin σ (fun y z => x (.inr ⟨g,z,y⟩))}

variable {D Y r}

def toParameter {w₀ σ : ℝ} (hw : 0 < w₀) (x : Geometry.Ambient D Y r)
    (hx : x ∈ K D Y r w₀ σ) : Parameter D Y r where
  weight c z := x (.inl (c,z))
  weight_pos c z := hw.trans_le (hx.2.1 c z)
  weight_total c := hx.1.1 c
  kernel g y z := x (.inr ⟨g,z,y⟩)
  kernel_nonneg g y z := hx.2.2.1 g z y
  kernel_total g z := hx.1.2 g z

@[simp] theorem embed_toParameter {w₀ σ : ℝ} (hw : 0 < w₀)
    (x : Geometry.Ambient D Y r) (hx : x ∈ K D Y r w₀ σ) :
    Geometry.embed D Y r (toParameter hw x hx) = x := by
  ext i
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;> rfl

theorem mem_K_embed_iff (θ : Parameter D Y r) (w₀ σ : ℝ) :
    Geometry.embed D Y r θ ∈ K D Y r w₀ σ ↔
      (∀ c z, w₀ ≤ θ.weight c z) ∧ ∀ g, GramMargin σ (θ.kernel g) := by
  constructor
  · intro h; exact ⟨h.2.1, h.2.2.2⟩
  · rintro ⟨hw, hg⟩
    exact ⟨Geometry.embed_normalized D Y r θ, hw, fun g z y => θ.kernel_nonneg g y z, hg⟩

private theorem closed_forall {X I : Type*} [TopologicalSpace X]
    (p : I → X → Prop) (h : ∀ i, IsClosed {x | p i x}) : IsClosed {x | ∀ i, p i x} := by
  rw [Set.setOf_forall]
  exact isClosed_iInter h

theorem isClosed_K (w₀ σ : ℝ) : IsClosed (K D Y r w₀ σ) := by
  apply IsClosed.inter
  · apply IsClosed.inter
    · apply closed_forall
      intro c
      apply isClosed_eq <;> fun_prop
    · apply closed_forall
      intro g
      apply closed_forall
      intro z
      apply isClosed_eq <;> fun_prop
  · apply IsClosed.inter
    · apply closed_forall
      intro c
      apply closed_forall
      intro z
      apply isClosed_le <;> fun_prop
    · apply IsClosed.inter
      · apply closed_forall
        intro g
        apply closed_forall
        intro z
        apply closed_forall
        intro y
        apply isClosed_le <;> fun_prop
      · apply closed_forall
        intro g
        apply closed_forall
        intro v
        apply isClosed_le <;> fun_prop

lemma coordinate_mem_Icc {w₀ σ : ℝ} (hw : 0 ≤ w₀) {x : Geometry.Ambient D Y r}
    (hx : x ∈ K D Y r w₀ σ) (i : Geometry.Coordinate D Y r) : x i ∈ Set.Icc (0:ℝ) 1 := by
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩
  · exact ⟨hw.trans (hx.2.1 c z), by
      rw [← hx.1.1 c]
      exact Finset.single_le_sum (fun j _ => hw.trans (hx.2.1 c j)) (Finset.mem_univ z)⟩
  · exact ⟨hx.2.2.1 g z y, by
      rw [← hx.1.2 g z]
      exact Finset.single_le_sum (fun j _ => hx.2.2.1 g z j) (Finset.mem_univ y)⟩

theorem norm_le_sqrt_dimension {w₀ σ : ℝ} (hw : 0 ≤ w₀)
    {x : Geometry.Ambient D Y r} (hx : x ∈ K D Y r w₀ σ) :
    ‖x‖ ≤ Real.sqrt (Fintype.card (Geometry.Coordinate D Y r)) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Geometry.Coordinate D Y r, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := coordinate_mem_Icc hw hx i
      nlinarith [h.1, h.2]
    _ = _ := by simp

theorem isCompact_K {w₀ σ : ℝ} (hw : 0 ≤ w₀) : IsCompact (K D Y r w₀ σ) := by
  apply (isCompact_closedBall (0 : Geometry.Ambient D Y r)
    (Real.sqrt (Fintype.card (Geometry.Coordinate D Y r)))).of_isClosed_subset (isClosed_K w₀ σ)
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_le_sqrt_dimension hw hx


lemma GramMargin.permute {Z O : Type*} [Fintype Z] [Fintype O]
    {σ : ℝ} {L : O → Z → ℝ} (h : GramMargin σ L) (q : Equiv.Perm Z) :
    GramMargin σ (fun y z => L y (q z)) := by
  intro v
  have hv := h (fun z => v (q⁻¹ z))
  have hs : (∑ z, (v (q⁻¹ z)) ^ 2) = ∑ z, (v z) ^ 2 :=
    Equiv.sum_comp q⁻¹ (fun z => (v z) ^ 2)
  rw [hs] at hv
  convert hv using 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  have he := Equiv.sum_comp q (fun z => L y z * v (q⁻¹ z))
  simpa using he

theorem permute_mem_K (θ : Parameter D Y r) {w₀ σ : ℝ}
    (hθ : Geometry.embed D Y r θ ∈ K D Y r w₀ σ) (q : W D r) :
    Geometry.embed D Y r (θ.permute q) ∈ K D Y r w₀ σ := by
  rw [mem_K_embed_iff] at hθ ⊢
  exact ⟨fun c z => hθ.1 c (q c z), fun g => (hθ.2 g).permute (q (D.groupComponent g))⟩

/-- W invariance on the actual Euclidean closed set; Geometry's left action is inverse pullback. -/
theorem smul_mem_K {w₀ σ : ℝ} (hw : 0 < w₀) {x : Geometry.Ambient D Y r}
    (hx : x ∈ K D Y r w₀ σ) (q : W D r) : q • x ∈ K D Y r w₀ σ := by
  have h := permute_mem_K (toParameter hw x hx) (by simpa using hx) q⁻¹
  simpa only [Geometry.embed_permute, inv_inv, embed_toParameter] using h

def identityKernel {O : Type*} [Fintype O] (ι : Fin r ↪ O) (y : O) (z : Fin r) : ℝ :=
  if y = ι z then 1 else 0

lemma identityKernel_total {O : Type*} [Fintype O] (ι : Fin r ↪ O) (z : Fin r) :
    ∑ y, identityKernel ι y z = 1 := by simp [identityKernel]

lemma identityKernel_contract {O : Type*} [Fintype O] (ι : Fin r ↪ O)
    (v : Fin r → ℝ) (z : Fin r) :
    ∑ j, identityKernel ι (ι z) j * v j = v z := by
  simp [identityKernel, ι.injective.eq_iff, eq_comm]

lemma identityKernel_gram {O : Type*} [Fintype O] (ι : Fin r ↪ O) {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) : GramMargin σ (identityKernel ι) := by
  intro v
  have hσ : σ ^ 2 ≤ 1 := by nlinarith
  calc
    σ ^ 2 * ∑ z, (v z) ^ 2 ≤ ∑ z, (v z) ^ 2 :=
      mul_le_of_le_one_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hσ
    _ = ∑ y ∈ Finset.univ.image ι, (∑ z, identityKernel ι y z * v z) ^ 2 := by
      rw [Finset.sum_image]
      · simp only [identityKernel_contract]
      · exact fun _ _ _ _ h => ι.injective h
    _ ≤ ∑ y, (∑ z, identityKernel ι y z * v z) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)

/-- The literal normalized identity-column witness, with all real zeros retained. -/
def uniformEmbedding (hr : 0 < r) (ι : ∀ g, Fin r ↪ Y g) : Parameter D Y r where
  weight _ _ := 1 / r
  weight_pos _ _ := one_div_pos.mpr (Nat.cast_pos.mpr hr)
  weight_total _ := by simp [ne_of_gt hr]
  kernel g := identityKernel (ι g)
  kernel_nonneg g y z := by unfold identityKernel; split_ifs <;> norm_num
  kernel_total g := identityKernel_total (ι g)

theorem uniformEmbedding_mem_K (hr : 0 < r) (ι : ∀ g, Fin r ↪ Y g)
    {w₀ σ : ℝ} (hw : w₀ ≤ 1 / r) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    Geometry.embed D Y r (uniformEmbedding hr ι) ∈ K D Y r w₀ σ := by
  rw [mem_K_embed_iff]
  exact ⟨fun _ _ => hw, fun g => identityKernel_gram (ι g) hσ0 hσ1⟩

/-- RATE-D1 nonemptiness for every allowed finite alphabet size and conditioning input. -/
theorem nonempty_K (hr : 0 < r) (hn : ∀ g, r ≤ Fintype.card (Y g))
    {w₀ σ : ℝ} (hw : w₀ ≤ 1 / r) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (K D Y r w₀ σ).Nonempty := by
  have he : ∀ g, Nonempty (Fin r ↪ Y g) := fun g =>
    Function.Embedding.nonempty_of_card_le (by simpa using hn g)
  let ι : ∀ g, Fin r ↪ Y g := fun g => Classical.choice (he g)
  exact ⟨Geometry.embed D Y r (uniformEmbedding hr ι), uniformEmbedding_mem_K hr ι hw hσ0 hσ1⟩


/-- A positive Gram margin proves full column rank, independently of tensor uniqueness. -/
theorem GramMargin.linearIndependent {Z O : Type*} [Fintype Z] [Fintype O]
    {σ : ℝ} {L : O → Z → ℝ} (h : GramMargin σ L) (hσ : 0 < σ) :
    LinearIndependent ℝ (fun z => fun y => L y z) := by
  rw [Fintype.linearIndependent_iff]
  intro v hv z
  have hzero : ∀ y, ∑ j, L y j * v j = 0 := by
    intro y
    have hh := congrFun hv y
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using hh
  have hg := h v
  simp only [hzero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hg
  have hs : (∑ j, (v j) ^ 2) ≤ 0 := by nlinarith [sq_pos_of_pos hσ]
  have hz : (v z) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ z)
  nlinarith [sq_nonneg (v z)]

theorem toParameter_fullColumnRank {w₀ σ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ)
    (x : Geometry.Ambient D Y r) (hx : x ∈ K D Y r w₀ σ) (g : G) :
    LinearIndependent ℝ (fun z => fun y => (toParameter hw x hx).kernel g y z) :=
  (hx.2.2.2 g).linearIndependent hσ

open Matrix

def gramDifference {Z O : Type*} [Fintype Z] [Fintype O] [DecidableEq Z]
    (σ : ℝ) (L : O → Z → ℝ) : Matrix Z Z ℝ :=
  (Matrix.of L)ᵀ * Matrix.of L - σ ^ 2 • (1 : Matrix Z Z ℝ)

lemma gramDifference_isHermitian {Z O : Type*} [Fintype Z] [Fintype O] [DecidableEq Z]
    (σ : ℝ) (L : O → Z → ℝ) : (gramDifference σ L).IsHermitian := by
  unfold gramDifference
  apply Matrix.IsHermitian.sub
  · simpa using Matrix.isHermitian_conjTranspose_mul_self (Matrix.of L)
  · exact Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])

lemma gramDifference_quadratic {Z O : Type*} [Fintype Z] [Fintype O] [DecidableEq Z]
    (σ : ℝ) (L : O → Z → ℝ) (v : Z → ℝ) :
    v ⬝ᵥ ((gramDifference σ L) *ᵥ v) =
      (∑ y, (∑ z, L y z * v z) ^ 2) - σ ^ 2 * (∑ z, (v z) ^ 2) := by
  simp only [gramDifference, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, Matrix.mulVec, smul_eq_mul]
  simp_rw [← pow_two]
  rfl

/-- The computational quadratic definition is exactly the paper's PSD Gram constraint. -/
theorem gramMargin_iff_posSemidef {Z O : Type*} [Fintype Z] [Fintype O] [DecidableEq Z]
    (σ : ℝ) (L : O → Z → ℝ) :
    GramMargin σ L ↔ (gramDifference σ L).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hh := gramDifference_isHermitian σ L
  simp only [hh, true_and, star_trivial, gramDifference_quadratic, sub_nonneg]
  rfl


/-- Both directions of W-invariance, including all boundary kernels. -/
theorem smul_mem_K_iff {w₀ σ : ℝ} (hw : 0 < w₀) (x : Geometry.Ambient D Y r) (q : W D r) :
    q • x ∈ K D Y r w₀ σ ↔ x ∈ K D Y r w₀ σ := by
  constructor
  · intro h
    simpa using smul_mem_K hw h q⁻¹
  · intro h
    exact smul_mem_K hw h q

/-- No coordinates are added or removed by the Euclidean presentation of the conditioned set. -/
theorem mem_K_iff_exists_parameter {w₀ σ : ℝ} (hw : 0 < w₀) (x : Geometry.Ambient D Y r) :
    x ∈ K D Y r w₀ σ ↔ ∃ θ : Parameter D Y r,
      Geometry.embed D Y r θ = x ∧ (∀ c z, w₀ ≤ θ.weight c z) ∧
        ∀ g, (gramDifference σ (θ.kernel g)).PosSemidef := by
  constructor
  · intro hx
    refine ⟨toParameter hw x hx, embed_toParameter hw x hx, hx.2.1, ?_⟩
    intro g
    exact (gramMargin_iff_posSemidef σ _).mp (hx.2.2.2 g)
  · rintro ⟨θ, rfl, hθw, hθg⟩
    rw [mem_K_embed_iff]
    exact ⟨hθw, fun g => (gramMargin_iff_posSemidef σ _).mpr (hθg g)⟩

theorem norm_sub_le_diameter {w₀ σ : ℝ} (hw : 0 < w₀)
    {x y : Geometry.Ambient D Y r} (hx : x ∈ K D Y r w₀ σ) (hy : y ∈ K D Y r w₀ σ) :
    ‖x - y‖ ≤ Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) := by
  simpa only [embed_toParameter] using
    Geometry.parameter_diameter D Y r (toParameter hw x hx) (toParameter hw y hy)

end Gen.Conditioned
