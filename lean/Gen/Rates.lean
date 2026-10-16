import Ext.ObservationBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.MetricSpace.IsometricSMul

set_option maxHeartbeats 1200000
open scoped BigOperators Classical
open Set
noncomputable section

namespace Gen.Rates

/-- Exact scalar localization. Equality at the radius belongs to the far set. -/
theorem strict_localization {d e R Δ : ℝ}
    (sep : R ≤ d → Δ ≤ e) (small : e < Δ) : d < R := by
  by_contra h
  exact (not_le_of_gt small) (sep (le_of_not_gt h))

/-- The global max coefficient, with no compactness or existence claim hidden in the lemma. -/
theorem global_inverse_composition {d e R Δ D κ : ℝ}
    (he : 0 ≤ e) (hΔ : 0 < Δ) (hD : 0 ≤ D) (hdiam : d ≤ D)
    (hloc : d ≤ R → d ≤ (2 / κ) * e)
    (hsep : R ≤ d → Δ ≤ e) :
    d ≤ max (2 / κ) (D / Δ) * e := by
  by_cases h : d ≤ R
  · exact (hloc h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he)
  · have hfar : Δ ≤ e := hsep (le_of_lt (lt_of_not_ge h))
    calc
      d ≤ D := hdiam
      _ = (D / Δ) * Δ := by field_simp
      _ ≤ (D / Δ) * e := mul_le_mul_of_nonneg_left hfar (div_nonneg hD hΔ.le)
      _ ≤ max (2 / κ) (D / Δ) * e :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) he

section Local
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A quadratic Taylor remainder derived from actual first and second derivatives.
The domain can be the normalization tangent space translated by the base point. -/
theorem quadratic_remainder_of_hessian
    (f : E → F) (f' : E → E →L[ℝ] F) (f'' : E → E →L[ℝ] (E →L[ℝ] F))
    (a v : E) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hv : ‖v‖ ≤ R)
    (hf : ∀ x, ‖x - a‖ ≤ R → HasFDerivAt f (f' x) x)
    (hf' : ∀ x, ‖x - a‖ ≤ R → HasFDerivAt f' (f'' x) x)
    (hH : ∀ x, ‖x - a‖ ≤ R → ∀ u w, ‖f'' x u w‖ ≤ M * ‖u‖ * ‖w‖) :
    ‖f (a + v) - f a - f' a v‖ ≤ M / 2 * ‖v‖ ^ 2 := by
  have hnorm : ∀ x, ‖x - a‖ ≤ R → ‖f'' x‖ ≤ M := by
    intro x hx
    apply ContinuousLinearMap.opNorm_le_bound _ hM
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg u))
    intro w
    exact hH x hx u w
  have hpath (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖(a + t • v) - a‖ ≤ R := by
    simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] using
      (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans hv
  have hdf (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖f' (a + t • v) - f' a‖ ≤ M * (t * ‖v‖) := by
    have h := (convex_closedBall a R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => (hf' x (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)).hasFDerivWithinAt)
      (fun x hx => hnorm x (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx))
      (show a ∈ Metric.closedBall a R by simpa using hR)
      (show a + t • v ∈ Metric.closedBall a R by simpa only [Metric.mem_closedBall, dist_eq_norm] using hpath t ht)
    simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] using h
  let g : ℝ → F := fun t => f (a + t • v) - f a - t • (f' a v)
  let g' : ℝ → F := fun t => f' (a + t • v) v - f' a v
  have hg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    have hp : HasDerivAt (fun t : ℝ => a + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add a
    convert! (((hf _ (hpath t ht)).comp_hasDerivAt t hp).sub_const (f a)).sub
      ((hasDerivAt_id t).smul_const (f' a v)) using 1 <;> simp [g, g']
  have hbound (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      ‖g' t‖ ≤ M * ‖v‖ ^ 2 * t := by
    calc
      ‖g' t‖ = ‖(f' (a + t • v) - f' a) v‖ := by rfl
      _ ≤ ‖f' (a + t • v) - f' a‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M * (t * ‖v‖)) * ‖v‖ := mul_le_mul_of_nonneg_right (hdf t (Ico_subset_Icc_self ht)) (norm_nonneg _)
      _ = _ := by ring
  let B : ℝ → ℝ := fun t => (M / 2 * ‖v‖ ^ 2) * t ^ 2
  have hB (t : ℝ) : HasDerivAt B (M * ‖v‖ ^ 2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_mul (M / 2 * ‖v‖ ^ 2) using 1 <;> simp [B] <;> ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show ‖g 0‖ ≤ B 0 by simp [g, B]) hB hbound
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  simpa [g, B] using h

/-- Analytic GEN-R-LOCAL on normalized coordinates, before finite gauge alignment. -/
theorem local_inverse_of_jacobian_hessian
    (f : E → F) (f' : E → E →L[ℝ] F) (f'' : E → E →L[ℝ] (E →L[ℝ] F))
    (a y : E) {κ M R : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (hR : 0 < R)
    (hMR : M * R ≤ κ) (hy : ‖y - a‖ ≤ R)
    (hf : ∀ x, ‖x - a‖ ≤ R → HasFDerivAt f (f' x) x)
    (hf' : ∀ x, ‖x - a‖ ≤ R → HasFDerivAt f' (f'' x) x)
    (hJ : ∀ v, κ * ‖v‖ ≤ ‖f' a v‖)
    (hH : ∀ x, ‖x - a‖ ≤ R → ∀ u v, ‖f'' x u v‖ ≤ M * ‖u‖ * ‖v‖) :
    ‖y - a‖ ≤ (2 / κ) * ‖f y - f a‖ := by
  have ht := quadratic_remainder_of_hessian f f' f'' a (y-a) hM hR.le hy hf hf' hH
  simp only [add_sub_cancel] at ht
  have hj := hJ (y-a)
  have hreverse : ‖f' a (y-a)‖ ≤ ‖f y - f a‖ + ‖f y - f a - f' a (y-a)‖ := by
    simpa only [sub_zero, norm_sub_rev, add_comm] using norm_sub_le_norm_sub_add_norm_sub (f' a (y-a)) (f y-f a) 0
  have hcurve : M * ‖y-a‖ ≤ κ := (mul_le_mul_of_nonneg_left hy hM).trans hMR
  have hcurv2 := mul_le_mul_of_nonneg_right hcurve (norm_nonneg (y-a))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hκ).2
  nlinarith
end Local

section Local
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A quadratic Taylor remainder derived from actual first and second derivatives.
The domain can be the normalization tangent space translated by the base point. -/
theorem quadratic_remainder_on_submodule
    (f : E → F) (f' : E → E →L[ℝ] F) (f'' : E → E →L[ℝ] (E →L[ℝ] F))
    (V : Submodule ℝ E) (a v : E) (hvV : v ∈ V) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hv : ‖v‖ ≤ R)
    (hf : ∀ x, x - a ∈ V → ‖x - a‖ ≤ R → HasFDerivAt f (f' x) x)
    (hf' : ∀ x, x - a ∈ V → ‖x - a‖ ≤ R → HasFDerivAt f' (f'' x) x)
    (hH : ∀ x, x - a ∈ V → ‖x - a‖ ≤ R → ∀ u ∈ V, ∀ w ∈ V, ‖f'' x u w‖ ≤ M * ‖u‖ * ‖w‖) :
    ‖f (a + v) - f a - f' a v‖ ≤ M / 2 * ‖v‖ ^ 2 := by
  have hpath (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖(a + t • v) - a‖ ≤ R := by
    simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] using
      (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans hv
  have hpathV (t : ℝ) : (a + t • v) - a ∈ V := by
    simpa only [add_sub_cancel_left] using V.smul_mem t hvV
  have hp (t : ℝ) : HasDerivAt (fun t : ℝ => a + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add a
  have hk (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => f' (a + t • v) v) (f'' (a+t•v) v v) t := by
    have hh := ((hf' _ (hpathV t) (hpath t ht)).comp_hasDerivAt t (hp t)).clm_apply (hasDerivAt_const t v)
    convert! hh using 1 <;> simp
  have hdf (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖f' (a + t • v) v - f' a v‖ ≤ (M * ‖v‖ ^ 2) * t := by
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hk t ht).hasDerivWithinAt)
      (fun t ht => (hH _ (hpathV t) (hpath t (Ico_subset_Icc_self ht)) v hvV v hvV)) t ht
    simpa [pow_two, mul_assoc] using hh
  let g : ℝ → F := fun t => f (a + t • v) - f a - t • (f' a v)
  let g' : ℝ → F := fun t => f' (a + t • v) v - f' a v
  have hg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    have hp : HasDerivAt (fun t : ℝ => a + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add a
    convert! (((hf _ (hpathV t) (hpath t ht)).comp_hasDerivAt t hp).sub_const (f a)).sub
      ((hasDerivAt_id t).smul_const (f' a v)) using 1 <;> simp [g, g']
  have hbound (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      ‖g' t‖ ≤ M * ‖v‖ ^ 2 * t := by
    simpa [g', mul_assoc] using hdf t (Ico_subset_Icc_self ht)
  let B : ℝ → ℝ := fun t => (M / 2 * ‖v‖ ^ 2) * t ^ 2
  have hB (t : ℝ) : HasDerivAt B (M * ‖v‖ ^ 2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_mul (M / 2 * ‖v‖ ^ 2) using 1 <;> simp [B] <;> ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show ‖g 0‖ ≤ B 0 by simp [g, B]) hB hbound
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  simpa [g, B] using h

/-- Analytic GEN-R-LOCAL on normalized coordinates, before finite gauge alignment. -/
theorem local_inverse_on_submodule
    (f : E → F) (f' : E → E →L[ℝ] F) (f'' : E → E →L[ℝ] (E →L[ℝ] F))
    (V : Submodule ℝ E) (a y : E) (hyV : y - a ∈ V) {κ M R : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (hR : 0 < R)
    (hMR : M * R ≤ κ) (hy : ‖y - a‖ ≤ R)
    (hf : ∀ x, x - a ∈ V → ‖x - a‖ ≤ R → HasFDerivAt f (f' x) x)
    (hf' : ∀ x, x - a ∈ V → ‖x - a‖ ≤ R → HasFDerivAt f' (f'' x) x)
    (hJ : ∀ v ∈ V, κ * ‖v‖ ≤ ‖f' a v‖)
    (hH : ∀ x, x - a ∈ V → ‖x - a‖ ≤ R → ∀ u ∈ V, ∀ v ∈ V, ‖f'' x u v‖ ≤ M * ‖u‖ * ‖v‖) :
    ‖y - a‖ ≤ (2 / κ) * ‖f y - f a‖ := by
  have ht := quadratic_remainder_on_submodule f f' f'' V a (y-a) hyV hM hR.le hy hf hf' hH
  simp only [add_sub_cancel] at ht
  have hj := hJ (y-a) hyV
  have hreverse : ‖f' a (y-a)‖ ≤ ‖f y - f a‖ + ‖f y - f a - f' a (y-a)‖ := by
    simpa only [sub_zero, norm_sub_rev, add_comm] using norm_sub_le_norm_sub_add_norm_sub (f' a (y-a)) (f y-f a) 0
  have hcurve : M * ‖y-a‖ ≤ κ := (mul_le_mul_of_nonneg_left hy hM).trans hMR
  have hcurv2 := mul_le_mul_of_nonneg_right hcurve (norm_nonneg (y-a))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hκ).2
  nlinarith
end Local

section Gauge
variable {Γ E : Type*} [Fintype Γ] [Group Γ] [MetricSpace E]
  [MulAction Γ E] [IsIsometricSMul Γ E]

/-- Finite isometric orbit distance, attained over the complete declared gauge. -/
def orbitDist (x y : E) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun q : Γ => dist x (q • y))

theorem orbitDist_attained (x y : E) :
    ∃ q : Γ, orbitDist (Γ := Γ) x y = dist x (q • y) := by
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun q : Γ => dist x (q • y))
  exact ⟨q,hq⟩

theorem orbitDist_le (x y : E) (q : Γ) : orbitDist (Γ := Γ) x y ≤ dist x (q • y) :=
  Finset.inf'_le _ (Finset.mem_univ q)

theorem orbitDist_nonneg (x y : E) : 0 ≤ orbitDist (Γ := Γ) x y :=
  Finset.le_inf' _ _ (fun _ _ => dist_nonneg)

@[simp] theorem orbitDist_self (x : E) : orbitDist (Γ := Γ) x x = 0 := by
  apply le_antisymm _ (orbitDist_nonneg _ _)
  simpa using orbitDist_le x x (1 : Γ)

theorem orbitDist_symm (x y : E) : orbitDist (Γ := Γ) x y = orbitDist (Γ := Γ) y x := by
  have h (x y : E) : orbitDist (Γ := Γ) x y ≤ orbitDist (Γ := Γ) y x := by
    obtain ⟨q,hq⟩ := orbitDist_attained (Γ := Γ) y x
    rw [hq]
    calc
      orbitDist (Γ := Γ) x y ≤ dist x (q⁻¹ • y) := orbitDist_le _ _ _
      _ = dist (q • x) y := by rw [← dist_smul q, smul_inv_smul]
      _ = dist y (q • x) := dist_comm _ _
  exact le_antisymm (h x y) (h y x)

theorem orbitDist_triangle (x y z : E) :
    orbitDist (Γ := Γ) x z ≤ orbitDist (Γ := Γ) x y + orbitDist (Γ := Γ) y z := by
  obtain ⟨q,hq⟩ := orbitDist_attained (Γ := Γ) x y
  obtain ⟨p,hp⟩ := orbitDist_attained (Γ := Γ) y z
  rw [hq,hp]
  calc
    orbitDist (Γ := Γ) x z ≤ dist x ((q*p) • z) := orbitDist_le _ _ _
    _ ≤ dist x (q • y) + dist (q • y) ((q*p) • z) := dist_triangle _ _ _
    _ = _ := by rw [mul_smul, dist_smul]

/-- Zero distance is exactly finite gauge equivalence, not merely orbit closure. -/
theorem orbitDist_eq_zero_iff (x y : E) :
    orbitDist (Γ := Γ) x y = 0 ↔ ∃ q : Γ, x = q • y := by
  constructor
  · intro hz
    obtain ⟨q,hq⟩ := orbitDist_attained (Γ := Γ) x y
    exact ⟨q, dist_eq_zero.mp (hq.symm.trans hz)⟩
  · rintro ⟨q,rfl⟩
    exact le_antisymm (by simpa using orbitDist_le (q • y) y q) (orbitDist_nonneg _ _)


@[simp] theorem orbitDist_smul_left (q : Γ) (x y : E) :
    orbitDist (Γ := Γ) (q • x) y = orbitDist (Γ := Γ) x y := by
  have hz : orbitDist (Γ := Γ) (q • x) x = 0 :=
    (orbitDist_eq_zero_iff _ _).2 ⟨q,rfl⟩
  have hz' : orbitDist (Γ := Γ) x (q • x) = 0 := by rw [orbitDist_symm, hz]
  apply le_antisymm
  · simpa only [hz, zero_add] using orbitDist_triangle (Γ := Γ) (q • x) x y
  · simpa only [hz', zero_add] using orbitDist_triangle (Γ := Γ) x (q • x) y

@[simp] theorem orbitDist_smul_right (q : Γ) (x y : E) :
    orbitDist (Γ := Γ) x (q • y) = orbitDist (Γ := Γ) x y := by
  rw [orbitDist_symm x (q • y), orbitDist_smul_left, orbitDist_symm]

/-- Quotient-Lipschitz control forces invariance; semantic functionals must meet it. -/
theorem quotient_lipschitz_invariant (K : Set E) (f : E → ℝ) (L : ℝ)
    (hK : ∀ (q : Γ) x, x ∈ K → q • x ∈ K)
    (hLip : ∀ x ∈ K, ∀ y ∈ K, |f x - f y| ≤ L * orbitDist (Γ := Γ) x y)
    (q : Γ) (x : E) (hx : x ∈ K) : f (q • x) = f x := by
  have hh := hLip (q • x) (hK q x hx) x hx
  simp only [orbitDist_smul_left, orbitDist_self, mul_zero] at hh
  have hh' := abs_le.mp hh
  linarith

/-- The same finite orbit distance on Euclidean parameter arrays uses entrywise norm. -/
theorem orbitDist_euclidean {ι : Type*} [Fintype ι]
    [MulAction Γ (EuclideanSpace ℝ ι)] [IsIsometricSMul Γ (EuclideanSpace ℝ ι)]
    (x y : EuclideanSpace ℝ ι) :
    orbitDist (Γ := Γ) x y =
      Finset.univ.inf' Finset.univ_nonempty (fun q : Γ => ‖x - q • y‖) := by
  simp only [orbitDist, dist_eq_norm]

/-- The finite minimum is jointly continuous, useful for compact separation. -/
theorem continuous_orbitDist : Continuous (fun p : E × E => orbitDist (Γ := Γ) p.1 p.2) := by
  have h := Continuous.finset_inf' (s := (Finset.univ : Finset Γ)) Finset.univ_nonempty
    (f := fun (q : Γ) (p : E × E) => dist p.1 (q • p.2))
    (fun q _ => continuous_fst.dist ((isometry_smul E q).continuous.comp continuous_snd))
  convert h using 1
  funext p
  simp only [orbitDist, Finset.inf'_apply]

end Gauge

section GaugeLocal
variable {Γ E F : Type*} [Fintype Γ] [Group Γ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MulAction Γ E] [IsIsometricSMul Γ E]

/-- GEN-R-LOCAL after exact finite alignment. Derivatives and the Hessian are
quantified on the whole affine ball, including points outside a simplex. -/
theorem orbit_local_inverse
    (f : E → F) (f' : E → E →L[ℝ] F) (f'' : E → E →L[ℝ] (E →L[ℝ] F))
    (V : Submodule ℝ E) (a y : E)
    (hinv : ∀ q : Γ, f (q • y) = f y)
    (hV : ∀ q : Γ, q • y - a ∈ V)
    {κ M R : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (hR : 0 < R)
    (hMR : M * R ≤ κ) (hy : orbitDist (Γ := Γ) y a ≤ R)
    (hf : ∀ x, x - a ∈ V → ‖x - a‖ ≤ R → HasFDerivAt f (f' x) x)
    (hf' : ∀ x, x - a ∈ V → ‖x - a‖ ≤ R → HasFDerivAt f' (f'' x) x)
    (hJ : ∀ v ∈ V, κ * ‖v‖ ≤ ‖f' a v‖)
    (hH : ∀ x, x - a ∈ V → ‖x - a‖ ≤ R → ∀ u ∈ V, ∀ v ∈ V,
      ‖f'' x u v‖ ≤ M * ‖u‖ * ‖v‖) :
    orbitDist (Γ := Γ) y a ≤ (2 / κ) * ‖f y - f a‖ := by
  obtain ⟨q,hq⟩ := orbitDist_attained (Γ := Γ) a y
  have heq : orbitDist (Γ := Γ) y a = ‖q • y - a‖ := by
    rw [orbitDist_symm, hq, dist_eq_norm, norm_sub_rev]
  have h := local_inverse_on_submodule f f' f'' V a (q • y) (hV q)
    hκ hM hR hMR (heq ▸ hy) hf hf' hJ hH
  rwa [hinv q, ← heq] at h
end GaugeLocal

section Normed
variable {H : Type*} [NormedAddCommGroup H]

/-- GEN absolute-residual transfer, for any normed observation space. -/
theorem residual_transfer {fit empirical population target : H} {τ s ε : ℝ}
    (hnoise : ‖empirical - population‖ ≤ s)
    (hmiss : ‖population - target‖ ≤ τ)
    (hres : ‖fit - empirical‖ ≤ τ + s + ε) :
    ‖fit - target‖ ≤ 2 * (τ + s) + ε := by
  have ht := norm_sub_le_norm_sub_add_norm_sub fit empirical target
  have hp := norm_sub_le_norm_sub_add_norm_sub empirical population target
  linarith

/-- RATE near-global comparison is used only at the population target. -/
theorem near_global_transfer {fit empirical population target : H} {τ s ε : ℝ}
    (hnoise : ‖empirical - population‖ ≤ s)
    (hmiss : ‖population - target‖ ≤ τ)
    (hopt : ‖fit - empirical‖ ≤ ‖target - empirical‖ + ε) :
    ‖fit - target‖ ≤ 2 * (τ + s) + ε := by
  apply residual_transfer hnoise hmiss
  have htri := norm_sub_le_norm_sub_add_norm_sub target population empirical
  rw [norm_sub_rev target population, norm_sub_rev population empirical] at htri
  linarith
end Normed

/-- Literal conservative sample count in RATE's informative regime. -/
def informativeCount (m a : ℝ) : ℕ := Nat.ceil (20 * m ^ 2 / a ^ 2)

theorem informativeCount_pos {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    0 < informativeCount m a := by
  exact Nat.ceil_pos.mpr (by positivity)

/-- The algebraic ceiling dominates the radius; no numerical log approximation. -/
theorem informative_radius_le {m a : ℝ} (hm : 1 ≤ m) (ha : 0 < a)
    (N : ℕ) (hN : informativeCount m a ≤ N) :
    Real.sqrt (m * Real.log (40 * m) / (2 * (N : ℝ))) ≤ a := by
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < N := (informativeCount_pos hm0 ha).trans_le hN
  have hnR : (0 : ℝ) < N := by exact_mod_cast hn0
  have hceil : 20 * m ^ 2 / a ^ 2 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hmul : 20 * m ^ 2 ≤ (N : ℝ) * a ^ 2 := (div_le_iff₀ (sq_pos_of_pos ha)).mp hceil
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 40 * m by positivity)
  have hmlog := mul_le_mul_of_nonneg_left hlog hm0.le
  apply (Real.sqrt_le_left ha.le).2
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2 * (N:ℝ))).2
  nlinarith

/-- Exact small-error and half-diameter arithmetic with the stated min and ceiling. -/
theorem informative_sample_rule {m κ D Δ : ℝ}
    (hm : 1 ≤ m) (hκ : 0 < κ) (hD : 0 < D) (hΔ : 0 < Δ)
    (N : ℕ) (hN : informativeCount m (min (κ * D / 8) (Δ / 4)) ≤ N) :
    2 * Real.sqrt (m * Real.log (40 * m) / (2 * (N : ℝ))) < Δ ∧
    (2 / κ) * (2 * Real.sqrt (m * Real.log (40 * m) / (2 * (N : ℝ)))) ≤ D / 2 := by
  have ha : 0 < min (κ * D / 8) (Δ / 4) := lt_min (by positivity) (by positivity)
  have hs := informative_radius_le hm ha N hN
  have hs1 := hs.trans (min_le_left _ _)
  have hs2 := hs.trans (min_le_right _ _)
  constructor
  · linarith
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hκ).2
    nlinarith

section Observation
variable {E : Type*} [Fintype E] [Nonempty E]
variable {X : E → Type*} [∀ e, Fintype (X e)]

/-- The actual Euclidean stacking of every edge cell, including zero cells. -/
def stack (p : ∀ e, X e → ℝ) : EuclideanSpace ℝ ((e : E) × X e) :=
  WithLp.toLp 2 (fun j => p j.1 j.2)

@[simp] theorem stack_apply (p : ∀ e, X e → ℝ) (j : (e : E) × X e) :
    stack p j = p j.1 j.2 := rfl

/-- Literal GEN/RATE radius, not an assumed concentration oracle. -/
def samplingRadius (O : Ext.ObservationExperiment E X) (δ : ℝ) : ℝ :=
  Real.sqrt (∑ e, (Fintype.card (X e) : ℝ) *
    Real.log (2 * (O.totalCells : ℝ) / δ) / (2 * (O.n e : ℝ)))

theorem samplingRadius_nonneg (O : Ext.ObservationExperiment E X) (δ : ℝ) :
    0 ≤ samplingRadius O δ := Real.sqrt_nonneg _

theorem radius_log_nonneg (O : Ext.ObservationExperiment E X)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ Real.log (2 * (O.totalCells : ℝ) / δ) := by
  have hm : (1 : ℝ) ≤ O.totalCells := by exact_mod_cast O.totalCells_pos
  apply Real.log_nonneg
  apply (le_div_iff₀ hδ).2
  linarith

/-- Every coordinate control implies the required stacked Euclidean control. -/
theorem stacked_of_cells (O : Ext.ObservationExperiment E X)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (p : ∀ e, X e → ℝ)
    (hc : ∀ e x, |p e x - (O.law e).mass x| ≤ O.cellRadius δ e) :
    ‖stack p - stack (fun e => (O.law e).mass)‖ ≤ samplingRadius O δ := by
  have hsq : ‖stack p - stack (fun e => (O.law e).mass)‖ ^ 2 ≤
      ∑ e, (Fintype.card (X e) : ℝ) *
        Real.log (2 * (O.totalCells : ℝ) / δ) / (2 * (O.n e : ℝ)) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro e _
    calc
      (∑ x : X e, (stack p - stack (fun e => (O.law e).mass)) ⟨e,x⟩ ^ 2) ≤
          ∑ _x : X e, (O.cellRadius δ e) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        change (p e x - (O.law e).mass x) ^ 2 ≤ (O.cellRadius δ e) ^ 2
        rw [← sq_abs (p e x - (O.law e).mass x)]
        exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).2 (hc e x)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [Ext.ObservationExperiment.cellRadius, Real.sq_sqrt
          (div_nonneg (radius_log_nonneg O hδ hδ1) (by positivity))]
        ring
  exact (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg (fun e _ =>
    div_nonneg (mul_nonneg (by positivity) (radius_log_nonneg O hδ hδ1)) (by positivity)))).2 hsq


/-- Equal sample counts recover the exact scalar form used in the sample rule. -/
theorem samplingRadius_equal_count (O : Ext.ObservationExperiment E X)
    (δ : ℝ) (N : ℕ) (hN : ∀ e, O.n e = N) :
    samplingRadius O δ = Real.sqrt ((O.totalCells : ℝ) *
      Real.log (2 * (O.totalCells : ℝ) / δ) / (2 * (N : ℝ))) := by
  unfold samplingRadius
  congr 1
  simp_rw [hN]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  simp only [Ext.ObservationExperiment.totalCells, Nat.cast_sum]

theorem samplingRadius_informative (O : Ext.ObservationExperiment E X)
    {κ D Δ : ℝ} (hκ : 0 < κ) (hD : 0 < D) (hΔ : 0 < Δ)
    (N : ℕ) (hN : ∀ e, O.n e = N)
    (hcount : informativeCount (O.totalCells : ℝ) (min (κ * D / 8) (Δ / 4)) ≤ N) :
    2 * samplingRadius O (1 / 20) < Δ ∧
    (2 / κ) * (2 * samplingRadius O (1 / 20)) ≤ D / 2 := by
  rw [samplingRadius_equal_count O (1/20) N hN]
  have hm : (1:ℝ) ≤ O.totalCells := by exact_mod_cast O.totalCells_pos
  have he : 2 * (O.totalCells : ℝ) / (1 / 20) = 40 * (O.totalCells : ℝ) := by ring
  rw [he]
  exact informative_sample_rule hm hκ hD hΔ N hcount

/-- A separately justified TV discrepancy gives the exact conservative Euclidean input. -/
theorem stacked_of_tv (P Q : ∀ e, Ext.FiniteLaw (X e)) (b : E → ℝ)
    (hb : ∀ e, (P e).tv (Q e) ≤ b e) :
    ‖stack (fun e => (P e).mass) - stack (fun e => (Q e).mass)‖ ≤
      2 * Real.sqrt (∑ e, (b e) ^ 2) := by
  have hb0 (e : E) : 0 ≤ b e := ((P e).tv_nonneg (Q e)).trans (hb e)
  have hs : ‖stack (fun e => (P e).mass) - stack (fun e => (Q e).mass)‖ ^ 2 ≤
      4 * ∑ e, (b e) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    have hsum : (∑ x, |(P e).mass x - (Q e).mass x|) ≤ 2 * b e := by
      have hh := hb e
      unfold Ext.FiniteLaw.tv at hh
      linarith
    calc
      (∑ x : X e, (stack (fun e => (P e).mass) - stack (fun e => (Q e).mass)) ⟨e,x⟩ ^ 2) =
          ∑ x, |(P e).mass x - (Q e).mass x| ^ 2 := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [sq_abs]
        rfl
      _ ≤ (∑ x, |(P e).mass x - (Q e).mass x|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun x _ => abs_nonneg _)
      _ ≤ (2 * b e) ^ 2 := (sq_le_sq₀ (Finset.sum_nonneg (fun x _ => abs_nonneg _))
        (mul_nonneg (by norm_num) (hb0 e))).2 hsum
      _ = 4 * (b e) ^ 2 := by ring
  have hh := Real.sq_sqrt (show 0 ≤ ∑ e, (b e)^2 from Finset.sum_nonneg (fun e _ => sq_nonneg (b e)))
  have hr := Real.sqrt_nonneg (∑ e, (b e)^2)
  nlinarith [norm_nonneg (stack (fun e => (P e).mass) - stack (fun e => (Q e).mass))]

/-- Actual finite IID-within-edge law. Dependence between edges is unrestricted. -/
theorem stacked_hoeffding {Ω : Type*} [Fintype Ω]
    (O : Ext.ObservationExperiment E X) (μ : Ext.FiniteLaw Ω)
    (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.prob (fun ω =>
      ‖stack (O.empirical (obs ω)) - stack (fun e => (O.law e).mass)‖ ≤ samplingRadius O δ) := by
  apply (Ext.edge_cell_family_bound O μ obs hIID hδ hδ1).trans (μ.prob_mono ?_)
  intro ω hω
  exact stacked_of_cells O hδ hδ1 _ hω

/-- GEN-R-STAT observational clause with the absolute residual quantified on every outcome. -/
theorem gen_stat_observation {Ω Θ : Type*} [Fintype Ω]
    (O : Ext.ObservationExperiment E X) (μ : Ext.FiniteLaw Ω)
    (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (F : Θ → EuclideanSpace ℝ ((e : E) × X e)) (target : Θ) (fit : Ω → Θ)
    {δ τ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmiss : ‖stack (fun e => (O.law e).mass) - F target‖ ≤ τ)
    (hres : ∀ ω, ‖F (fit ω) - stack (O.empirical (obs ω))‖ ≤ τ + samplingRadius O δ + ε) :
    1 - δ ≤ μ.prob (fun ω => ‖F (fit ω) - F target‖ ≤
      2 * (τ + samplingRadius O δ) + ε) := by
  apply (stacked_hoeffding O μ obs hIID hδ hδ1).trans (μ.prob_mono ?_)
  intro ω hω
  exact residual_transfer hω hmiss (hres ω)

/-- RATE-S error composition with all-outcome, all-competitor near-global optimality.
The deterministic inverse and diameter interfaces are explicit hypotheses here;
this declaration does not claim to derive RATE-D1--D4. -/
theorem rate_stat_composition {Ω Θ : Type*} [Fintype Ω]
    (O : Ext.ObservationExperiment E X) (μ : Ext.FiniteLaw Ω)
    (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (F : Θ → EuclideanSpace ℝ ((e : E) × X e)) (K : Set Θ)
    (target : Θ) (fit : Ω → Θ) (d : Θ → Θ → ℝ)
    {δ τ ε D C : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hC : 0 ≤ C)
    (htarget : target ∈ K) (hfit : ∀ ω, fit ω ∈ K)
    (hmiss : ‖stack (fun e => (O.law e).mass) - F target‖ ≤ τ)
    (hopt : ∀ ω, ∀ ζ ∈ K,
      ‖F (fit ω) - stack (O.empirical (obs ω))‖ ≤
        ‖F ζ - stack (O.empirical (obs ω))‖ + ε)
    (hdiam : ∀ a ∈ K, ∀ b ∈ K, d a b ≤ D)
    (hinv : ∀ a ∈ K, ∀ b ∈ K, d a b ≤ C * ‖F a - F b‖) :
    1 - δ ≤ μ.prob (fun ω =>
      ‖F (fit ω) - F target‖ ≤ 2 * (τ + samplingRadius O δ) + ε ∧
      d (fit ω) target ≤ min D (C * (2 * (τ + samplingRadius O δ) + ε))) := by
  apply (stacked_hoeffding O μ obs hIID hδ hδ1).trans (μ.prob_mono ?_)
  intro ω hω
  have he := near_global_transfer hω hmiss (hopt ω target htarget)
  exact ⟨he, le_min (hdiam _ (hfit ω) _ htarget)
    ((hinv _ (hfit ω) _ htarget).trans (mul_le_mul_of_nonneg_left he hC))⟩

/-- GEN local parameter transfer preserves the all-outcome localization condition. -/
theorem gen_stat_local {Ω Θ : Type*} [Fintype Ω]
    (O : Ext.ObservationExperiment E X) (μ : Ext.FiniteLaw Ω)
    (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (F : Θ → EuclideanSpace ℝ ((e : E) × X e)) (target : Θ) (fit : Ω → Θ)
    (d : Θ → Θ → ℝ) {δ τ ε κ R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hκ : 0 < κ)
    (hmiss : ‖stack (fun e => (O.law e).mass) - F target‖ ≤ τ)
    (hres : ∀ ω, ‖F (fit ω) - stack (O.empirical (obs ω))‖ ≤ τ + samplingRadius O δ + ε)
    (hfit : ∀ ω, d (fit ω) target ≤ R)
    (hloc : ∀ η, d η target ≤ R → d η target ≤ (2 / κ) * ‖F η - F target‖) :
    1 - δ ≤ μ.prob (fun ω => d (fit ω) target ≤
      (2 / κ) * (2 * (τ + samplingRadius O δ) + ε)) := by
  apply (gen_stat_observation O μ obs hIID F target fit hδ hδ1 hmiss hres).trans (μ.prob_mono ?_)
  intro ω hω
  exact (hloc _ (hfit ω)).trans (mul_le_mul_of_nonneg_left hω (by positivity))


/-- GEN global parameter bounds use the absolute-residual interface unchanged. -/
theorem gen_stat_global {Ω Θ : Type*} [Fintype Ω]
    (O : Ext.ObservationExperiment E X) (μ : Ext.FiniteLaw Ω)
    (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (F : Θ → EuclideanSpace ℝ ((e : E) × X e)) (K : Set Θ)
    (target : Θ) (fit : Ω → Θ) (d : Θ → Θ → ℝ)
    {δ τ ε D κ R Δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hD : 0 ≤ D) (hκ : 0 < κ) (hΔ : 0 < Δ)
    (htarget : target ∈ K) (hfit : ∀ ω, fit ω ∈ K)
    (hmiss : ‖stack (fun e => (O.law e).mass) - F target‖ ≤ τ)
    (hres : ∀ ω, ‖F (fit ω) - stack (O.empirical (obs ω))‖ ≤ τ + samplingRadius O δ + ε)
    (hdiam : ∀ a ∈ K, ∀ b ∈ K, d a b ≤ D)
    (hloc : ∀ a ∈ K, ∀ b ∈ K, d a b ≤ R → d a b ≤ (2 / κ) * ‖F a - F b‖)
    (hsep : ∀ a ∈ K, ∀ b ∈ K, R ≤ d a b → Δ ≤ ‖F a - F b‖) :
    1 - δ ≤ μ.prob (fun ω =>
      d (fit ω) target ≤ max (2 / κ) (D / Δ) * (2 * (τ + samplingRadius O δ) + ε) ∧
      (2 * (τ + samplingRadius O δ) + ε < Δ →
        d (fit ω) target ≤ (2 / κ) * (2 * (τ + samplingRadius O δ) + ε))) := by
  apply (gen_stat_observation O μ obs hIID F target fit hδ hδ1 hmiss hres).trans (μ.prob_mono ?_)
  intro ω he
  have hd := hdiam _ (hfit ω) _ htarget
  have hl := hloc _ (hfit ω) _ htarget
  have hs := hsep _ (hfit ω) _ htarget
  have hg := global_inverse_composition (norm_nonneg _) hΔ hD hd hl hs
  refine ⟨hg.trans (mul_le_mul_of_nonneg_left he ?_), ?_⟩
  · exact (show 0 ≤ 2 / κ by positivity).trans (le_max_left _ _)
  · intro hsmall
    exact (hl (strict_localization hs (he.trans_lt hsmall)).le).trans
      (mul_le_mul_of_nonneg_left he (by positivity))

/-- RATE-S conditional on the deterministic local/separation/diameter interface.
One actual concentration event supplies both global and strict-localized bounds. -/
theorem rate_stat_full_interface {Ω Θ : Type*} [Fintype Ω]
    (O : Ext.ObservationExperiment E X) (μ : Ext.FiniteLaw Ω)
    (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (F : Θ → EuclideanSpace ℝ ((e : E) × X e)) (K : Set Θ)
    (target : Θ) (fit : Ω → Θ) (d : Θ → Θ → ℝ)
    {δ τ ε D κ R Δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hD : 0 ≤ D) (hκ : 0 < κ) (hΔ : 0 < Δ)
    (htarget : target ∈ K) (hfit : ∀ ω, fit ω ∈ K)
    (hmiss : ‖stack (fun e => (O.law e).mass) - F target‖ ≤ τ)
    (hopt : ∀ ω, ∀ ζ ∈ K,
      ‖F (fit ω) - stack (O.empirical (obs ω))‖ ≤
        ‖F ζ - stack (O.empirical (obs ω))‖ + ε)
    (hdiam : ∀ a ∈ K, ∀ b ∈ K, d a b ≤ D)
    (hloc : ∀ a ∈ K, ∀ b ∈ K, d a b ≤ R → d a b ≤ (2 / κ) * ‖F a - F b‖)
    (hsep : ∀ a ∈ K, ∀ b ∈ K, R ≤ d a b → Δ ≤ ‖F a - F b‖) :
    1 - δ ≤ μ.prob (fun ω =>
      ‖F (fit ω) - F target‖ ≤ 2 * (τ + samplingRadius O δ) + ε ∧
      d (fit ω) target ≤ min D (max (2 / κ) (D / Δ) * (2 * (τ + samplingRadius O δ) + ε)) ∧
      (2 * (τ + samplingRadius O δ) + ε < Δ →
        d (fit ω) target ≤ min D ((2 / κ) * (2 * (τ + samplingRadius O δ) + ε)))) := by
  apply (stacked_hoeffding O μ obs hIID hδ hδ1).trans (μ.prob_mono ?_)
  intro ω hω
  have he := near_global_transfer hω hmiss (hopt ω target htarget)
  have hd := hdiam _ (hfit ω) _ htarget
  have hl := hloc _ (hfit ω) _ htarget
  have hs := hsep _ (hfit ω) _ htarget
  have hg := global_inverse_composition (norm_nonneg _) hΔ hD hd hl hs
  refine ⟨he, le_min hd (hg.trans (mul_le_mul_of_nonneg_left he ?_)), ?_⟩
  · exact (show 0 ≤ 2 / κ by positivity).trans (le_max_left _ _)
  · intro hsmall
    have hr := (strict_localization hs (he.trans_lt hsmall)).le
    exact le_min hd ((hl hr).trans (mul_le_mul_of_nonneg_left he (by positivity)))


/-- The literal algebraic sample rule yields probability 19/20 and error D/2
for a qualifying exact global estimator. Estimator computability is separate. -/
theorem rate_stat_informative {Ω Θ : Type*} [Fintype Ω]
    (O : Ext.ObservationExperiment E X) (μ : Ext.FiniteLaw Ω)
    (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (F : Θ → EuclideanSpace ℝ ((e : E) × X e)) (K : Set Θ)
    (target : Θ) (fit : Ω → Θ) (d : Θ → Θ → ℝ)
    {κ D R Δ : ℝ} (hκ : 0 < κ) (hD : 0 < D) (hΔ : 0 < Δ)
    (htarget : target ∈ K) (hfit : ∀ ω, fit ω ∈ K)
    (htrue : stack (fun e => (O.law e).mass) = F target)
    (hopt : ∀ ω, ∀ ζ ∈ K, ‖F (fit ω) - stack (O.empirical (obs ω))‖ ≤
      ‖F ζ - stack (O.empirical (obs ω))‖)
    (hloc : ∀ a ∈ K, ∀ b ∈ K, d a b ≤ R → d a b ≤ (2 / κ) * ‖F a - F b‖)
    (hsep : ∀ a ∈ K, ∀ b ∈ K, R ≤ d a b → Δ ≤ ‖F a - F b‖)
    (N : ℕ) (hN : ∀ e, O.n e = N)
    (hcount : informativeCount (O.totalCells : ℝ) (min (κ * D / 8) (Δ / 4)) ≤ N) :
    (19 / 20 : ℝ) ≤ μ.prob (fun ω => d (fit ω) target ≤ D / 2) := by
  have hsample := samplingRadius_informative O hκ hD hΔ N hN hcount
  have hprob := stacked_hoeffding O μ obs hIID
    (show (0:ℝ) < 1/20 by norm_num) (show (1/20:ℝ) < 1 by norm_num)
  norm_num at hprob
  apply hprob.trans (μ.prob_mono ?_)
  intro ω hω
  have he : ‖F (fit ω) - F target‖ ≤ 2 * samplingRadius O (1/20) := by
    have hmiss : ‖stack (fun e => (O.law e).mass) - F target‖ ≤ (0:ℝ) := by rw [htrue]; simp
    have hh := near_global_transfer hω hmiss
      (show ‖F (fit ω) - stack (O.empirical (obs ω))‖ ≤
        ‖F target - stack (O.empirical (obs ω))‖ + 0 by simpa using hopt ω target htarget)
    simpa only [zero_add, add_zero] using hh
  have hs := hsep _ (hfit ω) _ htarget
  have hr := (strict_localization hs (he.trans_lt hsample.1)).le
  exact ((hloc _ (hfit ω) _ htarget hr).trans
    (mul_le_mul_of_nonneg_left he (by positivity))).trans hsample.2

/-- A specified quotient-Lipschitz functional transfers on the same finite-law event. -/
theorem functional_rate_transfer {Ω Θ : Type*} [Fintype Ω]
    (μ : Ext.FiniteLaw Ω) (K : Set Θ) (f : Θ → ℝ) (d : Θ → Θ → ℝ)
    (target : Θ) (fit : Ω → Θ) {δ B L : ℝ}
    (hL : 0 ≤ L) (htarget : target ∈ K) (hfit : ∀ ω, fit ω ∈ K)
    (hLip : ∀ a ∈ K, ∀ b ∈ K, |f a - f b| ≤ L * d a b)
    (hrate : 1 - δ ≤ μ.prob (fun ω => d (fit ω) target ≤ B)) :
    1 - δ ≤ μ.prob (fun ω => |f (fit ω) - f target| ≤ L * B) := by
  apply hrate.trans (μ.prob_mono ?_)
  intro ω hω
  exact (hLip _ (hfit ω) _ htarget).trans (mul_le_mul_of_nonneg_left hω hL)

end Observation
end Gen.Rates
