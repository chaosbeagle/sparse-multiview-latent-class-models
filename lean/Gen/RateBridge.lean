import Gen.Geometry

set_option maxHeartbeats 1600000
open scoped BigOperators Classical
noncomputable section
namespace Gen.RateBridge
open Gen.Geometry

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- Every declared subgroup inherits the already proved coordinate isometry. -/
instance subgroupAmbientIsometric (Γ : Subgroup (Gen.W D r)) :
    IsIsometricSMul Γ (Ambient D Y r) where
  isometry_smul q := by
    simpa only [Subgroup.smul_def] using isometry_smul (Ambient D Y r) q.val

/-- Actual model distance for an arbitrary declared finite subgroup. -/
def parameterDist (Γ : Subgroup (Gen.W D r)) (θ η : Gen.Parameter D Y r) : ℝ :=
  Gen.Rates.orbitDist (Γ := Γ) (embed D Y r θ) (embed D Y r η)

/-- Exact equality to the paper's right-pullback minimum; inverse reindexing is explicit. -/
theorem parameterDist_eq_min (Γ : Subgroup (Gen.W D r)) (θ η : Gen.Parameter D Y r) :
    parameterDist D Y r Γ θ η = Finset.univ.inf' Finset.univ_nonempty
      (fun q : Γ => ‖embed D Y r θ - embed D Y r (η.permute q.val)‖) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro q _
    have h := Gen.Rates.orbitDist_le (embed D Y r θ) (embed D Y r η) (q⁻¹ : Γ)
    simpa only [parameterDist, dist_eq_norm, embed_permute, Subgroup.smul_def,
      InvMemClass.coe_inv] using h
  · obtain ⟨q,hq⟩ := Gen.Rates.orbitDist_attained (Γ := Γ) (embed D Y r θ) (embed D Y r η)
    unfold parameterDist
    rw [hq]
    have h := Finset.inf'_le (fun q : Γ => ‖embed D Y r θ - embed D Y r (η.permute q.val)‖)
      (Finset.mem_univ (q⁻¹ : Γ))
    simpa only [embed_permute, InvMemClass.coe_inv, inv_inv, dist_eq_norm, Subgroup.smul_def] using h

theorem parameterDist_nonneg (Γ : Subgroup (Gen.W D r)) (θ η : Gen.Parameter D Y r) :
    0 ≤ parameterDist D Y r Γ θ η := Gen.Rates.orbitDist_nonneg _ _

theorem parameterDist_symm (Γ : Subgroup (Gen.W D r)) (θ η : Gen.Parameter D Y r) :
    parameterDist D Y r Γ θ η = parameterDist D Y r Γ η θ := Gen.Rates.orbitDist_symm _ _

theorem parameterDist_triangle (Γ : Subgroup (Gen.W D r)) (θ η ζ : Gen.Parameter D Y r) :
    parameterDist D Y r Γ θ ζ ≤ parameterDist D Y r Γ θ η + parameterDist D Y r Γ η ζ :=
  Gen.Rates.orbitDist_triangle _ _ _

/-- This zero-loss relation is the exact declared semantic gauge, not the full W by default. -/
theorem parameterDist_eq_zero_iff (Γ : Subgroup (Gen.W D r)) (θ η : Gen.Parameter D Y r) :
    parameterDist D Y r Γ θ η = 0 ↔ ∃ q ∈ Γ, θ = η.permute q := by
  rw [parameterDist, Gen.Rates.orbitDist_eq_zero_iff]
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨q.val⁻¹, Γ.inv_mem q.property, (embed_injective D Y r) ?_⟩
    simpa only [embed_permute, inv_inv, Subgroup.smul_def] using hq
  · rintro ⟨q,hq,rfl⟩
    refine ⟨⟨q⁻¹,Γ.inv_mem hq⟩, ?_⟩
    exact embed_permute D Y r η q

/-- The literal global stochastic diameter also bounds each finite-gauge distance. -/
theorem parameterDist_diameter (Γ : Subgroup (Gen.W D r)) (θ η : Gen.Parameter D Y r) :
    parameterDist D Y r Γ θ η ≤
      Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) := by
  have h := Gen.Rates.orbitDist_le (embed D Y r θ) (embed D Y r η) (1 : Γ)
  simp only [one_smul, dist_eq_norm] at h
  exact h.trans (parameter_diameter D Y r θ η)

/-- Translation by the exact tangent space is equivalent to the affine equalities. -/
theorem normalized_of_sub_mem {x y : Ambient D Y r}
    (hy : Normalized D Y r y) (hxy : x - y ∈ tangent D Y r) : Normalized D Y r x := by
  constructor
  · intro c
    have h := hxy.1 c
    have hh := hy.1 c
    simp only [PiLp.sub_apply, Finset.sum_sub_distrib] at h
    linarith
  · intro g z
    have h := hxy.2 g z
    have hh := hy.2 g z
    simp only [PiLp.sub_apply, Finset.sum_sub_distrib] at h
    linarith

/-- Genuine first derivative of the actual observation polynomial. -/
theorem observation_hasFDerivAt (x : Ambient D Y r) :
    HasFDerivAt (observation D Y r) (fderiv ℝ (observation D Y r) x) x :=
  ((observation_contDiff D Y r 1).differentiable (by norm_num) x).hasFDerivAt

/-- Genuine second derivative exists throughout the ambient space, including outside Xi. -/
theorem observation_derivative_hasFDerivAt (x : Ambient D Y r) :
    HasFDerivAt (fderiv ℝ (observation D Y r))
      (fderiv ℝ (fderiv ℝ (observation D Y r)) x) x := by
  have h : ContDiff ℝ 1 (fderiv ℝ (observation D Y r)) :=
    (observation_contDiff D Y r 2).fderiv_right (by norm_num)
  exact (h.differentiable (by norm_num) x).hasFDerivAt

/-- GEN-R-LOCAL for the actual Xi_r polynomial, true Euclidean coordinates,
all normalization constraints, and any declared finite permutation subgroup. -/
theorem gen_local (Γ : Subgroup (Gen.W D r)) (θ η : Gen.Parameter D Y r)
    {κ M R : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (hR : 0 < R) (hMR : M * R ≤ κ)
    (hJ : ∀ v ∈ tangent D Y r,
      κ * ‖v‖ ≤ ‖fderiv ℝ (observation D Y r) (embed D Y r θ) v‖)
    (hH : ∀ x : Ambient D Y r, Normalized D Y r x → ‖x - embed D Y r θ‖ ≤ R →
      ∀ u ∈ tangent D Y r, ∀ v ∈ tangent D Y r,
        ‖fderiv ℝ (fderiv ℝ (observation D Y r)) x u v‖ ≤ M * ‖u‖ * ‖v‖)
    (hloc : parameterDist D Y r Γ η θ ≤ R) :
    parameterDist D Y r Γ η θ ≤ (2 / κ) *
      ‖Gen.Rates.stack (fun e => η.observation e) - Gen.Rates.stack (fun e => θ.observation e)‖ := by
  have ha (q : Γ) : embed D Y r (η.permute q.val⁻¹) = q • embed D Y r η := by
    simpa only [embed_permute, inv_inv, Subgroup.smul_def]
  have hi (q : Γ) : observation D Y r (q • embed D Y r η) = observation D Y r (embed D Y r η) := by
    rw [← ha q, observation_embed, observation_embed]
    congr 1
    funext e x
    exact η.permute_observation q.val⁻¹ e x
  have hv (q : Γ) : q • embed D Y r η - embed D Y r θ ∈ tangent D Y r := by
    rw [← ha q]
    exact sub_mem_tangent D Y r (embed_normalized D Y r _) (embed_normalized D Y r _)
  have h := Gen.Rates.orbit_local_inverse (Γ := Γ)
    (observation D Y r) (fderiv ℝ (observation D Y r))
    (fderiv ℝ (fderiv ℝ (observation D Y r))) (tangent D Y r)
    (embed D Y r θ) (embed D Y r η) hi hv hκ hM hR hMR hloc
    (fun x _ _ => observation_hasFDerivAt D Y r x)
    (fun x _ _ => observation_derivative_hasFDerivAt D Y r x)
    hJ (fun x hx hxr => hH x (normalized_of_sub_mem D Y r (embed_normalized D Y r θ) hx) hxr)
  simpa only [parameterDist, observation_embed] using h

/-- Exactly the accepted common Jacobian/Hessian conditions on the real model.
This structure records hypotheses; it does not claim the explicit RATE margins imply them. -/
structure LocalConditions (K : Set (Gen.Parameter D Y r)) (κ M R : ℝ) : Prop where
  kappa_pos : 0 < κ
  curvature_nonneg : 0 ≤ M
  radius_pos : 0 < R
  curvature_radius : M * R ≤ κ
  jacobian : ∀ θ ∈ K, ∀ v ∈ tangent D Y r,
    κ * ‖v‖ ≤ ‖fderiv ℝ (observation D Y r) (embed D Y r θ) v‖
  hessian : ∀ θ ∈ K, ∀ x : Ambient D Y r,
    Normalized D Y r x → ‖x - embed D Y r θ‖ ≤ R →
      ∀ u ∈ tangent D Y r, ∀ v ∈ tangent D Y r,
        ‖fderiv ℝ (fderiv ℝ (observation D Y r)) x u v‖ ≤ M * ‖u‖ * ‖v‖

/-- The actual-model global upgrade, with strict localization and the exact max. -/
theorem gen_global (Γ : Subgroup (Gen.W D r))
    (K : Set (Gen.Parameter D Y r)) {κ M R Δ DK : ℝ}
    (hc : LocalConditions D Y r K κ M R) (hΔ : 0 < Δ)
    (hdiam : ∀ θ ∈ K, ∀ η ∈ K, parameterDist D Y r Γ θ η ≤ DK)
    (hsep : ∀ θ ∈ K, ∀ η ∈ K, R ≤ parameterDist D Y r Γ θ η →
      Δ ≤ ‖Gen.Rates.stack θ.observation - Gen.Rates.stack η.observation‖)
    (θ η : Gen.Parameter D Y r) (hθ : θ ∈ K) (hη : η ∈ K) :
    (‖Gen.Rates.stack η.observation - Gen.Rates.stack θ.observation‖ < Δ →
      parameterDist D Y r Γ η θ ≤ (2 / κ) *
        ‖Gen.Rates.stack η.observation - Gen.Rates.stack θ.observation‖) ∧
    parameterDist D Y r Γ η θ ≤ max (2 / κ) (DK / Δ) *
      ‖Gen.Rates.stack η.observation - Gen.Rates.stack θ.observation‖ := by
  have hl := gen_local D Y r Γ θ η hc.kappa_pos hc.curvature_nonneg hc.radius_pos
    hc.curvature_radius (hc.jacobian θ hθ) (hc.hessian θ hθ)
  have hs := hsep η hη θ hθ
  have hd := hdiam η hη θ hθ
  exact ⟨fun he => hl (Gen.Rates.strict_localization hs he).le,
    Gen.Rates.global_inverse_composition (norm_nonneg _) hΔ
      ((parameterDist_nonneg D Y r Γ η θ).trans hd) hd hl hs⟩

/-- Actual model specialization of RATE's sampling interface, still explicitly
conditional on deterministic separation and quantitative local conditions. -/
theorem rate_stat (Γ : Subgroup (Gen.W D r))
    (K : Set (Gen.Parameter D Y r)) {κ M R Δ DK : ℝ}
    (hc : LocalConditions D Y r K κ M R) (hΔ : 0 < Δ)
    (hdiam : ∀ θ ∈ K, ∀ η ∈ K, parameterDist D Y r Γ θ η ≤ DK)
    (hsep : ∀ θ ∈ K, ∀ η ∈ K, R ≤ parameterDist D Y r Γ θ η →
      Δ ≤ ‖Gen.Rates.stack θ.observation - Gen.Rates.stack η.observation‖)
    {Ω : Type*} [Fintype Ω] (O : Ext.ObservationExperiment D.Edge (D.Outcome Y))
    (μ : Ext.FiniteLaw Ω) (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (θ : Gen.Parameter D Y r) (fit : Ω → Gen.Parameter D Y r)
    (hθ : θ ∈ K) (hfit : ∀ ω, fit ω ∈ K)
    {δ τ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmiss : ‖Gen.Rates.stack (fun e => (O.law e).mass) - Gen.Rates.stack θ.observation‖ ≤ τ)
    (hopt : ∀ ω, ∀ ζ ∈ K,
      ‖Gen.Rates.stack (fit ω).observation - Gen.Rates.stack (O.empirical (obs ω))‖ ≤
        ‖Gen.Rates.stack ζ.observation - Gen.Rates.stack (O.empirical (obs ω))‖ + ε) :
    1 - δ ≤ μ.prob (fun ω =>
      ‖Gen.Rates.stack (fit ω).observation - Gen.Rates.stack θ.observation‖ ≤
        2 * (τ + Gen.Rates.samplingRadius O δ) + ε ∧
      parameterDist D Y r Γ (fit ω) θ ≤ min DK (max (2 / κ) (DK / Δ) *
        (2 * (τ + Gen.Rates.samplingRadius O δ) + ε)) ∧
      (2 * (τ + Gen.Rates.samplingRadius O δ) + ε < Δ →
        parameterDist D Y r Γ (fit ω) θ ≤ min DK ((2 / κ) *
          (2 * (τ + Gen.Rates.samplingRadius O δ) + ε)))) := by
  letI : Nonempty D.Edge := D.edge_nonempty
  have hd : 0 ≤ DK := (parameterDist_nonneg D Y r Γ θ θ).trans (hdiam θ hθ θ hθ)
  exact Gen.Rates.rate_stat_full_interface (Θ := Gen.Parameter D Y r) O μ obs hIID
    (fun ζ : Gen.Parameter D Y r => Gen.Rates.stack ζ.observation) K θ fit (parameterDist D Y r Γ)
    hδ hδ1 hd hc.kappa_pos hΔ hθ hfit hmiss hopt hdiam
    (fun a ha b hb => gen_local D Y r Γ b a hc.kappa_pos hc.curvature_nonneg
      hc.radius_pos hc.curvature_radius (hc.jacobian b hb) (hc.hessian b hb)) hsep


/-- The unchanged GEN absolute-residual interface on the actual model.
Observation, global and strict-localized parameter bounds share one event. -/
theorem gen_stat (Γ : Subgroup (Gen.W D r))
    (K : Set (Gen.Parameter D Y r)) {κ M R Δ DK : ℝ}
    (hc : LocalConditions D Y r K κ M R) (hΔ : 0 < Δ)
    (hdiam : ∀ θ ∈ K, ∀ η ∈ K, parameterDist D Y r Γ θ η ≤ DK)
    (hsep : ∀ θ ∈ K, ∀ η ∈ K, R ≤ parameterDist D Y r Γ θ η →
      Δ ≤ ‖Gen.Rates.stack θ.observation - Gen.Rates.stack η.observation‖)
    {Ω : Type*} [Fintype Ω] (O : Ext.ObservationExperiment D.Edge (D.Outcome Y))
    (μ : Ext.FiniteLaw Ω) (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (θ : Gen.Parameter D Y r) (fit : Ω → Gen.Parameter D Y r)
    (hθ : θ ∈ K) (hfit : ∀ ω, fit ω ∈ K)
    {δ τ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmiss : ‖Gen.Rates.stack (fun e => (O.law e).mass) - Gen.Rates.stack θ.observation‖ ≤ τ)
    (hres : ∀ ω,
      ‖Gen.Rates.stack (fit ω).observation - Gen.Rates.stack (O.empirical (obs ω))‖ ≤
        τ + Gen.Rates.samplingRadius O δ + ε) :
    1 - δ ≤ μ.prob (fun ω =>
      ‖Gen.Rates.stack (fit ω).observation - Gen.Rates.stack θ.observation‖ ≤
        2 * (τ + Gen.Rates.samplingRadius O δ) + ε ∧
      parameterDist D Y r Γ (fit ω) θ ≤ max (2 / κ) (DK / Δ) *
        (2 * (τ + Gen.Rates.samplingRadius O δ) + ε) ∧
      (2 * (τ + Gen.Rates.samplingRadius O δ) + ε < Δ →
        parameterDist D Y r Γ (fit ω) θ ≤ (2 / κ) *
          (2 * (τ + Gen.Rates.samplingRadius O δ) + ε))) := by
  letI : Nonempty D.Edge := D.edge_nonempty
  apply (Gen.Rates.stacked_hoeffding O μ obs hIID hδ hδ1).trans (μ.prob_mono ?_)
  intro ω hω
  have he := Gen.Rates.residual_transfer hω hmiss (hres ω)
  have hg := gen_global D Y r Γ K hc hΔ hdiam hsep θ (fit ω) hθ (hfit ω)
  have hκ := hc.kappa_pos
  refine ⟨he, hg.2.trans (mul_le_mul_of_nonneg_left he ?_), ?_⟩
  · exact (show 0 ≤ 2 / κ by positivity).trans (le_max_left _ _)
  · intro hsmall
    exact (hg.1 (he.trans_lt hsmall)).trans (mul_le_mul_of_nonneg_left he (by positivity))

end Gen.RateBridge
