import Gen.Conditioned
import Gen.Uniqueness
import Gen.Separation
import Gen.RateBridge
import Gen.Estimator
import Gen.Hessian
import Gen.Jacobian

set_option maxHeartbeats 1600000
open scoped BigOperators Classical
noncomputable section
namespace Gen.ConditionedRates
open Gen.Geometry Gen.Conditioned

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

abbrev distance (x y : Ambient D Y r) : ℝ := Gen.Rates.orbitDist (Γ := Gen.W D r) x y

/-- Exact complete-W right-pullback minimum for the original parameter arrays. -/
theorem distance_embed_eq_min (θ η : Gen.Parameter D Y r) :
    distance D Y r (embed D Y r θ) (embed D Y r η) =
      Finset.univ.inf' Finset.univ_nonempty
        (fun q : Gen.W D r => ‖embed D Y r θ - embed D Y r (η.permute q)‖) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro q _
    have h := Gen.Rates.orbitDist_le (embed D Y r θ) (embed D Y r η) q⁻¹
    simpa only [distance, dist_eq_norm, embed_permute] using h
  · obtain ⟨q,hq⟩ := Gen.Rates.orbitDist_attained (Γ := Gen.W D r) (embed D Y r θ) (embed D Y r η)
    change _ ≤ Gen.Rates.orbitDist (Γ := Gen.W D r) (embed D Y r θ) (embed D Y r η)
    rw [hq]
    have h := Finset.inf'_le (fun q : Gen.W D r => ‖embed D Y r θ - embed D Y r (η.permute q)‖)
      (Finset.mem_univ q⁻¹)
    simpa only [embed_permute, inv_inv, dist_eq_norm] using h

theorem observation_toParameter {w₀ σ : ℝ} (hw : 0 < w₀)
    (x : Ambient D Y r) (hx : x ∈ K D Y r w₀ σ) :
    observation D Y r x = Gen.Rates.stack (toParameter hw x hx).observation := by
  rw [← observation_embed, embed_toParameter]

theorem observation_smul_on_K {w₀ σ : ℝ} (hw : 0 < w₀)
    (y : Ambient D Y r) (hy : y ∈ K D Y r w₀ σ) (q : Gen.W D r) :
    observation D Y r (q • y) = observation D Y r y := by
  have ha : embed D Y r ((toParameter hw y hy).permute q⁻¹) = q • y := by
    simp only [embed_permute, inv_inv, embed_toParameter]
  rw [← ha, observation_embed, observation_toParameter D Y r hw y hy]
  congr 1
  funext e x
  exact (toParameter hw y hy).permute_observation q⁻¹ e x

/-- RATE-D3 for the actual full real conditioned set. Full rank follows from the
positive Gram margin; no uniqueness or inverse oracle is assumed. -/
theorem observation_eq_iff_distance_zero {w₀ σ : ℝ}
    (hw : 0 < w₀) (hσ : 0 < σ) (hr : 0 < r)
    (x y : Ambient D Y r) (hx : x ∈ K D Y r w₀ σ) (hy : y ∈ K D Y r w₀ σ) :
    observation D Y r x = observation D Y r y ↔ distance D Y r x y = 0 := by
  constructor
  · intro heq
    have ho : ∀ e z, (toParameter hw x hx).observation e z = (toParameter hw y hy).observation e z := by
      rw [observation_toParameter D Y r hw x hx, observation_toParameter D Y r hw y hy] at heq
      intro e z
      exact congrArg (fun v : Geometry.ObservationSpace D Y => v ⟨e,z⟩) heq
    have hfull : Gen.FullColumnRank (toParameter hw y hy) :=
      fun g => toParameter_fullColumnRank hw hσ y hy g
    obtain ⟨q,hq⟩ := (Gen.fullColumnRank_observation_eq_iff
      (toParameter hw y hy) (toParameter hw x hx) hr hfull).mp ho
    apply (Gen.Rates.orbitDist_eq_zero_iff x y).2
    refine ⟨q⁻¹, ?_⟩
    have h := congrArg (embed D Y r) hq
    simpa only [embed_toParameter, embed_permute] using h
  · intro hz
    obtain ⟨q,rfl⟩ := (Gen.Rates.orbitDist_eq_zero_iff x y).mp hz
    exact observation_smul_on_K D Y r hw y hy q

/-- Actual stochastic parameter diameter, with every coordinate counted once. -/
theorem distance_diameter {w₀ σ : ℝ} (hw : 0 < w₀)
    (x y : Ambient D Y r) (hx : x ∈ K D Y r w₀ σ) (hy : y ∈ K D Y r w₀ σ) :
    distance D Y r x y ≤ Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) := by
  have h := Gen.Rates.orbitDist_le x y (1 : Gen.W D r)
  simp only [one_smul, dist_eq_norm] at h
  have hd := parameter_diameter D Y r (toParameter hw x hx) (toParameter hw y hy)
  simp only [embed_toParameter] at hd
  exact h.trans hd

theorem diameter_pos : 0 < Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) := by
  have hC : 0 < Fintype.card D.Component :=
    Fintype.card_pos_iff.mpr (Nonempty.map D.component D.edge_nonempty)
  have hCR : (0:ℝ) < Fintype.card D.Component := by exact_mod_cast hC
  unfold Gen.Constants.diameter
  positivity

/-- A genuine positive separation exists on the complete real K, including the
empty-far-set branch. This is qualitative, not effective RATE-CONSTANTS. -/
theorem exists_positive_separation {w₀ σ R : ℝ}
    (hw : 0 < w₀) (hσ : 0 < σ) (hr : 0 < r) (hR : 0 < R) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      R ≤ distance D Y r x y → Δ ≤ ‖observation D Y r x - observation D Y r y‖ := by
  have h := Gen.Separation.compact_positive_separation (K D Y r w₀ σ)
    (isCompact_K hw.le) (observation D Y r) (observation_continuous D Y r)
    (distance D Y r) (Gen.Rates.continuous_orbitDist (Γ := Gen.W D r))
    (fun x hx y hy heq => (observation_eq_iff_distance_zero D Y r hw hσ hr x y hx hy).mp heq) hR
  simpa only [dist_eq_norm] using h

/-- Explicit dependency interface for the derivative bounds still to be derived
from RATE's literal margins. These are quantified actual derivatives, not remainders. -/
structure DerivativeBounds (w₀ σ κ M R : ℝ) : Prop where
  kappa_pos : 0 < κ
  curvature_nonneg : 0 ≤ M
  radius_pos : 0 < R
  curvature_radius : M * R ≤ κ
  jacobian : ∀ θ ∈ K D Y r w₀ σ, ∀ v ∈ tangent D Y r,
    κ * ‖v‖ ≤ ‖fderiv ℝ (observation D Y r) θ v‖
  hessian : ∀ θ ∈ K D Y r w₀ σ, ∀ x : Ambient D Y r,
    Normalized D Y r x → ‖x - θ‖ ≤ R → ∀ u ∈ tangent D Y r, ∀ v ∈ tangent D Y r,
      ‖fderiv ℝ (fderiv ℝ (observation D Y r)) x u v‖ ≤ M * ‖u‖ * ‖v‖


/-- Literal number of observed cells, with full alphabets retained. -/
def cells : ℕ := ∑ e : D.Edge, ∏ g : D.GroupAt e, Fintype.card (Y g.val)

theorem cells_eq_card : cells D Y = Fintype.card ((e : D.Edge) × D.Outcome Y e) := by
  simp [cells, Fintype.card_sigma, Ext.TripleDesign.Outcome, Fintype.card_pi]

theorem totalCells_eq_cells (O : Ext.ObservationExperiment D.Edge (D.Outcome Y)) :
    O.totalCells = cells D Y := by
  simp [Ext.ObservationExperiment.totalCells, cells, Ext.TripleDesign.Outcome, Fintype.card_pi]

/-- Literal RATE curvature constant M=12 sqrt(m). -/
def curvature : ℝ := 12 * Real.sqrt (cells D Y)

/-- The accepted normalized radius R=min(1,kappa/M). -/
def radius (κ : ℝ) : ℝ := min 1 (κ / curvature D Y)

theorem cells_pos {w₀ σ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty) :
    0 < cells D Y := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨e⟩ := D.edge_nonempty
  have hneX : Nonempty (D.Outcome Y e) :=
    Fintype.card_pos_iff.mp ((toParameter hw x hx).observationLaw e).card_pos
  obtain ⟨y⟩ := hneX
  rw [cells_eq_card]
  exact Fintype.card_pos_iff.mpr ⟨⟨e,y⟩⟩

theorem curvature_pos {w₀ σ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty) :
    0 < curvature D Y := by
  have hm : (0:ℝ) < cells D Y := by exact_mod_cast cells_pos D Y r hw hne
  unfold curvature
  positivity

theorem radius_pos {w₀ σ κ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty) (hκ : 0 < κ) :
    0 < radius D Y κ := lt_min (by norm_num) (div_pos hκ (curvature_pos D Y r hw hne))

theorem radius_le_one (κ : ℝ) : radius D Y κ ≤ 1 := min_le_left _ _

theorem curvature_radius_le {w₀ σ κ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty) :
    curvature D Y * radius D Y κ ≤ κ := by
  have hM := curvature_pos D Y r hw hne
  calc
    curvature D Y * radius D Y κ ≤ curvature D Y * (κ / curvature D Y) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
    _ = κ := by field_simp

/-- The full ambient Hessian constant is derived from the quartic polynomial.
No normalized or nonnegative restriction is imposed on the perturbed point. -/
theorem hessian_bound {w₀ σ : ℝ} (hw : 0 < w₀)
    (θ : Ambient D Y r) (hθ : θ ∈ K D Y r w₀ σ)
    (x u v : Ambient D Y r) (hx : ‖x - θ‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (observation D Y r)) x u v‖ ≤ curvature D Y * ‖u‖ * ‖v‖ := by
  have h := Gen.Hessian.observation_hessian_bound D Y r (toParameter hw θ hθ) x u v
    (by simpa only [embed_toParameter] using hx)
  simpa only [curvature, cells_eq_card] using h

/-- Compositional assembly from an actual quantitative Jacobian lower theorem.
The literal lower theorem is instantiated by literal_derivativeBounds below. -/
theorem derivativeBounds_of_jacobian {w₀ σ κ : ℝ} (hw : 0 < w₀)
    (hne : (K D Y r w₀ σ).Nonempty) (hκ : 0 < κ)
    (hJ : ∀ θ ∈ K D Y r w₀ σ, ∀ v ∈ tangent D Y r,
      κ * ‖v‖ ≤ ‖fderiv ℝ (observation D Y r) θ v‖) :
    DerivativeBounds D Y r w₀ σ κ (curvature D Y) (radius D Y κ) := by
  refine ⟨hκ, (curvature_pos D Y r hw hne).le, radius_pos D Y r hw hne hκ,
    curvature_radius_le D Y r hw hne, hJ, ?_⟩
  intro θ hθ x _ hx u _ v _
  exact hessian_bound D Y r hw θ hθ x u v (hx.trans (radius_le_one D Y κ))


local instance edgeNonempty : Nonempty D.Edge := D.edge_nonempty

/-- The literal reciprocal maximum built from a_g and b_e, not an input oracle. -/
def kappa (w₀ σ : ℝ) : ℝ :=
  Gen.Constants.kappa (fun e : D.Edge => e.val) (fun g => Fintype.card (Y g)) w₀ σ

theorem kappa_pos {w₀ σ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ) : 0 < kappa D Y w₀ σ :=
  Gen.Constants.kappa_pos (fun e : D.Edge => e.val) (fun g => Fintype.card (Y g)) hw hσ

theorem curvature_eq_constants : curvature D Y = Gen.Constants.curvature (cells D Y) := rfl

theorem radius_eq_constants (w₀ σ : ℝ) : radius D Y (kappa D Y w₀ σ) =
    Gen.Constants.radius (fun e : D.Edge => e.val) (fun g => Fintype.card (Y g)) w₀ σ (cells D Y) := rfl

/-- Literal RATE-D2 Jacobian lower bound on every real point of the actual K. -/
theorem jacobian_bound {w₀ σ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ)
    (θ : Ambient D Y r) (hθ : θ ∈ K D Y r w₀ σ) (v : Ambient D Y r)
    (hv : v ∈ tangent D Y r) :
    kappa D Y w₀ σ * ‖v‖ ≤ ‖fderiv ℝ (observation D Y r) θ v‖ := by
  have h := Gen.Jacobian.observation_jacobian_lower_bound D Y r (toParameter hw θ hθ)
    v hv w₀ σ hw hσ hθ.2.1 hθ.2.2.2
  simpa only [kappa, embed_toParameter] using h

/-- All actual analytic conditions are derived with the exact accepted κ,M,R.
No derivative, Taylor remainder, singular value, or local inverse is assumed. -/
theorem literal_derivativeBounds {w₀ σ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ)
    (hne : (K D Y r w₀ σ).Nonempty) :
    DerivativeBounds D Y r w₀ σ (kappa D Y w₀ σ) (curvature D Y)
      (radius D Y (kappa D Y w₀ σ)) :=
  derivativeBounds_of_jacobian D Y r hw hne (kappa_pos D Y hw hσ)
    (jacobian_bound D Y r hw hσ)

/-- Every declared admissible family has the exact analytic bounds, using the
proved identity-column nonemptiness witness rather than a feasibility oracle. -/
theorem admitted_derivativeBounds {w₀ σ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ)
    (hr : 0 < r) (hn : ∀ g, r ≤ Fintype.card (Y g)) (hwupper : w₀ ≤ 1 / r) (hσ1 : σ ≤ 1) :
    DerivativeBounds D Y r w₀ σ (kappa D Y w₀ σ) (curvature D Y)
      (radius D Y (kappa D Y w₀ σ)) :=
  literal_derivativeBounds D Y r hw hσ (nonempty_K hr hn hwupper hσ.le hσ1)

/-- Analytic inverse on actual K from the displayed derivative conditions. -/
theorem local_inverse {w₀ σ κ M R : ℝ} (hw : 0 < w₀)
    (hb : DerivativeBounds D Y r w₀ σ κ M R)
    (x y : Ambient D Y r) (hx : x ∈ K D Y r w₀ σ) (hy : y ∈ K D Y r w₀ σ)
    (hnear : distance D Y r y x ≤ R) :
    distance D Y r y x ≤ (2 / κ) * ‖observation D Y r y - observation D Y r x‖ := by
  apply Gen.Rates.orbit_local_inverse (Γ := Gen.W D r)
    (observation D Y r) (fderiv ℝ (observation D Y r))
    (fderiv ℝ (fderiv ℝ (observation D Y r))) (tangent D Y r) x y
    (fun q => observation_smul_on_K D Y r hw y hy q)
    (fun q => sub_mem_tangent D Y r (smul_mem_K hw hy q).1 hx.1)
    hb.kappa_pos hb.curvature_nonneg hb.radius_pos hb.curvature_radius hnear
    (fun z _ _ => Gen.RateBridge.observation_hasFDerivAt D Y r z)
    (fun z _ _ => Gen.RateBridge.observation_derivative_hasFDerivAt D Y r z)
    (hb.jacobian x hx)
  intro z hz hzr
  exact hb.hessian x hx z (Gen.RateBridge.normalized_of_sub_mem D Y r hx.1 hz) hzr

/-- Valid-separation conditional global inverse with the literal stochastic diameter. -/
theorem global_inverse {w₀ σ κ M R Δ : ℝ} (hw : 0 < w₀)
    (hb : DerivativeBounds D Y r w₀ σ κ M R) (hΔ : 0 < Δ)
    (hsep : ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      R ≤ distance D Y r x y → Δ ≤ ‖observation D Y r x - observation D Y r y‖)
    (x y : Ambient D Y r) (hx : x ∈ K D Y r w₀ σ) (hy : y ∈ K D Y r w₀ σ) :
    distance D Y r x y ≤ max (2 / κ)
      (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / Δ) *
      ‖observation D Y r x - observation D Y r y‖ := by
  have hd := distance_diameter D Y r hw x y hx hy
  exact Gen.Rates.global_inverse_composition (norm_nonneg _) hΔ
    ((Gen.Rates.orbitDist_nonneg x y).trans hd) hd
    (local_inverse D Y r hw hb y x hy hx) (hsep x hx y hy)

/-- Exact mathematical baseline on the actual conditioned K, with supplied coordinate order. -/
def baseline {w₀ σ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    (data : Geometry.ObservationSpace D Y) : Ambient D Y r :=
  Gen.Estimator.orderedLeastSquares order (K D Y r w₀ σ) (isCompact_K hw.le) hne
    (observation D Y r) (observation_continuous D Y r) data

theorem baseline_mem {w₀ σ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    (data : Geometry.ObservationSpace D Y) : baseline D Y r hw hne order data ∈ K D Y r w₀ σ :=
  Gen.Estimator.orderedLeastSquares_mem _ _ _ _ _ _ _

theorem baseline_optimal {w₀ σ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    (data : Geometry.ObservationSpace D Y) :
    ∀ y ∈ K D Y r w₀ σ,
      ‖observation D Y r (baseline D Y r hw hne order data) - data‖ ≤ ‖observation D Y r y - data‖ :=
  Gen.Estimator.orderedLeastSquares_optimal _ _ _ _ _ _ _

theorem baseline_lexLeast {w₀ σ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    (data : Geometry.ObservationSpace D Y) :
    Gen.Estimator.OrderedLexLeast order
      (Gen.Estimator.minimizers (K D Y r w₀ σ) (fun x => ‖observation D Y r x - data‖^2))
      (baseline D Y r hw hne order data) :=
  Gen.Estimator.orderedLeastSquares_lexLeast _ _ _ _ _ _ _

/-- The chosen coordinate array really is a Xi_r parameter, not a relaxed point. -/
def baselineParameter {w₀ σ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    (data : Geometry.ObservationSpace D Y) : Gen.Parameter D Y r :=
  toParameter hw (baseline D Y r hw hne order data) (baseline_mem D Y r hw hne order data)

@[simp] theorem baselineParameter_embed {w₀ σ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    (data : Geometry.ObservationSpace D Y) :
    embed D Y r (baselineParameter D Y r hw hne order data) = baseline D Y r hw hne order data :=
  embed_toParameter _ _ _

/-- The baseline's global objective comparison is also stated on the original
Xi_r parameter type with all same-r conditioned real competitors. -/
theorem baselineParameter_optimal {w₀ σ : ℝ} (hw : 0 < w₀) (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    (data : Geometry.ObservationSpace D Y) (ζ : Gen.Parameter D Y r)
    (hζ : embed D Y r ζ ∈ K D Y r w₀ σ) :
    ‖Gen.Rates.stack (baselineParameter D Y r hw hne order data).observation - data‖ ≤
      ‖Gen.Rates.stack ζ.observation - data‖ := by
  have h := baseline_optimal D Y r hw hne order data (embed D Y r ζ) hζ
  rw [← baselineParameter_embed D Y r hw hne order data, observation_embed, observation_embed] at h
  exact h

/-- Mathematical baseline existence for every admitted design and margin input.
The output is a function of data only; all realizations receive a global optimum. -/
theorem baseline_all_outcomes {w₀ σ : ℝ} (hw : 0 < w₀)
    (hr : 0 < r) (hn : ∀ g, r ≤ Fintype.card (Y g))
    (hwupper : w₀ ≤ 1 / r) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    {Ω : Type*} (data : Ω → Geometry.ObservationSpace D Y) :
    ∃ fit : Ω → Ambient D Y r, (∀ ω, fit ω ∈ K D Y r w₀ σ) ∧
      (∀ ω, ∀ y ∈ K D Y r w₀ σ,
        ‖observation D Y r (fit ω) - data ω‖ ≤ ‖observation D Y r y - data ω‖) ∧
      ∀ ω, Gen.Estimator.OrderedLexLeast order
        (Gen.Estimator.minimizers (K D Y r w₀ σ) (fun x => ‖observation D Y r x - data ω‖^2)) (fit ω) := by
  have hne := nonempty_K (D := D) (Y := Y) hr hn hwupper hσ0 hσ1
  exact Gen.Estimator.orderedLeastSquares_all_outcomes order data (K D Y r w₀ σ)
    (isCompact_K hw.le) hne (observation D Y r) (observation_continuous D Y r)

/-- Actual conditioned RATE-S, conditional only on the displayed derivative bounds
and a valid separation number. The prerequisite interfaces are not asserted as algorithms. -/
theorem rate_stat {w₀ σ κ M R Δ : ℝ} (hw : 0 < w₀)
    (hb : DerivativeBounds D Y r w₀ σ κ M R) (hΔ : 0 < Δ)
    (hsep : ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      R ≤ distance D Y r x y → Δ ≤ ‖observation D Y r x - observation D Y r y‖)
    {Ω : Type*} [Fintype Ω] (O : Ext.ObservationExperiment D.Edge (D.Outcome Y))
    (μ : Ext.FiniteLaw Ω) (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (θ : Ambient D Y r) (fit : Ω → Ambient D Y r)
    (hθ : θ ∈ K D Y r w₀ σ) (hfit : ∀ ω, fit ω ∈ K D Y r w₀ σ)
    {δ τ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmiss : ‖Gen.Rates.stack (fun e => (O.law e).mass) - observation D Y r θ‖ ≤ τ)
    (hopt : ∀ ω, ∀ ζ ∈ K D Y r w₀ σ,
      ‖observation D Y r (fit ω) - Gen.Rates.stack (O.empirical (obs ω))‖ ≤
        ‖observation D Y r ζ - Gen.Rates.stack (O.empirical (obs ω))‖ + ε) :
    1 - δ ≤ μ.prob (fun ω =>
      ‖observation D Y r (fit ω) - observation D Y r θ‖ ≤
        2 * (τ + Gen.Rates.samplingRadius O δ) + ε ∧
      distance D Y r (fit ω) θ ≤ min (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G))
        (max (2 / κ) (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / Δ) *
          (2 * (τ + Gen.Rates.samplingRadius O δ) + ε)) ∧
      (2 * (τ + Gen.Rates.samplingRadius O δ) + ε < Δ →
        distance D Y r (fit ω) θ ≤ min (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G))
          ((2 / κ) * (2 * (τ + Gen.Rates.samplingRadius O δ) + ε)))) := by
  letI : Nonempty D.Edge := D.edge_nonempty
  have hdiam := distance_diameter D Y r (σ := σ) hw
  have hD := (Gen.Rates.orbitDist_nonneg (Γ := Gen.W D r) θ θ).trans (hdiam θ θ hθ hθ)
  exact Gen.Rates.rate_stat_full_interface (Θ := Ambient D Y r) O μ obs hIID
    (observation D Y r) (K D Y r w₀ σ) θ fit (distance D Y r)
    hδ hδ1 hD hb.kappa_pos hΔ hθ hfit hmiss hopt
    (fun x hx y hy => hdiam x y hx hy)
    (fun x hx y hy => local_inverse D Y r hw hb y x hy hx) hsep

/-- RATE-S for the actual lexicographic least-squares baseline, so no optimizer
existence/convergence premise remains. Effective computation is still not asserted. -/
theorem baseline_rate_stat {w₀ σ κ M R Δ : ℝ} (hw : 0 < w₀)
    (hb : DerivativeBounds D Y r w₀ σ κ M R) (hΔ : 0 < Δ)
    (hsep : ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      R ≤ distance D Y r x y → Δ ≤ ‖observation D Y r x - observation D Y r y‖)
    (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    {Ω : Type*} [Fintype Ω] (O : Ext.ObservationExperiment D.Edge (D.Outcome Y))
    (μ : Ext.FiniteLaw Ω) (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (θ : Ambient D Y r) (hθ : θ ∈ K D Y r w₀ σ)
    {δ τ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmiss : ‖Gen.Rates.stack (fun e => (O.law e).mass) - observation D Y r θ‖ ≤ τ) :
    1 - δ ≤ μ.prob (fun ω =>
      let fit := baseline D Y r hw hne order (Gen.Rates.stack (O.empirical (obs ω)))
      ‖observation D Y r fit - observation D Y r θ‖ ≤ 2 * (τ + Gen.Rates.samplingRadius O δ) ∧
      distance D Y r fit θ ≤ min (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G))
        (max (2 / κ) (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / Δ) *
          (2 * (τ + Gen.Rates.samplingRadius O δ))) ∧
      (2 * (τ + Gen.Rates.samplingRadius O δ) < Δ →
        distance D Y r fit θ ≤ min (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G))
          ((2 / κ) * (2 * (τ + Gen.Rates.samplingRadius O δ))))) := by
  have h := rate_stat D Y r hw hb hΔ hsep O μ obs hIID θ
    (fun ω => baseline D Y r hw hne order (Gen.Rates.stack (O.empirical (obs ω)))) hθ
    (fun ω => baseline_mem D Y r hw hne order _) hδ hδ1 hmiss
    (ε := 0) (fun ω ζ hζ => by simpa using (baseline_optimal D Y r hw hne order (Gen.Rates.stack (O.empirical (obs ω))) ζ hζ))
  simpa only [add_zero] using h

/-- With positive Gram margins, compactness and proved full-rank uniqueness supply
some positive separation and hence a global inverse. No computable Delta is claimed. -/
theorem qualitative_global_inverse {w₀ σ κ M R : ℝ} (hw : 0 < w₀)
    (hσ : 0 < σ) (hr : 0 < r) (hb : DerivativeBounds D Y r w₀ σ κ M R) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      distance D Y r x y ≤ max (2 / κ)
        (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / Δ) *
        ‖observation D Y r x - observation D Y r y‖ := by
  obtain ⟨Δ,hΔ,hsep⟩ := exists_positive_separation D Y r hw hσ hr hb.radius_pos
  exact ⟨Δ,hΔ,fun x hx y hy => global_inverse D Y r hw hb hΔ hsep x y hx hy⟩

/-- The actual lexicographic baseline and literal count rule give the informative
19/20, half-diameter regime for any exactly specified target law on K. -/
theorem baseline_informative {w₀ σ κ M R Δ : ℝ} (hw : 0 < w₀)
    (hb : DerivativeBounds D Y r w₀ σ κ M R) (hΔ : 0 < Δ)
    (hsep : ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      R ≤ distance D Y r x y → Δ ≤ ‖observation D Y r x - observation D Y r y‖)
    (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    {Ω : Type*} [Fintype Ω] (O : Ext.ObservationExperiment D.Edge (D.Outcome Y))
    (μ : Ext.FiniteLaw Ω) (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (θ : Ambient D Y r) (hθ : θ ∈ K D Y r w₀ σ)
    (htrue : Gen.Rates.stack (fun e => (O.law e).mass) = observation D Y r θ)
    (N : ℕ) (hN : ∀ e, O.n e = N)
    (hcount : Gen.Rates.informativeCount (O.totalCells : ℝ)
      (min (κ * Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / 8) (Δ / 4)) ≤ N) :
    (19 / 20 : ℝ) ≤ μ.prob (fun ω => distance D Y r
      (baseline D Y r hw hne order (Gen.Rates.stack (O.empirical (obs ω)))) θ ≤
        Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / 2) := by
  letI : Nonempty D.Edge := D.edge_nonempty
  exact Gen.Rates.rate_stat_informative (Θ := Ambient D Y r) O μ obs hIID
    (observation D Y r) (K D Y r w₀ σ) θ
    (fun ω => baseline D Y r hw hne order (Gen.Rates.stack (O.empirical (obs ω))))
    (distance D Y r) hb.kappa_pos (diameter_pos D r) hΔ hθ
    (fun ω => baseline_mem D Y r hw hne order _) htrue
    (fun ω ζ hζ => baseline_optimal D Y r hw hne order _ ζ hζ)
    (fun x hx y hy => local_inverse D Y r hw hb y x hy hx) hsep N hN hcount

/-- Explicit RATE local inverse, with every conditioning constant derived. -/
theorem literal_local_inverse {w₀ σ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ)
    (x y : Ambient D Y r) (hx : x ∈ K D Y r w₀ σ) (hy : y ∈ K D Y r w₀ σ)
    (hnear : distance D Y r y x ≤ radius D Y (kappa D Y w₀ σ)) :
    distance D Y r y x ≤ (2 / kappa D Y w₀ σ) * ‖observation D Y r y - observation D Y r x‖ :=
  local_inverse D Y r hw (literal_derivativeBounds D Y r hw hσ ⟨x,hx⟩) x y hx hy hnear

/-- Explicit global inverse for a supplied valid separation certificate.
Only the effective computation of Delta remains a separate obligation. -/
theorem literal_global_inverse {w₀ σ Δ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ) (hΔ : 0 < Δ)
    (hsep : ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      radius D Y (kappa D Y w₀ σ) ≤ distance D Y r x y →
        Δ ≤ ‖observation D Y r x - observation D Y r y‖)
    (x y : Ambient D Y r) (hx : x ∈ K D Y r w₀ σ) (hy : y ∈ K D Y r w₀ σ) :
    distance D Y r x y ≤ max (2 / kappa D Y w₀ σ)
      (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / Δ) *
      ‖observation D Y r x - observation D Y r y‖ :=
  global_inverse D Y r hw (literal_derivativeBounds D Y r hw hσ ⟨x,hx⟩) hΔ hsep x y hx hy

/-- No separation oracle is assumed in this qualitative existence result.
All analytic constants are literal; effective RATE-D4 is deliberately not claimed. -/
theorem literal_qualitative_global_inverse {w₀ σ : ℝ} (hw : 0 < w₀)
    (hσ : 0 < σ) (hr : 0 < r) (hne : (K D Y r w₀ σ).Nonempty) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      distance D Y r x y ≤ max (2 / kappa D Y w₀ σ)
        (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / Δ) *
        ‖observation D Y r x - observation D Y r y‖ :=
  qualitative_global_inverse D Y r hw hσ hr (literal_derivativeBounds D Y r hw hσ hne)


/-- Explicit literal-constant specialization: no Jacobian/Hessian or inverse hypothesis remains.
A valid separation Delta is still required, and effective QE is not claimed. -/
theorem literal_rate_stat {w₀ σ Δ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ) (hΔ : 0 < Δ)
    (hsep : ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      (radius D Y (kappa D Y w₀ σ)) ≤ distance D Y r x y → Δ ≤ ‖observation D Y r x - observation D Y r y‖)
    {Ω : Type*} [Fintype Ω] (O : Ext.ObservationExperiment D.Edge (D.Outcome Y))
    (μ : Ext.FiniteLaw Ω) (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (θ : Ambient D Y r) (fit : Ω → Ambient D Y r)
    (hθ : θ ∈ K D Y r w₀ σ) (hfit : ∀ ω, fit ω ∈ K D Y r w₀ σ)
    {δ τ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmiss : ‖Gen.Rates.stack (fun e => (O.law e).mass) - observation D Y r θ‖ ≤ τ)
    (hopt : ∀ ω, ∀ ζ ∈ K D Y r w₀ σ,
      ‖observation D Y r (fit ω) - Gen.Rates.stack (O.empirical (obs ω))‖ ≤
        ‖observation D Y r ζ - Gen.Rates.stack (O.empirical (obs ω))‖ + ε) :
    1 - δ ≤ μ.prob (fun ω =>
      ‖observation D Y r (fit ω) - observation D Y r θ‖ ≤
        2 * (τ + Gen.Rates.samplingRadius O δ) + ε ∧
      distance D Y r (fit ω) θ ≤ min (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G))
        (max (2 / (kappa D Y w₀ σ)) (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / Δ) *
          (2 * (τ + Gen.Rates.samplingRadius O δ) + ε)) ∧
      (2 * (τ + Gen.Rates.samplingRadius O δ) + ε < Δ →
        distance D Y r (fit ω) θ ≤ min (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G))
          ((2 / (kappa D Y w₀ σ)) * (2 * (τ + Gen.Rates.samplingRadius O δ) + ε)))) := by
  exact rate_stat D Y r hw (literal_derivativeBounds D Y r hw hσ ⟨θ,hθ⟩)
    hΔ hsep O μ obs hIID θ fit hθ hfit hδ hδ1 hmiss hopt

/-- Explicit literal-constant specialization: no Jacobian/Hessian or inverse hypothesis remains.
A valid separation Delta is still required, and effective QE is not claimed. -/
theorem literal_baseline_rate_stat {w₀ σ Δ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ) (hΔ : 0 < Δ)
    (hsep : ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      (radius D Y (kappa D Y w₀ σ)) ≤ distance D Y r x y → Δ ≤ ‖observation D Y r x - observation D Y r y‖)
    (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    {Ω : Type*} [Fintype Ω] (O : Ext.ObservationExperiment D.Edge (D.Outcome Y))
    (μ : Ext.FiniteLaw Ω) (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (θ : Ambient D Y r) (hθ : θ ∈ K D Y r w₀ σ)
    {δ τ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmiss : ‖Gen.Rates.stack (fun e => (O.law e).mass) - observation D Y r θ‖ ≤ τ) :
    1 - δ ≤ μ.prob (fun ω =>
      let fit := baseline D Y r hw hne order (Gen.Rates.stack (O.empirical (obs ω)))
      ‖observation D Y r fit - observation D Y r θ‖ ≤ 2 * (τ + Gen.Rates.samplingRadius O δ) ∧
      distance D Y r fit θ ≤ min (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G))
        (max (2 / (kappa D Y w₀ σ)) (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / Δ) *
          (2 * (τ + Gen.Rates.samplingRadius O δ))) ∧
      (2 * (τ + Gen.Rates.samplingRadius O δ) < Δ →
        distance D Y r fit θ ≤ min (Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G))
          ((2 / (kappa D Y w₀ σ)) * (2 * (τ + Gen.Rates.samplingRadius O δ))))) := by
  exact baseline_rate_stat D Y r hw (literal_derivativeBounds D Y r hw hσ hne)
    hΔ hsep hne order O μ obs hIID θ hθ hδ hδ1 hmiss

/-- Explicit literal-constant specialization: no Jacobian/Hessian or inverse hypothesis remains.
A valid separation Delta is still required, and effective QE is not claimed. -/
theorem literal_baseline_informative {w₀ σ Δ : ℝ} (hw : 0 < w₀) (hσ : 0 < σ) (hΔ : 0 < Δ)
    (hsep : ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      (radius D Y (kappa D Y w₀ σ)) ≤ distance D Y r x y → Δ ≤ ‖observation D Y r x - observation D Y r y‖)
    (hne : (K D Y r w₀ σ).Nonempty)
    (order : Coordinate D Y r ≃ Fin (Fintype.card (Coordinate D Y r)))
    {Ω : Type*} [Fintype Ω] (O : Ext.ObservationExperiment D.Edge (D.Outcome Y))
    (μ : Ext.FiniteLaw Ω) (obs : Ω → Ext.ObservationSpace O) (hIID : O.IID μ obs)
    (θ : Ambient D Y r) (hθ : θ ∈ K D Y r w₀ σ)
    (htrue : Gen.Rates.stack (fun e => (O.law e).mass) = observation D Y r θ)
    (N : ℕ) (hN : ∀ e, O.n e = N)
    (hcount : Gen.Rates.informativeCount (O.totalCells : ℝ)
      (min ((kappa D Y w₀ σ) * Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / 8) (Δ / 4)) ≤ N) :
    (19 / 20 : ℝ) ≤ μ.prob (fun ω => distance D Y r
      (baseline D Y r hw hne order (Gen.Rates.stack (O.empirical (obs ω)))) θ ≤
        Gen.Constants.diameter (Fintype.card D.Component) r (Fintype.card G) / 2) := by
  exact baseline_informative D Y r hw (literal_derivativeBounds D Y r hw hσ hne)
    hΔ hsep hne order O μ obs hIID θ hθ htrue N hN hcount

end Gen.ConditionedRates
