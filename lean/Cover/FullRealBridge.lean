import Cover.ConcreteCompiler

open scoped BigOperators Classical
namespace Cover.FullRealBridge
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- The literal full Euclidean/Frobenius sum, counting each original coordinate once. -/
theorem rightPullback_norm_sq (θ η : Gen.Geometry.Ambient D Y r) (q : Gen.W D r) :
    ‖θ - q⁻¹ • η‖^2 =
      (∑ c, ∑ z, (θ (.inl (c,z)) - η (.inl (c,q c z)))^2) +
      ∑ g, ∑ z, ∑ y, (θ (.inr ⟨g,z,y⟩) - η (.inr ⟨g,q (D.groupComponent g) z,y⟩))^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_sigma,
    Gen.ModelEncoding.inverse_action_apply,Gen.Geometry.coordinatePerm]

/-- Observation invariance holds on the whole real ambient space. -/
theorem observation_rightPullback (θ : Gen.Geometry.Ambient D Y r) (q : Gen.W D r) :
    Gen.Geometry.observation D Y r (q⁻¹ • θ) = Gen.Geometry.observation D Y r θ := by
  ext ⟨e,x⟩
  change (∑ z, (q⁻¹ • θ) (.inl (D.component e,z)) *
    ∏ g : D.GroupAt e, (q⁻¹ • θ) (.inr ⟨g.val,z,x g⟩)) = _
  simp only [Gen.ModelEncoding.inverse_action_apply,Gen.Geometry.coordinatePerm,
    Equiv.coe_fn_mk]
  simp_rw [D.groupComponent_eq e]
  exact Equiv.sum_comp (q (D.component e))
    (fun z => θ (.inl (D.component e,z)) * ∏ g : D.GroupAt e, θ (.inr ⟨g.val,z,x g⟩))

/-- The finite all-permutation threshold is exactly the genuine quotient distance threshold. -/
theorem radius_le_fullDistance_iff (θ η : Gen.Geometry.Ambient D Y r) (R : ℝ) :
    R ≤ Gen.Rates.orbitDist (Γ := Gen.W D r) θ η ↔
      ∀ q : Gen.W D r, R ≤ ‖θ - q⁻¹ • η‖ := by
  constructor
  · intro h q
    exact h.trans (by simpa [dist_eq_norm] using Gen.Rates.orbitDist_le θ η q⁻¹)
  · intro h
    obtain ⟨q,hq⟩ := Gen.Rates.orbitDist_attained (Γ := Gen.W D r) θ η
    rw [hq,dist_eq_norm]
    simpa using h q⁻¹

open Cover.FiniteDesign Cover.Compiler Cover.ConcreteCompiler

theorem concrete_coverEncoding_iff_fullDistance (I : Syntax) (h : Valid I)
    (w σ R : ℝ) (hR : 0 ≤ R) (x : Fin (dimension I h + dimension I h) → ℝ) :
    nonnegative (ConcreteCompiler.constraints I h) (SquaredCompiler.coefficients w σ R) x ↔
      expandLeft I h x ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ ∧
      expandRight I h x ∈ Gen.Conditioned.K (toBaseline I h) (fun g => Fin (I.outputPred g+1)) (I.rankPred+1) w σ ∧
      R ≤ Gen.Rates.orbitDist (Γ := Gen.W (toBaseline I h) (I.rankPred+1)) (expandLeft I h x) (expandRight I h x) := by
  rw [ConcreteCompiler.coverEncoding_iff I h w σ R hR x,radius_le_fullDistance_iff]
end Cover.FullRealBridge
