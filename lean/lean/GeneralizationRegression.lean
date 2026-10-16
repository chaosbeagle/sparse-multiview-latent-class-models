import Gen

open scoped BigOperators Classical
noncomputable section

/-- Regression protects the original full-real competitor domain. -/
example (m : Ext.Hidden.ModelH)
    (hm : ∀ x y z, m.observed x y z = Ext.Hidden.starObservation x y z) :
    ∃ j : Ext.Hidden.Latent ≃ Ext.Hidden.Output, m = Ext.Hidden.atomModel j :=
  Ext.Hidden.full_star_is_atom m hm

example : Ext.Hidden.fullImage = ({(1:ℝ)/2,1} : Set ℝ) := Ext.Hidden.fullImage_exact
example : Ext.Hidden.width Ext.Hidden.fullImage = (1:ℝ)/2 := Ext.Hidden.GEN_F_STAR.2.2.2.2.2.2

/-- Zero curvature is accepted by the proved analytic local theorem. -/
example (a y : ℝ) (hy : ‖y-a‖ ≤ 17) : ‖y-a‖ ≤ (2:ℝ) * ‖y-a‖ := by
  have h := Gen.Rates.local_inverse_of_jacobian_hessian
    (fun x : ℝ => x) (fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ => 0)
    a y (κ := 1) (M := 0) (R := 17) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hy (fun x _ => hasFDerivAt_id x)
    (fun x _ => hasFDerivAt_const (ContinuousLinearMap.id ℝ ℝ) x)
    (by intro v; simp) (by intro x hx u v; simp)
  simpa using h

example {d e R Δ : ℝ} (hsep : R ≤ d → Δ ≤ e) (hsmall : e < Δ) : d < R :=
  Gen.Rates.strict_localization hsep hsmall

/-- Literal finite-control constant arithmetic, independently of the as-yet-unreplayed
    finite-control h=1 certificate. -/
example (g : Fin 3) : Gen.Constants.a (fun _ : Fin 3 => 2) (1/2) 1 g =
    2 + 2 * Real.sqrt 2 := by
  norm_num [Gen.Constants.a]
  ring

example (e : Unit) : Gen.Constants.b (fun _ : Unit => (Finset.univ : Finset (Fin 3)))
    (fun _ => 2) (1/2) 1 e = 7 + 6 * Real.sqrt 2 := by
  norm_num [Gen.Constants.b, Gen.Constants.a, Finset.sum_const]
  ring

example : Gen.QEEncoding.rationalDyadicExponent (1/100) (by norm_num) = 4 :=
  Gen.QEEncoding.rational_example_exponent
example : Gen.QEEncoding.rationalDyadicSeparation (1/100) (by norm_num) = 1/16 :=
  Gen.QEEncoding.rational_example_separation

#check Gen.Diagonal.GEN_F_DIAGONAL
#check Gen.NoSemantic.GEN_G_NOSEM
#check Gen.ConditionedRates.literal_derivativeBounds
#check Gen.ConditionedRates.literal_baseline_informative
#check Gen.PrincipalMinors.posSemidef_iff_principalMinors
#check Gen.Jacobian.observation_jacobian_lower_bound
#check Gen.Hessian.observation_hessian_bound


/- The generic theorem is tested outside the full-column-rank scope. -/
#check Gen.KruskalWitness.parameter_outside_fullrank_scope
#check Gen.KruskalWitness.rank_deficient_full_fiber_identified
#check Gen.KruskalWitness.rank_deficient_localRigid
#check Gen.QuotientMetric.parameter_distance_eq_quotient

/- Full-real reduction precedes this exact finite-control replay. -/
#check Gen.FiniteControl.literal_minimum_one
#check Gen.FiniteControl.literal_delta_one
#check Gen.FiniteControl.prescribed_statistical_bound
example : Nat.ceil ((40960 / 7 : ℝ) * (157 + 108 * Real.sqrt 2)) = 1812393 :=
  Gen.FiniteControl.prescribed_count_exact
