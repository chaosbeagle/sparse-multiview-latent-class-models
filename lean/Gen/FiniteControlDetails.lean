import Gen.FiniteControl

noncomputable section
namespace Gen.FiniteControl

lemma sqrt_two_ge_one : (1:ℝ) ≤ Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg (2:ℝ)]

lemma Bvalue_ge_one : (1:ℝ) ≤ Bvalue := by
  have hs := Bvalue_square
  nlinarith [Bvalue_pos, Real.sqrt_nonneg (2:ℝ)]

/-- The selected branch of the literal radius agrees with the accepted closed form. -/
theorem controlRadius_exact : controlRadius = 1 / (24 * Real.sqrt 2 * Bvalue) := by
  unfold controlRadius Gen.ConditionedRates.radius
  rw [kappa_exact, curvature_exact]
  have hm : 0 < 24 * Real.sqrt (2:ℝ) := by positivity
  have hk : 1 / Bvalue ≤ 1 := (div_le_iff₀ Bvalue_pos).mpr (by simpa using Bvalue_ge_one)
  have h : (1 / Bvalue) / (24 * Real.sqrt (2:ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith [sqrt_two_ge_one]
  rw [min_eq_right h]
  field_simp

theorem controlRadius_square_exact : controlRadius ^ 2 =
    1 / (1152 * (157 + 108 * Real.sqrt 2)) := by
  rw [controlRadius_exact, div_pow]
  simp only [one_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Bvalue_square]
  congr 1 <;> ring

/-- Delta=1 makes the literal global max coefficient exactly 2B. -/
theorem inverseCoefficient_exact :
    max (2 / Gen.ConditionedRates.kappa tripleDesign binaryAlphabet (1/2) 1)
      (Gen.Constants.diameter (Fintype.card tripleDesign.Component) 2 (Fintype.card (Fin 3)) / 1) =
        2 * Bvalue := by
  rw [kappa_exact,diameter_exact]
  have hs : Real.sqrt 14 ≤ 2 * Bvalue := by
    have h14 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 14)
    have hB := Bvalue_square
    nlinarith [Bvalue_pos, Real.sqrt_nonneg (14:ℝ), Real.sqrt_nonneg (2:ℝ)]
  have he : 2 / (1 / Bvalue) = 2 * Bvalue := by field_simp
  rw [he, div_one, max_eq_left hs]

end Gen.FiniteControl
