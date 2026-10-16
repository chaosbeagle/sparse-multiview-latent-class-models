import Cover.ScalarCoefficients
import Cover.CompletenessBridge

namespace Cover

theorem validatedCoefficients_uniform_error (n : Fin g → ℕ) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ [])
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ)
    {w₀ σ₀ : ℝ} (hwd : w.denotes w₀) (hσd : σ.denotes σ₀)
    (gs : Fin j → PolyExpr N 3) (H : PolyExpr N 3) :
    UniformEndpointError (validatedScalarCoefficients n edges r w σ h)
      ![w₀,σ₀^2,((Literal.R n edges).eval w₀ σ₀)^2] gs H :=
  uniformEndpointError_of_coefficient_refinement _ _ gs H
    (validatedScalarCoefficients_sound n hn he r w σ h hwd hσd)
    (validatedScalarCoefficients_widths_refine n hn he r w σ h)

/-- The all-stage scalar legality and interval approximation obligations are fully
discharged for validated algebraic margins and the literal radius. Only the
project-specific real feasible-set positivity bridge remains conditional here. -/
theorem coverStage_eventually_succeeds_of_validated_margins
    (n : Fin g → ℕ) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ [])
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ)
    {w₀ σ₀ : ℝ} (hwd : w.denotes w₀) (hσd : σ.denotes σ₀)
    (gs : Fin j → PolyExpr N 3) (H : PolyExpr N 3) (hN : 0 < N)
    (hgap : ∀ x, (unitBox N).Contains x →
      (∀ i, 0 ≤ (gs i).eval ![w₀,σ₀^2,((Literal.R n edges).eval w₀ σ₀)^2] x) →
      0 < H.eval ![w₀,σ₀^2,((Literal.R n edges).eval w₀ σ₀)^2] x) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, ∃ t,
      coverStage (validatedScalarCoefficients n edges r w σ h) gs H hN s = .success t :=
  coverStage_eventually_succeeds_of_positive _ _ gs H hN hgap
    (validatedCoefficients_uniform_error n hn he r w σ h hwd hσd gs H)

end Cover
