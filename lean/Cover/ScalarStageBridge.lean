import Cover.ScalarConvergence
import Cover.CompletenessBridge

open Filter
open scoped Topology

namespace Cover

/-- The polynomial evaluator receives the actual certified outputs of a finite
literal scalar-expression family, with repeated leaves sharing their denotations. -/
theorem scalarBounds_imply_uniformEndpointError
    (ps : Fin a → ScalarExpr) (w σ : ℕ → QInterval) (w₀ σ₀ : ℝ)
    (hw : ∀ s, (w s).contains w₀) (hσ : ∀ s, (σ s).contains σ₀)
    (hww : Tendsto (fun s => ((w s).width : ℝ)) atTop (𝓝 0))
    (hσw : Tendsto (fun s => ((σ s).width : ℝ)) atTop (𝓝 0))
    (cs : ℕ → Fin a → QInterval)
    (hcs : ∀ s i, (ps i).bounds s (w s) (σ s) = some (cs s i))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) :
    UniformEndpointError cs (fun i => (ps i).eval w₀ σ₀) gs H :=
  uniformEndpointError_of_coefficient_refinement cs _ gs H
    (fun s i => (ps i).evalScalarBounds_sound (hw s) (hσ s) (hcs s i))
    (ScalarExpr.scalarFamily_widths_refine ps w σ w₀ σ₀ hw hσ hww hσw cs hcs)

/-- Fully concrete scalar/interval/stage composition. The remaining premise is the
actual model's positivity on the feasible set, not a uniform-error or halting oracle. -/
theorem coverStage_eventually_succeeds_of_scalar_bounds
    (ps : Fin a → ScalarExpr) (w σ : ℕ → QInterval) (w₀ σ₀ : ℝ)
    (hw : ∀ s, (w s).contains w₀) (hσ : ∀ s, (σ s).contains σ₀)
    (hww : Tendsto (fun s => ((w s).width : ℝ)) atTop (𝓝 0))
    (hσw : Tendsto (fun s => ((σ s).width : ℝ)) atTop (𝓝 0))
    (cs : ℕ → Fin a → QInterval)
    (hcs : ∀ s i, (ps i).bounds s (w s) (σ s) = some (cs s i))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n)
    (hgap : ∀ x, (unitBox n).Contains x →
      (∀ i, 0 ≤ (gs i).eval (fun k => (ps k).eval w₀ σ₀) x) →
      0 < H.eval (fun k => (ps k).eval w₀ σ₀) x) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, ∃ t, coverStage cs gs H hn s = .success t :=
  coverStage_eventually_succeeds_of_positive cs _ gs H hn hgap
    (scalarBounds_imply_uniformEndpointError ps w σ w₀ σ₀ hw hσ hww hσw cs hcs gs H)

end Cover
