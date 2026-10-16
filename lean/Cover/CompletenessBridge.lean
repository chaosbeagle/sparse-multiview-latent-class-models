import Cover.TreeCompleteness
import Cover.UniformUnitBox

namespace Cover

/-- The explicit endpoint-approximation premise of the finite-tree completeness
proof follows from the literal interval evaluator and joint coefficient refinement. -/
theorem uniformEndpointError_of_coefficient_refinement
    (cs : ℕ → Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a)
    (hcs : ∀ s i, (cs s i).contains (values i))
    (hcw : ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (cs s i).width ≤ δ) :
    UniformEndpointError cs values gs H := by
  intro ε hε
  obtain ⟨s₀,hs₀⟩ := coverInterval_uniform_convergence
    (H :: (List.finRange j).map gs) cs values hcs hcw hε
  refine ⟨s₀,?_⟩
  intro s hs B hB hsub hw x hx
  constructor
  · intro i
    exact (hs₀ s hs B hB hsub hw x hx (gs i)
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))).2
  · exact (hs₀ s hs B hB hsub hw x hx H (List.mem_cons_self)).1

/-- Generic strict-gap completeness with the actual rational evaluator, actual
cyclic traversal, fixed serialized dyadic threshold, and mandatory replay. The
strict feasible gap is an explicit generic premise, not an A06 conclusion. -/
theorem strictGap_has_interval_cover
    (cs : ℕ → Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (k : ℕ)
    (hcs : ∀ s i, (cs s i).contains (values i))
    (hcw : ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (cs s i).width ≤ δ)
    (hgap : ∀ x, (unitBox n).Contains x → (∀ i, 0 ≤ (gs i).eval values x) →
      (dyadic (2*k) : ℝ) < H.eval values x) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, ∃ t : CoverTree n j,
      (visit (cs s) gs H k hn (n*s) 0 (unitBox n)).2 = some t ∧
      checkTree (cs s) gs H k (unitBox n) t = true :=
  generic_strict_gap_cover_complete cs values gs H hn k hgap
    (uniformEndpointError_of_coefficient_refinement cs values gs H hcs hcw)

/-- Conditional eventual success of the actual Stage(s), not merely existence of
some cover. Parent A06 results must discharge the visible positivity premise. -/
theorem coverStage_eventually_succeeds_of_refining_coefficients
    (cs : ℕ → Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n)
    (hcs : ∀ s i, (cs s i).contains (values i))
    (hcw : ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (cs s i).width ≤ δ)
    (hgap : ∀ x, (unitBox n).Contains x → (∀ i, 0 ≤ (gs i).eval values x) →
      0 < H.eval values x) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, ∃ t, coverStage cs gs H hn s = .success t :=
  coverStage_eventually_succeeds_of_positive cs values gs H hn hgap
    (uniformEndpointError_of_coefficient_refinement cs values gs H hcs hcw)

/-- A positive real requested gap need not itself be of serialized form. A smaller
reciprocal-power-of-two gap is selected only in this semantic existence proof. -/
theorem strictRealGap_has_dyadic_cover
    (cs : ℕ → Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n)
    (hcs : ∀ s i, (cs s i).contains (values i))
    (hcw : ∀ η : ℚ, 0 < η → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (cs s i).width ≤ η)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x, (unitBox n).Contains x → (∀ i, 0 ≤ (gs i).eval values x) →
      δ^2 < H.eval values x) :
    ∃ k : ℕ, (dyadic k : ℝ) ≤ δ ∧ ∃ s₀ : ℕ, ∀ s ≥ s₀, ∃ t : CoverTree n j,
      (visit (cs s) gs H k hn (n*s) 0 (unitBox n)).2 = some t ∧
      checkTree (cs s) gs H k (unitBox n) t = true := by
  obtain ⟨k,hk⟩ := dyadic_square_eventually_small (δ^2) (sq_pos_of_pos hδ)
  have hks := hk k (le_refl _)
  have hpow : (dyadic (2*k) : ℝ) = (dyadic k : ℝ)^2 := by
    simp only [dyadic, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat]
    rw [← pow_mul, Nat.mul_comm]
  have hkδ : (dyadic k : ℝ) ≤ δ := by
    rw [hpow] at hks
    nlinarith
  refine ⟨k,hkδ,?_⟩
  apply strictGap_has_interval_cover cs values gs H hn k hcs hcw
  intro x hx hg
  exact hks.trans (hgap x hx hg)

end Cover
