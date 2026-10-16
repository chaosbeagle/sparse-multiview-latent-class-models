import Cover.PolyConvergence

namespace Cover.PolyExpr

theorem dyadic_mesh_eventually_le {δ : ℚ} (hδ : 0 < δ) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, 1 / (2 : ℚ)^s ≤ δ := by
  obtain ⟨s₀,hs₀⟩ := exists_nat_one_div_lt hδ
  refine ⟨s₀,?_⟩
  intro s hs
  have growth : ∀ k : ℕ, (k : ℚ) + 1 ≤ (2 : ℚ)^k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      nlinarith
  have hm : (s₀ : ℚ) ≤ s := by exact_mod_cast hs
  have hden : (0 : ℚ) < (s₀ : ℚ)+1 := by positivity
  exact (one_div_le_one_div_of_le hden (by linarith [growth s])).trans hs₀.le

/-- Eventual uniformity at the actual diagonal precision/mesh schedule. The stage
threshold precedes all boxes, all real points and all expressions of the family. -/
theorem interval_uniform_stages (ps : List (PolyExpr n a)) {M : ℚ} (hM : 0 ≤ M)
    (ics : ℕ → Fin a → QInterval) (cs : Fin a → ℝ)
    (hcs : ∀ s i, (ics s i).contains (cs i))
    (hcm : ∀ s i, (ics s i).mag ≤ M)
    (hcw : ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (ics s i).width ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ (box : Fin n → QInterval) (x : Fin n → ℝ),
      (∀ i, (box i).contains (x i)) → (∀ i, (box i).mag ≤ M) →
      (∀ i, (box i).width ≤ 1 / (2 : ℚ)^s) →
      ∀ p ∈ ps, eval cs x p - (interval (ics s) box p).lower < ε ∧
        ((interval (ics s) box p).upper : ℝ) - eval cs x p < ε := by
  obtain ⟨δ,hδ,hconv⟩ := uniform_joint_convergence ps hM hε
  obtain ⟨sc,hsc⟩ := hcw δ hδ
  obtain ⟨sx,hsx⟩ := dyadic_mesh_eventually_le hδ
  refine ⟨max sc sx,?_⟩
  intro s hs box x hx hxm hxw p hp
  exact hconv (ics s) box cs x (hcs s) hx (hcm s) hxm
    (hsc s ((le_max_left _ _).trans hs))
    (fun i => (hxw i).trans (hsx s ((le_max_right _ _).trans hs))) p hp

end Cover.PolyExpr
