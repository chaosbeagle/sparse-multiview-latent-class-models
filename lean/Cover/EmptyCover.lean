import Cover.CompletenessBridge

namespace Cover
namespace CoverTree

/-- Every leaf excludes a concrete constraint; no GAP label occurs. -/
def OnlyExclude : CoverTree n j → Prop
  | .leaf (.exclude _) => True
  | .leaf .gap => False
  | .split _ l r => l.OnlyExclude ∧ r.OnlyExclude

theorem onlyExclude_of_zero_objective_checked (cs : Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (k : ℕ) (t : CoverTree n j) (B : QBox n)
    (hc : checkTree cs gs (.rat 0) k B t = true) : t.OnlyExclude := by
  induction t generalizing B with
  | leaf label =>
      cases label with
      | exclude _ => trivial
      | gap =>
          have hle : dyadic (2*k) ≤ 0 := by
            simpa only [checkTree,checkLeaf,PolyExpr.interval,QInterval.singleton,decide_eq_true_eq] using hc
          exact (not_le_of_gt (dyadic_pos _)) hle
  | split i l r ihl ihr =>
      simp only [checkTree,Bool.and_eq_true] at hc
      exact ⟨ihl _ hc.1,ihr _ hc.2⟩

/-- EXCLUDE labels are unchanged by the objective or the positive dyadic threshold. -/
theorem checkTree_transfer_onlyExclude (cs : Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H H' : PolyExpr n a) (k k' : ℕ)
    (t : CoverTree n j) (ht : t.OnlyExclude) (B : QBox n) :
    checkTree cs gs H k B t = checkTree cs gs H' k' B t := by
  induction t generalizing B with
  | leaf label =>
      cases label with
      | exclude _ => rfl
      | gap => exact False.elim ht
  | split i l r ihl ihr =>
      simp only [checkTree,ihl ht.1, ihr ht.2]

/-- An accepted finite all-EXCLUDE cover proves the real feasible set empty. -/
theorem onlyExclude_checked_implies_empty (cs : Fin a → QInterval) (values : Fin a → ℝ)
    (hcs : ∀ i, (cs i).contains (values i))
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (k : ℕ)
    (t : CoverTree n j) (ht : t.OnlyExclude)
    (hc : checkTree cs gs H k (unitBox n) t = true) :
    ∀ x, (unitBox n).Contains x → ¬(∀ i, 0 ≤ (gs i).eval values x) := by
  intro x hx hf
  have hc0 : checkTree cs gs (.rat 0) 0 (unitBox n) t = true := by
    rw [← checkTree_transfer_onlyExclude cs gs H (.rat 0) k 0 t ht]
    exact hc
  have h := verifyCoverTree_sound cs values gs (.rat 0) 0 hcs t hc0 x hx hf
  norm_num [dyadic,PolyExpr.eval] at h

end CoverTree

/-- Empty feasible sets have all-EXCLUDE certificates. The proof constructs the tree
by the concrete zero-objective visitor, then replays that same finite tree against
the original objective and threshold. It does not assert that early pruning with
the original objective must return only EXCLUDE labels. -/
theorem emptyFeasible_has_allExclude_cover
    (cs : ℕ → Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (k : ℕ)
    (hcs : ∀ s i, (cs s i).contains (values i))
    (hcw : ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (cs s i).width ≤ δ)
    (hempty : ∀ x, (unitBox n).Contains x → ¬(∀ i, 0 ≤ (gs i).eval values x)) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, ∃ t : CoverTree n j,
      (visit (cs s) gs (.rat 0) 0 hn (n*s) 0 (unitBox n)).2 = some t ∧
      t.OnlyExclude ∧ checkTree (cs s) gs H k (unitBox n) t = true := by
  have hgap : ∀ x, (unitBox n).Contains x → (∀ i, 0 ≤ (gs i).eval values x) →
      (dyadic (2*0) : ℝ) < (PolyExpr.rat 0).eval values x := by
    intro x hx hg
    exact False.elim (hempty x hx hg)
  obtain ⟨s₀,hs₀⟩ := strictGap_has_interval_cover cs values gs (.rat 0) hn 0 hcs hcw hgap
  refine ⟨s₀,?_⟩
  intro s hs
  obtain ⟨t,hvisit,hcheck⟩ := hs₀ s hs
  have ht := t.onlyExclude_of_zero_objective_checked (cs s) gs 0 (unitBox n) hcheck
  refine ⟨t,hvisit,ht,?_⟩
  rw [← t.checkTree_transfer_onlyExclude (cs s) gs (.rat 0) H 0 k ht]
  exact hcheck

end Cover
