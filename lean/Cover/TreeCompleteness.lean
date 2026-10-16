import Cover.Mesh
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

namespace Cover

namespace PolyExpr
theorem continuous_eval (p : PolyExpr n a) (cs : Fin a → ℝ) : Continuous (fun x => p.eval cs x) := by
  induction p with
  | rat q => exact continuous_const
  | scalar i => exact continuous_const
  | var i => exact continuous_apply i
  | add p q hp hq => exact hp.add hq
  | neg p hp => exact hp.neg
  | mul p q hp hq => exact hp.mul hq
end PolyExpr

variable {X : Type*}
noncomputable def maxList (base : X → ℝ) (fs : List (X → ℝ)) (x : X) : ℝ :=
  fs.foldr (fun f v => max (f x) v) (base x)

theorem maxList_base_le (base : X → ℝ) (fs : List (X → ℝ)) (x : X) :
    base x ≤ maxList base fs x := by
  induction fs with
  | nil => exact le_refl _
  | cons f fs ih => exact ih.trans (le_max_right _ _)

theorem maxList_term_le (base : X → ℝ) (fs : List (X → ℝ)) (x : X)
    (f : X → ℝ) (hf : f ∈ fs) : f x ≤ maxList base fs x := by
  induction fs with
  | nil => contradiction
  | cons g fs ih =>
    rcases List.mem_cons.mp hf with h | h
    · subst f; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem maxList_attained (base : X → ℝ) (fs : List (X → ℝ)) (x : X) :
    maxList base fs x = base x ∨ ∃ f ∈ fs, maxList base fs x = f x := by
  induction fs with
  | nil => exact Or.inl rfl
  | cons f fs ih =>
    by_cases h : maxList base fs x ≤ f x
    · right; exact ⟨f, List.mem_cons_self, max_eq_left h⟩
    · have heq : maxList base (f::fs) x = maxList base fs x := max_eq_right (le_of_not_ge h)
      rcases ih with ih | ⟨g, hg, ih⟩
      · exact Or.inl (heq.trans ih)
      · exact Or.inr ⟨g, List.mem_cons_of_mem f hg, heq.trans ih⟩

theorem continuous_maxList [TopologicalSpace X] (base : X → ℝ) (fs : List (X → ℝ))
    (hb : Continuous base) (hf : ∀ f ∈ fs, Continuous f) : Continuous (maxList base fs) := by
  induction fs with
  | nil => exact hb
  | cons f fs ih =>
    exact (hf f List.mem_cons_self).max (ih (fun g hg => hf g (List.mem_cons_of_mem f hg)))

/-- A compact slack theorem used only in proofs, with literal concrete expression denotations. -/
theorem compact_strict_slack (cs : Fin a → ℝ) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (threshold : ℝ)
    (hgap : ∀ x, (unitBox n).Contains x → (∀ i, 0 ≤ (gs i).eval cs x) →
      threshold < H.eval cs x) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x, (unitBox n).Contains x →
      threshold + γ ≤ H.eval cs x ∨ ∃ i, (gs i).eval cs x ≤ -γ := by
  classical
  let base : (Fin n → ℝ) → ℝ := fun x => H.eval cs x - threshold
  let fs : List ((Fin n → ℝ) → ℝ) := (List.finRange j).map (fun i x => -(gs i).eval cs x)
  let f := maxList base fs
  have hc : Continuous f := continuous_maxList base fs ((H.continuous_eval cs).sub continuous_const)
    (by intro g hg; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg; exact (gs i |>.continuous_eval cs).neg)
  let S : Set (Fin n → ℝ) := Set.Icc (fun _ => 0) (fun _ => 1)
  have hmem (x : Fin n → ℝ) : x ∈ S ↔ (unitBox n).Contains x := by
    simp only [S, Set.mem_Icc, Pi.le_def, QBox.Contains, unitBox, QInterval.contains,
      Rat.cast_zero, Rat.cast_one]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  have hS : IsCompact S := isCompact_Icc
  have hSne : S.Nonempty := ⟨fun _ => 0, by constructor <;> intro i <;> norm_num⟩
  have hpos : ∀ x ∈ S, 0 < f x := by
    intro x hx
    by_cases hfeas : ∀ i, 0 ≤ (gs i).eval cs x
    · have hb : 0 < base x := sub_pos.mpr (hgap x ((hmem x).mp hx) hfeas)
      exact hb.trans_le (maxList_base_le base fs x)
    · push_neg at hfeas
      obtain ⟨i, hi⟩ := hfeas
      have hm : (fun x => -(gs i).eval cs x) ∈ fs := List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
      exact (neg_pos.mpr hi).trans_le (maxList_term_le base fs x _ hm)
  obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn hSne hc.continuousOn
  refine ⟨f x0, hpos x0 hx0, ?_⟩
  intro x hx
  have hle : f x0 ≤ f x := hmin ((hmem x).mpr hx)
  rcases maxList_attained base fs x with ha | ⟨g, hg, ha⟩
  · left
    change maxList base fs x = _ at ha
    change f x0 ≤ maxList base fs x at hle
    rw [ha] at hle
    dsimp [base] at hle
    linarith
  · right
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    refine ⟨i, ?_⟩
    change f x0 ≤ maxList base fs x at hle
    rw [ha] at hle
    linarith


/-- Uniform approximation is a semantic property of the actual endpoint execution,
    uniformly over all small subboxes and their real points. -/
def UniformEndpointError (cs : Nat → Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s0 : Nat, ∀ s ≥ s0, ∀ B : QBox n, B.Valid →
    (∀ x, B.Contains x → (unitBox n).Contains x) →
    (∀ i, (B i).width ≤ dyadic s) → ∀ x, B.Contains x →
    (∀ i, (((gs i).interval (cs s) B).upper : ℝ) - (gs i).eval values x < ε) ∧
    H.eval values x - ((H.interval (cs s) B).lower : ℝ) < ε

theorem cyclicBox_contains_root (hn : 0 < n) (h : CyclicBox hn depth B)
    (x : Fin n → ℝ) (hx : B.Contains x) : (unitBox n).Contains x := by
  induction h with
  | root => exact hx
  | child h right ih =>
    apply ih
    apply (midpoint_children_union_parent _ _ x).mpr
    cases right
    · exact Or.inl hx
    · exact Or.inr hx

theorem chooseLeaf_exists_of_checked (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) (label : CoverLeaf j)
    (h : checkLeaf cs gs H k B label = true) : ∃ label, chooseLeaf cs gs H k B = some label := by
  cases hc : chooseLeaf cs gs H k B with
  | some l => exact ⟨l, rfl⟩
  | none =>
    have hf := (chooseLeaf_none_iff cs gs H k B).mp hc label
    rw [h] at hf
    contradiction

theorem dyadic_square_eventually_small (ε : ℝ) (hε : 0 < ε) :
    ∃ s0 : Nat, ∀ s ≥ s0, (dyadic (2*s) : ℝ) < ε := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1:ℝ)/4 < 1)
  obtain ⟨s0, hs⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hε)
  refine ⟨s0, ?_⟩
  intro s hss
  have hd : (dyadic (2*s) : ℝ) = (1/4:ℝ)^s := by
    simp only [dyadic, Rat.cast_pow, Rat.cast_inv, Rat.cast_ofNat, pow_mul]
    norm_num
  rw [hd]
  exact hs s hss

/-- Generic mathematical completeness. The strict feasible gap and uniform endpoint
    approximation are hypotheses here, to be discharged by the concrete project. -/
theorem generic_strict_gap_cover_complete (cs : Nat → Fin a → QInterval)
    (values : Fin a → ℝ) (gs : Fin j → PolyExpr n a) (H : PolyExpr n a)
    (hn : 0 < n) (k : Nat)
    (hgap : ∀ x, (unitBox n).Contains x → (∀ i, 0 ≤ (gs i).eval values x) →
      (dyadic (2*k) : ℝ) < H.eval values x)
    (herr : UniformEndpointError cs values gs H) :
    ∃ s0 : Nat, ∀ s ≥ s0, ∃ t : CoverTree n j,
      (visit (cs s) gs H k hn (n*s) 0 (unitBox n)).2 = some t ∧
      checkTree (cs s) gs H k (unitBox n) t = true := by
  obtain ⟨γ, hγ, hslack⟩ := compact_strict_slack values gs H (dyadic (2*k)) hgap
  obtain ⟨s0, herror⟩ := herr (γ/2) (by positivity)
  refine ⟨s0, ?_⟩
  intro s hs
  have hall : ∀ B, CyclicBox hn (n*s) B → ∃ label, chooseLeaf (cs s) gs H k B = some label := by
    intro B hB
    let x : Fin n → ℝ := fun i => (B i).lower
    have hx : B.Contains x := fun i => QInterval.contains_lower (cyclicBox_valid hn hB i)
    have hxroot := cyclicBox_contains_root hn hB x hx
    obtain ⟨he, hH⟩ := herror s hs B (cyclicBox_valid hn hB)
      (fun x hx => cyclicBox_contains_root hn hB x hx)
      (fun i => le_of_eq (full_depth_mesh_width hn s hB i)) x hx
    rcases hslack x hxroot with hg | ⟨i, hg⟩
    · apply chooseLeaf_exists_of_checked (cs s) gs H k B .gap
      have hreal : (dyadic (2*k) : ℝ) ≤ ((H.interval (cs s) B).lower : ℝ) := by linarith
      have hrat : dyadic (2*k) ≤ (H.interval (cs s) B).lower := by exact_mod_cast hreal
      simpa [checkLeaf] using hrat
    · apply chooseLeaf_exists_of_checked (cs s) gs H k B (.exclude i)
      have hreal : (((gs i).interval (cs s) B).upper : ℝ) < 0 := by linarith [he i]
      have hrat : ((gs i).interval (cs s) B).upper < 0 := by exact_mod_cast hreal
      simpa [checkLeaf] using hrat
  have hp := allTerminalPass_of_cyclic (cs s) gs H k hn (n*s) hall (n*s) 0 (unitBox n)
    (by omega) .root
  obtain ⟨t, ht⟩ := visit_succeeds_of_terminal_pass (cs s) gs H k hn (n*s) 0 (unitBox n) hp
  exact ⟨t, ht, visit_replays (cs s) gs H k hn (n*s) 0 (unitBox n) t ht⟩

/-- The concrete diagonal stage succeeds eventually, conditional only on the two
    analytic facts that the parent project's actual admitted model must prove. -/
theorem coverStage_eventually_succeeds_of_positive (cs : Nat → Fin a → QInterval)
    (values : Fin a → ℝ) (gs : Fin j → PolyExpr n a) (H : PolyExpr n a)
    (hn : 0 < n)
    (hgap : ∀ x, (unitBox n).Contains x → (∀ i, 0 ≤ (gs i).eval values x) →
      0 < H.eval values x)
    (herr : UniformEndpointError cs values gs H) :
    ∃ s0 : Nat, ∀ s ≥ s0, ∃ t, coverStage cs gs H hn s = .success t := by
  obtain ⟨γ, hγ, hslack⟩ := compact_strict_slack values gs H 0 hgap
  obtain ⟨s1, herror⟩ := herr (γ/4) (by positivity)
  obtain ⟨s2, hsmall⟩ := dyadic_square_eventually_small (γ/2) (by positivity)
  refine ⟨max s1 s2, ?_⟩
  intro s hs
  have h1 : s1 ≤ s := (le_max_left _ _).trans hs
  have h2 : s2 ≤ s := (le_max_right _ _).trans hs
  apply coverStage_succeeds_of_full_depth_boxes
  intro B hB
  let x : Fin n → ℝ := fun i => (B i).lower
  have hx : B.Contains x := fun i => QInterval.contains_lower (cyclicBox_valid hn hB i)
  have hxroot := cyclicBox_contains_root hn hB x hx
  obtain ⟨he, hH⟩ := herror s h1 B (cyclicBox_valid hn hB)
    (fun x hx => cyclicBox_contains_root hn hB x hx)
    (fun i => le_of_eq (full_depth_mesh_width hn s hB i)) x hx
  rcases hslack x hxroot with hg | ⟨i, hg⟩
  · apply chooseLeaf_exists_of_checked (cs s) gs H s B .gap
    have hreal : (dyadic (2*s) : ℝ) ≤ ((H.interval (cs s) B).lower : ℝ) := by linarith [hsmall s h2]
    have hrat : dyadic (2*s) ≤ (H.interval (cs s) B).lower := by exact_mod_cast hreal
    simpa [checkLeaf] using hrat
  · apply chooseLeaf_exists_of_checked (cs s) gs H s B (.exclude i)
    have hreal : (((gs i).interval (cs s) B).upper : ℝ) < 0 := by linarith [he i]
    have hrat : ((gs i).interval (cs s) B).upper < 0 := by exact_mod_cast hreal
    simpa [checkLeaf] using hrat

end Cover
