import Gen.Kruskal

open scoped BigOperators Classical
noncomputable section
namespace Gen.KruskalConsequences

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {Y : G → Type*} [∀ g, Fintype (Y g)] {r : ℕ}

/-- All accepted GEN-G-KRUSKAL conclusions from the actual reference k-rank condition.
    There is no LocalRigid assumption and no competitor rank restriction. -/
theorem GEN_G_KRUSKAL (θ : Gen.Parameter D Y r) (hK : ∀ e, Gen.KCond θ e) :
    (∀ e, Gen.LocalRigid θ e) ∧
    Gen.fiber D Y r θ (fun _ => True) = Gen.orbit D Y r θ ⊤ ∧
    Function.Injective θ.permute ∧
    Nat.card {η // η ∈ Gen.fiber D Y r θ (fun _ => True)} =
      (Nat.factorial r) ^ Fintype.card D.Component := by
  have hr := fun e => Gen.Kruskal.localRigid_of_KCond θ e (hK e)
  exact ⟨hr, Gen.graph_conclusions_of_localRigid_and_KCond θ hK hr⟩

/-- The semantic permutation test now follows from the genuine generic tensor theorem,
    for an arbitrary fixed predicate, without silently assuming anchor invariance. -/
theorem GEN_G_SEMANTIC (θ : Gen.Parameter D Y r) (τ : Gen.TruthPartition r)
    (A : Gen.Parameter D Y r → Prop) (hK : ∀ e, Gen.KCond θ e) :
    Gen.fiber D Y r θ A = {η | ∃ q : Gen.W D r, A (θ.permute q) ∧ η = θ.permute q} ∧
    (Gen.IdentifiesModulo D Y r θ A (Gen.truthGauge (D := D) τ) ↔
      ∀ q : Gen.W D r, A (θ.permute q) → q ∈ Gen.truthGauge (D := D) τ) ∧
    (Gen.IdentifiesModulo D Y r θ A (Gen.truthPreservingGauge (D := D) τ) ↔
      ∀ q : Gen.W D r, A (θ.permute q) → q ∈ Gen.truthPreservingGauge (D := D) τ) := by
  have hr := fun e => Gen.Kruskal.localRigid_of_KCond θ e (hK e)
  have hd := Gen.KCond.distinctColumns θ hK
  exact ⟨Gen.anchored_fiber_eq_surviving_perms_of_localRigid θ A hr hd,
    Gen.identifies_iff_surviving_perms_of_localRigid θ A _ hr hd,
    Gen.identifies_iff_surviving_perms_of_localRigid θ A _ hr hd⟩

/-- Full column rank remains a sufficient special case, not the generic theorem's premise. -/
theorem fullColumnRank_special_case (θ : Gen.Parameter D Y r) (hr : 2 ≤ r)
    (hfull : Gen.FullColumnRank θ) :
    Gen.fiber D Y r θ (fun _ => True) = Gen.orbit D Y r θ ⊤ := by
  exact Gen.Kruskal.kruskal_fiber_eq_component_orbit θ (Gen.fullColumnRank_KCond θ hr hfull)

end Gen.KruskalConsequences
