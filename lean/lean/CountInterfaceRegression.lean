import Ext.CountLaw
import Ext.Experiments
open scoped BigOperators Classical
noncomputable section
namespace Ext
-- The theorem specializes without adding observation assumptions to gold-only laws.
example {A : Type*} [Fintype A] (G : GoldExperiment A) (μ : GoldSampleLaw G)
    (a : A) (S : Set (Fin (G.n a false + 1) × Fin (G.n a true + 1))) :
    μ.law.prob (fun ω => G.countPair ω a ∈ S) =
      ∑ k, if k ∈ S then binomialMass (G.n a false) (G.p a false) k.1.val *
        binomialMass (G.n a true) (G.p a true) k.2.val else 0 :=
  gold_count_event_law G μ.law id μ.iid a S

-- The joint interface still imposes no cross-block or gold-observation independence.
example {A E : Type*} [Fintype A] [Fintype E] {X : E → Type*}
    [∀ e, Fintype (X e)] (G : GoldExperiment A) (O : ObservationExperiment E X)
    (μ : JointSampleLaw G O) (a : A)
    (S : Set (Fin (G.n a false + 1) × Fin (G.n a true + 1))) :
    μ.law.prob (fun ω => G.countPair ω.1 a ∈ S) =
      ∑ k, if k ∈ S then binomialMass (G.n a false) (G.p a false) k.1.val *
        binomialMass (G.n a true) (G.p a true) k.2.val else 0 :=
  gold_count_event_law G μ.law Prod.fst μ.gold_iid a S
end Ext
