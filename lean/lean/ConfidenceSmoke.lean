import Ext.TV
import Ext.Experiments
open scoped Classical
noncomputable section
namespace Ext
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)]
variable {A : Type*} [Fintype A]
local instance : DecidableEq D.Edge := Classical.decEq _
set_option maxHeartbeats 2000000 in
example (B : Misspecification2 D Y) (anchors : A → Anchor2 Y)
    (nO : D.Edge → ℕ) (hnO : ∀ e, 0 < nO e)
    (nG : A → Bool → ℕ) (hnG : ∀ a t, 0 < nG a t)
    (μ : JointSampleLaw (modelGoldExperiment D Y B.truth anchors nG hnG)
      (B.observationExperiment nO hnO)) : μ.law.prob (fun _ => True) = 1 := by
  exact μ.law.prob_true
end Ext
