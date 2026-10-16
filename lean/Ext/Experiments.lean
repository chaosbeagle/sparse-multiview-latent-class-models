import Ext.Core

open scoped BigOperators Classical
noncomputable section
namespace Ext

/-- The exact gold-only finite sample space, with arbitrary coupling between anchors. -/
structure GoldSampleLaw {A : Type*} [Fintype A] (G : GoldExperiment A) where
  law : FiniteLaw (GoldSpace G)
  iid : G.IID law id

/-- The exact observation-only space. No gold parameters or premises are present. -/
structure ObservationSampleLaw {E : Type*} [Fintype E] {X : E → Type*}
    [∀ e, Fintype (X e)] (O : ObservationExperiment E X) where
  law : FiniteLaw (ObservationSpace O)
  iid : O.IID law id

/-- The exact joint space permits arbitrary dependence between gold and observation blocks. -/
structure JointSampleLaw {A E : Type*} [Fintype A] [Fintype E] {X : E → Type*}
    [∀ e, Fintype (X e)] (G : GoldExperiment A) (O : ObservationExperiment E X) where
  law : FiniteLaw (GoldSpace G × ObservationSpace O)
  gold_iid : G.IID law Prod.fst
  observation_iid : O.IID law Prod.snd

/-- A-T0-O, for all events of the full observation string and all finite couplings. -/
theorem observation_string_event_law {Ω E : Type*} [Fintype Ω] [Fintype E]
    {X : E → Type*} [∀ e, Fintype (X e)]
    (O : ObservationExperiment E X) (μ : FiniteLaw Ω)
    (obs : Ω → ObservationSpace O) (hIID : O.IID μ obs)
    (e : E) (U : (Fin (O.n e) → X e) → Prop) :
    μ.prob (fun ω => U (obs ω e)) =
      ∑ x, if U x then ∏ i, (O.law e).mass (x i) else 0 := by
  rw [μ.prob_map_event (fun ω => obs ω e) U]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · exact hIID e x
  · rfl

/-- Gold-only instantiation of the generic finite-space results needs no edge design. -/
def GoldSampleLaw.coordinates {A : Type*} [Fintype A] {G : GoldExperiment A}
    (_μ : GoldSampleLaw G) : GoldSpace G → GoldSpace G := id

/-- Observation-only instantiation has exactly the full categorical sample-string coordinates. -/
def ObservationSampleLaw.coordinates {E : Type*} [Fintype E] {X : E → Type*}
    [∀ e, Fintype (X e)] {O : ObservationExperiment E X}
    (_μ : ObservationSampleLaw O) : ObservationSpace O → ObservationSpace O := id

end Ext
