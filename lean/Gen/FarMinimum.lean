import Gen.ConditionedRates
import Gen.QEEncoding

open Set
open scoped Classical
noncomputable section
namespace Gen.FarMinimum
open Gen.Geometry Gen.Conditioned

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

def farSet (w₀ σ R : ℝ) : Set (Ambient D Y r × Ambient D Y r) :=
  (K D Y r w₀ σ ×ˢ K D Y r w₀ σ) ∩
    {p | R ≤ Gen.ConditionedRates.distance D Y r p.1 p.2}

def lossSquared (p : Ambient D Y r × Ambient D Y r) : ℝ :=
  ‖observation D Y r p.1 - observation D Y r p.2‖ ^ 2

lemma farSet_compact (w₀ σ R : ℝ) (hw : 0 ≤ w₀) : IsCompact (farSet D Y r w₀ σ R) := by
  exact ((Gen.Conditioned.isCompact_K (D := D) (Y := Y) (r := r) hw).prod (Gen.Conditioned.isCompact_K (D := D) (Y := Y) (r := r) hw)).inter_right
    (isClosed_le continuous_const Gen.Rates.continuous_orbitDist)

lemma lossSquared_continuous : Continuous (lossSquared D Y r) := by
  unfold lossSquared
  exact (((observation_continuous D Y r).comp continuous_fst).sub
    ((observation_continuous D Y r).comp continuous_snd)).norm.pow 2

/-- The exact attained h>0 and minimizing pair over the full real far set. This is
    mathematical existence; no algebraic encoding or terminating computation is claimed. -/
theorem attained_positive_minimum {w₀ σ R : ℝ}
    (hw : 0 < w₀) (hσ : 0 < σ) (hr : 0 < r) (hR : 0 < R)
    (hne : (farSet D Y r w₀ σ R).Nonempty) :
    ∃ h : ℝ, 0 < h ∧ Gen.QEEncoding.AttainedMinimum
      (fun p => p ∈ farSet D Y r w₀ σ R) (lossSquared D Y r) h := by
  obtain ⟨p,hp,hmin⟩ := (farSet_compact D Y r w₀ σ R hw.le).exists_isMinOn hne
    (lossSquared_continuous D Y r).continuousOn
  have hn : observation D Y r p.1 ≠ observation D Y r p.2 := by
    intro heq
    have hz := (Gen.ConditionedRates.observation_eq_iff_distance_zero D Y r hw hσ hr
      p.1 p.2 hp.1.1 hp.1.2).mp heq
    have hfar : R ≤ Gen.ConditionedRates.distance D Y r p.1 p.2 := hp.2
    linarith
  refine ⟨lossSquared D Y r p, ?_, ?_⟩
  · unfold lossSquared
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn))
  · apply (Gen.QEEncoding.attainedMinimum_iff _ _ _).mpr
    exact ⟨⟨p,hp,rfl⟩, fun q hq => (isMinOn_iff.mp hmin) q hq⟩

/-- The empty far-set branch literally permits Delta=1. -/
theorem empty_far_separation {w₀ σ R : ℝ}
    (he : farSet D Y r w₀ σ R = ∅) :
    ∀ x ∈ K D Y r w₀ σ, ∀ y ∈ K D Y r w₀ σ,
      R ≤ Gen.ConditionedRates.distance D Y r x y →
        1 ≤ ‖observation D Y r x - observation D Y r y‖ := by
  intro x hx y hy hfar
  have hp : (x,y) ∈ farSet D Y r w₀ σ R := ⟨⟨hx,hy⟩,hfar⟩
  rw [he] at hp
  exact False.elim hp

end Gen.FarMinimum
