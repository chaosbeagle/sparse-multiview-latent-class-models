import Ext.GoldBounds
import Ext.TV

open scoped BigOperators Classical
noncomputable section
namespace Ext
namespace ObservationExperiment
variable {E : Type*} [Fintype E] {X : E → Type*} [∀ e, Fintype (X e)]

/-- Full alphabet count. Zero-count and zero-probability cells are retained. -/
def totalCells (_O : ObservationExperiment E X) : ℕ := ∑ e, Fintype.card (X e)

lemma totalCells_pos [Nonempty E] (O : ObservationExperiment E X) : 0 < O.totalCells := by
  obtain ⟨e⟩ := ‹Nonempty E›
  unfold totalCells
  exact lt_of_lt_of_le ((O.law e).card_pos)
    (Finset.single_le_sum (f := fun e : E => Fintype.card (X e))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ e))

def cellRadius (O : ObservationExperiment E X) (δ : ℝ) (e : E) : ℝ :=
  Real.sqrt (Real.log (2 * (O.totalCells : ℝ) / δ) / (2 * (O.n e : ℝ)))

def tvRadius (O : ObservationExperiment E X) (δ : ℝ) (e : E) : ℝ :=
  min 1 ((Fintype.card (X e) : ℝ) * O.cellRadius δ e / 2)
end ObservationExperiment

/-- A-T5 all-cell event for arbitrary cross-edge coupling and all complete alphabets. -/
theorem edge_cell_family_bound {Ω E : Type*} [Fintype Ω] [Fintype E] [Nonempty E]
    {X : E → Type*} [∀ e, Fintype (X e)]
    (O : ObservationExperiment E X) (μ : FiniteLaw Ω)
    (obs : Ω → ObservationSpace O) (hIID : O.IID μ obs)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.prob (fun ω => ∀ e x,
      |O.empirical (obs ω) e x - (O.law e).mass x| ≤ O.cellRadius δ e) := by
  have hM : 0 < O.totalCells := O.totalCells_pos
  have hM1 : (1 : ℝ) ≤ O.totalCells := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < O.totalCells := by exact_mod_cast hM
  have hδM : δ ≤ 2 * (O.totalCells : ℝ) := by linarith
  have hcard : Fintype.card ((e : E) × X e) = O.totalCells := Fintype.card_sigma
  letI : Nonempty ((e : E) × X e) := Fintype.card_pos_iff.mp (hcard.symm ▸ hM)
  have failure : μ.prob (fun ω => ∃ j : (e : E) × X e,
      O.cellRadius δ j.1 < |O.empirical (obs ω) j.1 j.2 - (O.law j.1).mass j.2|) ≤ δ := by
    calc
      μ.prob (fun ω => ∃ j : (e : E) × X e,
          O.cellRadius δ j.1 < |O.empirical (obs ω) j.1 j.2 - (O.law j.1).mass j.2|) ≤
          ∑ j : (e : E) × X e, μ.prob (fun ω =>
            O.cellRadius δ j.1 < |O.empirical (obs ω) j.1 j.2 - (O.law j.1).mass j.2|) :=
        μ.prob_exists_le _
      _ ≤ ∑ _j : (e : E) × X e, δ / (O.totalCells : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have hu := edge_cell_hoeffding_upper O μ obs hIID j.1 j.2
          (show 0 ≤ O.cellRadius δ j.1 from Real.sqrt_nonneg _)
        have hl := edge_cell_hoeffding_lower O μ obs hIID j.1 j.2
          (show 0 ≤ O.cellRadius δ j.1 from Real.sqrt_nonneg _)
        unfold ObservationExperiment.cellRadius at hu hl
        rw [cell_radius_tail (O.n_pos j.1) hδ hδM] at hu hl
        have hevent : μ.prob (fun ω => O.cellRadius δ j.1 <
              |O.empirical (obs ω) j.1 j.2 - (O.law j.1).mass j.2|) ≤
            μ.prob (fun ω => O.cellRadius δ j.1 ≤
              O.empirical (obs ω) j.1 j.2 - (O.law j.1).mass j.2) +
            μ.prob (fun ω => O.empirical (obs ω) j.1 j.2 - (O.law j.1).mass j.2 ≤
              -O.cellRadius δ j.1) := by
          apply (μ.prob_mono ?_).trans (μ.prob_union_le _ _)
          intro ω hω
          rcases lt_abs.mp hω with hb | hb
          · exact Or.inl hb.le
          · exact Or.inr (by linarith)
        unfold ObservationExperiment.cellRadius at hevent
        have heq : δ / (2 * (O.totalCells : ℝ)) + δ / (2 * (O.totalCells : ℝ)) =
            δ / (O.totalCells : ℝ) := by field_simp <;> ring
        unfold ObservationExperiment.cellRadius
        linarith
      _ = δ := by rw [← hcard]; exact sum_card_div δ
  have he : (fun ω => ∃ j : (e : E) × X e,
      O.cellRadius δ j.1 < |O.empirical (obs ω) j.1 j.2 - (O.law j.1).mass j.2|) =
      (fun ω => ¬ ∀ e x, |O.empirical (obs ω) e x - (O.law e).mass x| ≤ O.cellRadius δ e) := by
    funext ω
    simp
  rw [he, μ.prob_compl] at failure
  linarith

/-- A-T5 simultaneous empirical full-law TV coverage. -/
theorem edge_tv_family_bound {Ω E : Type*} [Fintype Ω] [Fintype E] [Nonempty E]
    {X : E → Type*} [∀ e, Fintype (X e)]
    (O : ObservationExperiment E X) (μ : FiniteLaw Ω)
    (obs : Ω → ObservationSpace O) (hIID : O.IID μ obs)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.prob (fun ω => ∀ e, (O.empiricalLaw (obs ω) e).tv (O.law e) ≤ O.tvRadius δ e) := by
  apply (edge_cell_family_bound O μ obs hIID hδ hδ1).trans (μ.prob_mono ?_)
  intro ω hω e
  exact FiniteLaw.tv_of_cells_le (O.empiricalLaw (obs ω) e) (O.law e) (O.cellRadius δ e) (hω e)

end Ext
