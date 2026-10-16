import Ext.Blindspot
import Gen.Diagonal

open scoped BigOperators Classical
noncomputable section
namespace Ext.Hidden

/-- A bridge between the full four-coordinate C observation and the general
    finite-coordinate observation. All competing parameters remain real. -/
lemma observed_as_product (m : ModelH) (x : Group → Output) :
    (∑ z, m.weight z * ∏ g, m.kernel g (x g) z) = m.observed (x 0) (x 1) (x 2) := by
  unfold ModelH.observed
  apply Finset.sum_congr rfl
  intro z _
  simp [Fin.prod_univ_succ]
  ring

lemma diagonal_as_star (x : Group → Output) :
    Gen.Diagonal.diagonal (fun _ : Output => (1:ℝ)/4) x =
      starObservation (x 0) (x 1) (x 2) := by
  classical
  have hx : (x = fun _ => x 0) ↔ x 0 = x 1 ∧ x 1 = x 2 := by
    constructor
    · intro h
      exact ⟨(congrFun h 1).symm, (congrFun h 1).trans (congrFun h 2).symm⟩
    · rintro ⟨h01,h12⟩
      funext g
      fin_cases g <;> simp_all
  unfold Gen.Diagonal.diagonal starObservation
  rw [Finset.sum_eq_single (x 0)]
  · simp [hx]
  · intro j _ hj
    exact if_neg (fun h => hj (congrFun h 0).symm)
  · simp

/-- Full real P* fiber theorem: deterministic bijective columns and equal weights
    are consequences of the observations, never assumptions on the competitor. -/
theorem full_star_is_atom (m : ModelH)
    (hobs : ∀ x y z, m.observed x y z = starObservation x y z) :
    ∃ j : Latent ≃ Output, m = atomModel j := by
  obtain ⟨j,hw,hk⟩ := Gen.Diagonal.local_diagonal_fiber
    (I := Group) (Z := Latent) (J := Output) (by decide)
    m.weight m.weight_pos m.kernel m.kernel_nonneg m.kernel_total
    (fun _ => (1:ℝ)/4) (by intro j; norm_num)
    (fun x => by rw [observed_as_product, hobs, diagonal_as_star])
  refine ⟨j, ModelH.ext ?_ ?_⟩
  · funext z; exact hw z
  · funext g y z
    change m.kernel g y z = if y = j z then 1 else 0
    split_ifs with h <;> simpa [h] using hk g y z

/-- Exact equality with the already accepted 24-bijection atom submodel. -/
theorem fullFiber_eq_atomFiber : FullFiber = AtomFiber := by
  ext m
  constructor
  · intro hm; exact ⟨hm, full_star_is_atom m hm.1⟩
  · exact fun hm => hm.1

theorem fullFiber_eq_rank4Fiber : FullFiber = Rank4Fiber := by
  ext m
  constructor
  · intro hm
    obtain ⟨j,rfl⟩ := full_star_is_atom m hm.1
    exact ⟨hm,atom_rank4 j⟩
  · exact fun hm => hm.1

theorem fullImage_exact : fullImage = ({(1:ℝ)/2, 1} : Set ℝ) := by
  rw [fullImage, fullFiber_eq_atomFiber]
  exact atomImage_exact

theorem rank4Image_exact : rank4Image = ({(1:ℝ)/2, 1} : Set ℝ) := by
  rw [rank4Image, ← fullFiber_eq_rank4Fiber]
  exact fullImage_exact

theorem GEN_F_STAR : FullFiber = AtomFiber ∧ FullFiber = Rank4Fiber ∧
    fullImage = ({(1:ℝ)/2, 1} : Set ℝ) ∧
    rank4Image = ({(1:ℝ)/2, 1} : Set ℝ) ∧
    sInf fullImage = (1:ℝ)/2 ∧ sSup fullImage = 1 ∧ width fullImage = (1:ℝ)/2 := by
  refine ⟨fullFiber_eq_atomFiber, fullFiber_eq_rank4Fiber,
    fullImage_exact, rank4Image_exact, ?_, ?_, ?_⟩
  all_goals rw [fullImage_exact]
  · norm_num
  · norm_num
  · norm_num [width]

end Ext.Hidden
