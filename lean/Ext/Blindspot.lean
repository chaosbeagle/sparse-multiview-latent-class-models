import Ext.Hidden
import Mathlib.Data.Fintype.Perm

open scoped BigOperators Classical
noncomputable section
namespace Ext.Hidden

/-- All 24 bijections, with no externally supplied truth partition. -/
def atomModel (j : Latent ≃ Output) : ModelH where
  weight := fun _ => 1 / 4
  weight_pos := by intro z; norm_num
  weight_total := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]
  kernel := fun _ y z => if y = j z then 1 else 0
  kernel_nonneg := by intro g y z; split_ifs <;> norm_num
  kernel_total := by intro g z; simp

lemma atom_rank4 (j : Latent ≃ Output) : (atomModel j).Rank4 := by
  intro g
  rw [Fintype.linearIndependent_iff]
  intro c hc l
  have h := congrFun hc (j l)
  simpa [atomModel, Finset.sum_apply, Pi.smul_apply, j.injective.eq_iff,
    eq_comm] using h

/-- Exactly the four visible diagonal atoms, on all 64 observed cells. -/
def starObservation (x y z : Output) : ℝ := if x = y ∧ y = z then 1 / 4 else 0

lemma atom_observed (j : Latent ≃ Output) (x y z : Output) :
    (atomModel j).observed x y z = starObservation x y z := by
  unfold ModelH.observed
  rw [Finset.sum_eq_single (j.symm x)]
  · by_cases hxy : x = y <;> by_cases hyz : y = z <;>
      simp_all [atomModel, starObservation, eq_comm]
  · intro l hl hne
    have hx : x ≠ j l := by
      intro he
      apply hne
      exact (j.symm_apply_eq).2 he |>.symm
    simp [atomModel, hx]
  · simp

/-- Zero-based versions of (3,4,1,2) and (2,4,1,3). -/
def jAFun : Latent → Output
  | (false,false) => 2
  | (false,true) => 3
  | (true,false) => 0
  | (true,true) => 1

def jBFun : Latent → Output
  | (false,false) => 1
  | (false,true) => 3
  | (true,false) => 0
  | (true,true) => 2

def jA : Latent ≃ Output := Equiv.ofBijective jAFun (by decide)
def jB : Latent ≃ Output := Equiv.ofBijective jBFun (by decide)
lemma atom_parameter_count : Fintype.card (Latent ≃ Output) = 24 := by
  rw [Fintype.card_equiv jA]
  norm_num [Latent]

def worldA : ModelH := atomModel jA
def worldB : ModelH := atomModel jB

def anchorGap (m : ModelH) : ℝ := m.truthKernel 0 0 true - m.truthKernel 0 0 false
def Anchored (m : ModelH) : Prop := 0 < anchorGap m

def sensitivity (m : ModelH) : ℝ := (m.truthLaw 0 true).prob (fun y => y.val < 2)
def specificity (m : ModelH) : ℝ := (m.truthLaw 0 false).prob (fun y => ¬ y.val < 2)

lemma prevalence_le_one (m : ModelH) (t : Bool) : m.truthWeight t ≤ 1 := by
  have ht := m.truthWeight_total
  simp only [Fintype.sum_bool] at ht
  have h0 := m.truthWeight_pos false
  have h1 := m.truthWeight_pos true
  cases t <;> linarith

lemma truth_preserving_gauge_functionals (m : ModelH) (b : Bool → Bool) :
    sensitivity (m.reindex (semanticEquiv false b)) = sensitivity m ∧
    specificity (m.reindex (semanticEquiv false b)) = specificity m ∧
    anchorGap (m.reindex (semanticEquiv false b)) = anchorGap m ∧
    (m.reindex (semanticEquiv false b)).truthWeight true = m.truthWeight true := by
  simp only [sensitivity, specificity, anchorGap, ModelH.truthLaw, Ext.FiniteLaw.prob,
    truthKernel_semantic, truthWeight_semantic]
  simp

lemma whole_truth_swap_anchor_sign (m : ModelH) (b : Bool → Bool) :
    anchorGap (m.reindex (semanticEquiv true b)) = -anchorGap m := by
  simp only [anchorGap, truthKernel_semantic]
  simp

lemma sensitivity_nonneg (m : ModelH) : 0 ≤ sensitivity m :=
  (m.truthLaw 0 true).prob_nonneg _
lemma sensitivity_le_one (m : ModelH) : sensitivity m ≤ 1 :=
  (m.truthLaw 0 true).prob_le_one _
lemma specificity_nonneg (m : ModelH) : 0 ≤ specificity m :=
  (m.truthLaw 0 false).prob_nonneg _
lemma specificity_le_one (m : ModelH) : specificity m ≤ 1 :=
  (m.truthLaw 0 false).prob_le_one _

lemma worldA_values : anchorGap worldA = 1/2 ∧ sensitivity worldA = 1 ∧
    specificity worldA = 1 ∧ worldA.truthWeight true = 1/2 := by
  norm_num [anchorGap, sensitivity, specificity, worldA, atomModel, jA, jAFun,
    ModelH.truthLaw, ModelH.truthKernel, ModelH.truthWeight, Ext.FiniteLaw.prob,
    Fintype.sum_bool, Fin.sum_univ_succ] <;> norm_num [Fin.ext_iff]

lemma worldB_values : anchorGap worldB = 1/2 ∧ sensitivity worldB = 1/2 ∧
    specificity worldB = 1/2 ∧ worldB.truthWeight true = 1/2 := by
  norm_num [anchorGap, sensitivity, specificity, worldB, atomModel, jB, jBFun,
    ModelH.truthLaw, ModelH.truthKernel, ModelH.truthWeight, Ext.FiniteLaw.prob,
    Fintype.sum_bool, Fin.sum_univ_succ] <;> norm_num [Fin.ext_iff]

lemma worlds_not_semantically_equivalent : ¬ SemEq worldA worldB := by
  rintro ⟨a,b,h⟩
  cases a with
  | false =>
    have h' := congrArg (fun m : ModelH => m.kernel 0 2 (true,true)) h
    cases hb : b true <;>
      norm_num [worldA, worldB, atomModel, ModelH.reindex, semanticEquiv,
        semanticMap, jA, jB, jAFun, jBFun, hb, Fin.ext_iff] at h'
  | true =>
    have h' := congrArg (fun m : ModelH => m.kernel 0 0 (true,false)) h
    cases hb : b true <;>
      norm_num [worldA, worldB, atomModel, ModelH.reindex, semanticEquiv,
        semanticMap, jA, jB, jAFun, jBFun, hb, Fin.ext_iff] at h'

/-- The full real fiber fixes only observations and the single strict direction anchor. -/
def FullFiber : Set ModelH := {m | (∀ x y z, m.observed x y z = starObservation x y z) ∧ Anchored m}
def Rank4Fiber : Set ModelH := {m | m ∈ FullFiber ∧ m.Rank4}
def AtomFiber : Set ModelH := {m | m ∈ FullFiber ∧ ∃ j : Latent ≃ Output, m = atomModel j}
def fullImage : Set ℝ := sensitivity '' FullFiber
def rank4Image : Set ℝ := sensitivity '' Rank4Fiber
def atomImage : Set ℝ := sensitivity '' AtomFiber
def width (S : Set ℝ) : ℝ := sSup S - sInf S

lemma worldA_full : worldA ∈ FullFiber := by
  exact ⟨atom_observed jA, by unfold Anchored; rw [worldA_values.1]; norm_num⟩
lemma worldB_full : worldB ∈ FullFiber := by
  exact ⟨atom_observed jB, by unfold Anchored; rw [worldB_values.1]; norm_num⟩
lemma worldA_rank4 : worldA ∈ Rank4Fiber := ⟨worldA_full, atom_rank4 jA⟩
lemma worldB_rank4 : worldB ∈ Rank4Fiber := ⟨worldB_full, atom_rank4 jB⟩
lemma worldA_atom : worldA ∈ AtomFiber := ⟨worldA_full, jA, rfl⟩
lemma worldB_atom : worldB ∈ AtomFiber := ⟨worldB_full, jB, rfl⟩

lemma image_bddAbove (S : Set ModelH) : BddAbove (sensitivity '' S) := by
  refine ⟨1, ?_⟩
  rintro r ⟨m, hm, rfl⟩
  exact sensitivity_le_one m
lemma image_bddBelow (S : Set ModelH) : BddBelow (sensitivity '' S) := by
  refine ⟨0, ?_⟩
  rintro r ⟨m, hm, rfl⟩
  exact sensitivity_nonneg m

lemma image_width_lower (S : Set ModelH) (hA : worldA ∈ S) (hB : worldB ∈ S) :
    (1:ℝ)/2 ≤ width (sensitivity '' S) := by
  have ha : (1:ℝ) ∈ sensitivity '' S := ⟨worldA, hA, worldA_values.2.1⟩
  have hb : (1:ℝ)/2 ∈ sensitivity '' S := ⟨worldB, hB, worldB_values.2.1⟩
  have hu := le_csSup (image_bddAbove S) ha
  have hl := csInf_le (image_bddBelow S) hb
  unfold width
  linarith

/-- C-T1: full-space and rank4-space nonidentification, with genuine real image widths. -/
theorem C_T1 : worldA ∈ Rank4Fiber ∧ worldB ∈ Rank4Fiber ∧
    (¬ SemEq worldA worldB) ∧ sensitivity worldA - sensitivity worldB = 1/2 ∧
    (1:ℝ)/2 ≤ width fullImage ∧ (1:ℝ)/2 ≤ width rank4Image := by
  refine ⟨worldA_rank4, worldB_rank4, worlds_not_semantically_equivalent, ?_,
    image_width_lower FullFiber worldA_full worldB_full,
    image_width_lower Rank4Fiber worldA_rank4 worldB_rank4⟩
  rw [worldA_values.2.1, worldB_values.2.1]
  norm_num

/-- Integer certificates are kernel-replayed over every function, not external enumeration. -/
def anchorCount (j : Latent → Output) (t : Bool) : ℕ :=
  (if (0:Output) = j (t,false) then 1 else 0) + (if (0:Output) = j (t,true) then 1 else 0)
def readoutCount (j : Latent → Output) (t : Bool) : ℕ :=
  (if (j (t,false)).val < 2 then 1 else 0) + (if (j (t,true)).val < 2 then 1 else 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
lemma regrouping_certificate : ∀ j : Latent → Output, Function.Injective j →
    anchorCount j false < anchorCount j true →
    readoutCount j true = 1 ∨ readoutCount j true = 2 := by
  decide

lemma atom_anchorGap (j : Latent ≃ Output) : anchorGap (atomModel j) =
    ((anchorCount j true : ℝ) - (anchorCount j false : ℝ)) / 2 := by
  simp only [anchorGap, ModelH.truthKernel, ModelH.truthWeight, atomModel,
    Fintype.sum_bool, anchorCount, Nat.cast_add, apply_ite, Nat.cast_one,
    Nat.cast_zero]
  split_ifs <;> norm_num

lemma atom_sensitivity (j : Latent ≃ Output) : sensitivity (atomModel j) =
    (readoutCount j true : ℝ) / 2 := by
  generalize h0 : j (true,false) = x
  generalize h1 : j (true,true) = y
  fin_cases x <;> fin_cases y <;>
    norm_num [sensitivity, ModelH.truthLaw, ModelH.truthKernel, ModelH.truthWeight,
      atomModel, Ext.FiniteLaw.prob, Fintype.sum_bool, Fin.sum_univ_succ,
      readoutCount, h0, h1] <;> norm_num [Fin.ext_iff]

lemma anchored_atom_sensitivity (j : Latent ≃ Output) (h : Anchored (atomModel j)) :
    sensitivity (atomModel j) = 1/2 ∨ sensitivity (atomModel j) = 1 := by
  unfold Anchored at h
  rw [atom_anchorGap] at h
  have hr : (anchorCount j false : ℝ) < (anchorCount j true : ℝ) := by linarith
  have hn : anchorCount j false < anchorCount j true := by exact_mod_cast hr
  have hc := regrouping_certificate j j.injective hn
  rw [atom_sensitivity]
  rcases hc with hc | hc <;> simp [hc]

lemma atomImage_exact : atomImage = ({(1:ℝ)/2, 1} : Set ℝ) := by
  ext r
  constructor
  · rintro ⟨m, ⟨hm, j, rfl⟩, rfl⟩
    rcases anchored_atom_sensitivity j hm.2 with h | h <;> simp [h]
  · intro hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact ⟨worldB, worldB_atom, worldB_values.2.1⟩
    · exact ⟨worldA, worldA_atom, worldA_values.2.1⟩

lemma atomImage_inf : sInf atomImage = (1:ℝ)/2 := by
  rw [atomImage_exact]
  norm_num

lemma atomImage_sup : sSup atomImage = (1:ℝ) := by
  rw [atomImage_exact]
  norm_num

/-- C-T2 is sharp only for the explicitly restricted atom submodel. -/
theorem C_T2 : atomImage = ({(1:ℝ)/2, 1} : Set ℝ) ∧
    sInf atomImage = (1:ℝ)/2 ∧ sSup atomImage = (1:ℝ) ∧ width atomImage = (1:ℝ)/2 := by
  refine ⟨atomImage_exact, atomImage_inf, atomImage_sup, ?_⟩
  rw [width, atomImage_inf, atomImage_sup]
  norm_num

end Ext.Hidden
