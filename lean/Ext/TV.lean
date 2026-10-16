import Ext.Model2
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open scoped BigOperators Classical
noncomputable section
namespace Ext
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
/-- Full-cell total variation, with real coordinates. -/
def tv (P Q : FiniteLaw Ω) : ℝ := (∑ x, |P.mass x - Q.mass x|) / 2

theorem tv_nonneg (P Q : FiniteLaw Ω) : 0 ≤ P.tv Q := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ => abs_nonneg _)) (by norm_num)
@[simp] theorem tv_self (P : FiniteLaw Ω) : P.tv P = 0 := by simp [tv]
theorem tv_symm (P Q : FiniteLaw Ω) : P.tv Q = Q.tv P := by
  simp only [tv, abs_sub_comm]
theorem tv_triangle (P Q R : FiniteLaw Ω) : P.tv R ≤ P.tv Q + Q.tv R := by
  unfold tv
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum (fun x _ => abs_sub_le (P.mass x) (Q.mass x) (R.mass x))
theorem tv_le_one (P Q : FiniteLaw Ω) : P.tv Q ≤ 1 := by
  have h : (∑ x, |P.mass x - Q.mass x|) ≤ 2 := by
    calc
      _ ≤ ∑ x, (P.mass x + Q.mass x) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [abs_le]
        constructor <;> linarith [P.nonneg x, Q.nonneg x]
      _ = 2 := by rw [Finset.sum_add_distrib, P.total, Q.total]; norm_num
  unfold tv
  linarith

variable {J : Type*} [Fintype J]
theorem tv_mix_le (w : FiniteLaw J) (P Q : J → FiniteLaw Ω) :
    (mixLaw w P).tv (mixLaw w Q) ≤ ∑ j, w.mass j * (P j).tv (Q j) := by
  have pointwise (x : Ω) :
      |(∑ j, w.mass j * (P j).mass x) - ∑ j, w.mass j * (Q j).mass x| ≤
        ∑ j, w.mass j * |(P j).mass x - (Q j).mass x| := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      _ ≤ ∑ j, |w.mass j * ((P j).mass x - (Q j).mass x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [abs_mul, abs_of_nonneg (w.nonneg _)]
  calc
    _ ≤ (∑ x, ∑ j, w.mass j * |(P j).mass x - (Q j).mass x|) / 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => pointwise x)) (by norm_num)
    _ = _ := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum, mul_div_assoc]
      rfl

/-- A single full-cell coordinate bound implies the usual finite-alphabet TV bound. -/
theorem tv_of_cells_le (P Q : FiniteLaw Ω) (r : ℝ)
    (h : ∀ x, |P.mass x - Q.mass x| ≤ r) :
    P.tv Q ≤ min 1 ((Fintype.card Ω : ℝ) * r / 2) := by
  apply le_min (tv_le_one P Q)
  unfold tv
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ _ : Ω, r := Finset.sum_le_sum (fun x _ => h x)
    _ = _ := by simp

/-- Pure TV-ball diameter, including the universal probability-law clamp. -/
theorem tv_ball_diameter (P Q center : FiniteLaw Ω) (r : ℝ)
    (hP : P.tv center ≤ min 1 r) (hQ : Q.tv center ≤ min 1 r) :
    P.tv Q ≤ min 1 (2 * r) := by
  apply le_min (tv_le_one P Q)
  have h := tv_triangle P center Q
  rw [tv_symm center Q] at h
  have hP' := hP.trans (min_le_right 1 r)
  have hQ' := hQ.trans (min_le_right 1 r)
  linarith
end FiniteLaw

namespace ObservationExperiment
variable {E : Type*} [Fintype E] {X : E → Type*} [∀ e, Fintype (X e)]
/-- The empirical law contains every alphabet cell, including zero-count cells. -/
def empiricalLaw (O : ObservationExperiment E X) (ω : ObservationSpace O) (e : E) :
    FiniteLaw (X e) where
  mass := O.empirical ω e
  nonneg x := by
    unfold empirical
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  total := by
    classical
    simp only [empirical, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt (O.n_pos e)))

@[simp] theorem empiricalLaw_mass (O : ObservationExperiment E X) (ω : ObservationSpace O)
    (e : E) (x : X e) : (O.empiricalLaw ω e).mass x = O.empirical ω e x := rfl
end ObservationExperiment

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)]
/-- Exact B-D1: true normalized conditional laws, stable target marginals, component
    prevalence, externally bounded discrepancies and a deterministic computable budget. -/
structure Misspecification2 where
  truth : Theta2 D Y
  conditional : ∀ e : D.Edge, Bool → FiniteLaw (D.Outcome Y e)
  stable_marginals : ∀ (e : D.Edge) (t : Bool) (g : D.GroupAt e) (y : Y g.val),
    (conditional e t).prob (fun x => x g = y) = (truth.kernel g.val t).mass y
  epsilon : D.Edge → Bool → ℝ
  epsilon_nonneg : ∀ e t, 0 ≤ epsilon e t
  epsilon_le_one : ∀ e t, epsilon e t ≤ 1
  conditional_tv : ∀ e t, (conditional e t).tv (truth.reference e t) ≤ epsilon e t
  budget : D.Edge → ℝ
  budget_nonneg : ∀ e, 0 ≤ budget e
  budget_le_one : ∀ e, budget e ≤ 1
  budget_valid : ∀ e, (∑ t, (truth.prevalence (D.component e)).mass t * epsilon e t) ≤ budget e

namespace Misspecification2
variable {D Y}
def actual (B : Misspecification2 D Y) (e : D.Edge) : FiniteLaw (D.Outcome Y e) :=
  FiniteLaw.mixLaw (B.truth.prevalence (D.component e)) (B.conditional e)
def trueBudget (B : Misspecification2 D Y) (e : D.Edge) : ℝ :=
  ∑ t, (B.truth.prevalence (D.component e)).mass t * B.epsilon e t

/-- B-T1, derived from actual conditional laws and their true product references. -/
theorem mixture_tv_reference_bound (B : Misspecification2 D Y) (e : D.Edge) :
    (B.actual e).tv (B.truth.observation e) ≤ B.trueBudget e ∧
      B.trueBudget e ≤ B.budget e := by
  constructor
  · apply (FiniteLaw.tv_mix_le _ _ _).trans
    exact Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left
      (B.conditional_tv e t) ((B.truth.prevalence (D.component e)).nonneg t))
  · exact B.budget_valid e

theorem trueBudget_nonneg (B : Misspecification2 D Y) (e : D.Edge) :
    0 ≤ B.trueBudget e :=
  Finset.sum_nonneg (fun t _ => mul_nonneg
    ((B.truth.prevalence (D.component e)).nonneg t) (B.epsilon_nonneg e t))

theorem trueBudget_le_max (B : Misspecification2 D Y) (e : D.Edge) :
    B.trueBudget e ≤ max (B.epsilon e false) (B.epsilon e true) := by
  calc
    _ ≤ ∑ t, (B.truth.prevalence (D.component e)).mass t *
        max (B.epsilon e false) (B.epsilon e true) := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_left _ ((B.truth.prevalence (D.component e)).nonneg t)
      cases t
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = _ := by rw [← Finset.sum_mul, FiniteLaw.total, one_mul]

def observationExperiment (B : Misspecification2 D Y) (n : D.Edge → ℕ)
    (hn : ∀ e, 0 < n e) : ObservationExperiment D.Edge (D.Outcome Y) :=
  ⟨n, hn, B.actual⟩
end Misspecification2

/-- Fixed semantic gold records use exactly the target kernel event probabilities. -/
def modelGoldExperiment {A : Type*} [Fintype A] (θ : Theta2 D Y) (anchors : A → Anchor2 Y)
    (n : A → Bool → ℕ) (hn : ∀ a t, 0 < n a t) : GoldExperiment A where
  n := n
  n_pos := hn
  p a t := (anchors a).probability θ t
  p_nonneg a t := FiniteLaw.event_nonneg (θ.kernel (anchors a).group t) (anchors a).event
  p_le_one a t := FiniteLaw.event_le_one (θ.kernel (anchors a).group t) (anchors a).event
  sign a := (anchors a).sign
  sign_valid a := (anchors a).sign_valid

/-- All sample sizes are unrestricted positive naturals; alphabets and parameter
    spaces are not replaced by a finite parameter search. -/
structure ConfidenceData2 {A : Type*} [Fintype A] (B : Misspecification2 D Y)
    (anchors : A → Anchor2 Y) where
  obsN : D.Edge → ℕ
  obsN_pos : ∀ e, 0 < obsN e
  goldN : A → Bool → ℕ
  goldN_pos : ∀ a t, 0 < goldN a t
  observations : ObservationSpace (B.observationExperiment obsN obsN_pos)
  gold : GoldSpace (modelGoldExperiment D Y B.truth anchors goldN goldN_pos)

namespace ConfidenceData2
variable {D Y} {A : Type*} [Fintype A] {B : Misspecification2 D Y} {anchors : A → Anchor2 Y}
variable (data : ConfidenceData2 D Y B anchors)
def empirical (e : D.Edge) : FiniteLaw (D.Outcome Y e) :=
  (B.observationExperiment data.obsN data.obsN_pos).empiricalLaw data.observations e
def estimate (a : A) : ℝ :=
  (modelGoldExperiment D Y B.truth anchors data.goldN data.goldN_pos).estimate data.gold a
def totalCells (_data : ConfidenceData2 D Y B anchors) : ℕ := ∑ e : D.Edge, Fintype.card (D.Outcome Y e)
theorem totalCells_pos : 0 < data.totalCells := by
  unfold totalCells
  obtain ⟨e⟩ := D.edge_nonempty
  exact lt_of_lt_of_le ((B.actual e).card_pos) (Finset.single_le_sum (f := fun e : D.Edge => Fintype.card (D.Outcome Y e)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e))
def cellRadius (δO : ℝ) (e : D.Edge) : ℝ :=
  Real.sqrt (Real.log (2 * (data.totalCells : ℝ) / δO) / (2 * (data.obsN e : ℝ)))
def observationRadius (δO : ℝ) (e : D.Edge) : ℝ :=
  min 1 ((Fintype.card (D.Outcome Y e) : ℝ) * data.cellRadius δO e / 2)
def goldRadius (δG : ℝ) (a : A) : ℝ :=
  Real.sqrt ((((data.goldN a true : ℝ)⁻¹ + (data.goldN a false : ℝ)⁻¹) / 2) *
    Real.log (2 * (Fintype.card A : ℝ) / δG))

/-- B-D2, the full real set, with both clamps and all gold interval constraints. -/
def confidenceSet (δO δG : ℝ) : Set (Theta2 D Y) :=
  {θ | (∀ e, (θ.observation e).tv (data.empirical e) ≤
      min 1 (B.budget e + data.observationRadius δO e)) ∧
    (∀ a, |(anchors a).direction θ - data.estimate a| ≤ data.goldRadius δG a)}

def observationGood (δO : ℝ) : Prop :=
  ∀ e, (data.empirical e).tv (B.actual e) ≤ data.observationRadius δO e
def goldGood (δG : ℝ) : Prop :=
  ∀ a, |data.estimate a - (anchors a).direction B.truth| ≤ data.goldRadius δG a

/-- The deterministic implication to which A-T4 and A-T5 are applied in B-T2.
    This is explicitly not a replacement for their probability theorems. -/
theorem truth_mem_of_good (δO δG : ℝ) (ho : data.observationGood δO)
    (hg : data.goldGood δG) : B.truth ∈ data.confidenceSet δO δG := by
  constructor
  · intro e
    apply le_min (FiniteLaw.tv_le_one _ _)
    have htri := FiniteLaw.tv_triangle (B.truth.observation e) (B.actual e) (data.empirical e)
    have hb := (B.mixture_tv_reference_bound e).1.trans (B.mixture_tv_reference_bound e).2
    rw [FiniteLaw.tv_symm (B.actual e) (B.truth.observation e)] at hb
    have he := ho e
    rw [FiniteLaw.tv_symm (data.empirical e) (B.actual e)] at he
    linarith
  · intro a
    rw [abs_sub_comm]
    exact hg a

theorem nonempty_of_good (δO δG : ℝ) (ho : data.observationGood δO)
    (hg : data.goldGood δG) : (data.confidenceSet δO δG).Nonempty :=
  ⟨B.truth, data.truth_mem_of_good δO δG ho hg⟩

/-- B-T3 is only an observation-law diameter; there is no inverse claim. -/
theorem observation_diameter (δO δG : ℝ) {θ θ' : Theta2 D Y}
    (hθ : θ ∈ data.confidenceSet δO δG) (hθ' : θ' ∈ data.confidenceSet δO δG)
    (e : D.Edge) : (θ.observation e).tv (θ'.observation e) ≤
      min 1 (2 * (B.budget e + data.observationRadius δO e)) :=
  FiniteLaw.tv_ball_diameter _ _ _ _ (hθ.1 e) (hθ'.1 e)
end ConfidenceData2

/-- A probability-valued functional is explicitly bounded on the entire real domain. -/
structure ProbabilityFunctional (Θ : Type*) where
  value : Θ → ℝ
  nonneg : ∀ θ, 0 ≤ value θ
  le_one : ∀ θ, value θ ≤ 1
namespace ProbabilityFunctional
variable {Θ : Type*}
def lower (f : ProbabilityFunctional Θ) (S : Set Θ) : ℝ := sInf (f.value '' S)
def upper (f : ProbabilityFunctional Θ) (S : Set Θ) : ℝ := sSup (f.value '' S)

theorem value_mem_interval (f : ProbabilityFunctional Θ) (S : Set Θ) {θ : Θ} (h : θ ∈ S) :
    f.lower S ≤ f.value θ ∧ f.value θ ≤ f.upper S := by
  have hlo : BddBelow (f.value '' S) := ⟨0, by rintro y ⟨η, hη, rfl⟩; exact f.nonneg η⟩
  have hhi : BddAbove (f.value '' S) := ⟨1, by rintro y ⟨η, hη, rfl⟩; exact f.le_one η⟩
  exact ⟨csInf_le hlo ⟨θ, h, rfl⟩, le_csSup hhi ⟨θ, h, rfl⟩⟩

/-- Simultaneous functional containment uses the same parameter membership event.
    In fact no cardinality restriction on the predeclared family is needed here. -/
theorem simultaneous_intervals {I : Type*} (f : I → ProbabilityFunctional Θ) (S : Set Θ)
    {θ : Θ} (h : θ ∈ S) : ∀ i, (f i).lower S ≤ (f i).value θ ∧
      (f i).value θ ≤ (f i).upper S := fun i => (f i).value_mem_interval S h

theorem certified_outer_interval (f : ProbabilityFunctional Θ) (S : Set Θ) (L U : ℝ)
    (hcert : ∀ η ∈ S, L ≤ f.value η ∧ f.value η ≤ U) {θ : Θ} (h : θ ∈ S) :
    L ≤ f.value θ ∧ f.value θ ≤ U := hcert θ h

theorem unit_outer_interval (f : ProbabilityFunctional Θ) (S : Set Θ) :
    ∀ θ ∈ S, (0 : ℝ) ≤ f.value θ ∧ f.value θ ≤ 1 := fun θ _ => ⟨f.nonneg θ, f.le_one θ⟩
end ProbabilityFunctional
end Ext
