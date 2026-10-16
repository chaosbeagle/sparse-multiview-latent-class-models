import Ext

open scoped BigOperators Classical
noncomputable section
namespace Ext.Regression

/-- Endpoint Bernoulli masses preserve the ordinary empty-power convention. -/
example : bernMass 0 false = 1 ∧ bernMass 0 true = 0 ∧
    bernMass 1 false = 0 ∧ bernMass 1 true = 1 := by norm_num [bernMass]
example : (0 : ℝ) ^ 0 = 1 := by norm_num

/-- The zero threshold is covered by the genuine weighted-product theorem. -/
example {Ω I : Type*} [Fintype Ω] [Fintype I]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (μ : FiniteLaw Ω) (sample : Ω → ∀ i, X i) (P : ∀ i, FiniteLaw (X i))
    (h : ProductBlockIID μ sample P) (f : ∀ i, X i → ℝ) (a b : I → ℝ)
    (hb : ∀ i x, f i x ∈ Set.Icc (a i) (b i)) :
    μ.prob (fun ω => 0 ≤ (∑ i, f i (sample ω i)) - ∑ i, (P i).mean (f i)) ≤ 1 := by
  simpa using weighted_product_hoeffding_upper μ sample P h f a b hb 0 le_rfl

/-- Every finite family of real normalized laws has an actual admissible product block. -/
example {I : Type*} [Fintype I] {X : I → Type*} [∀ i, Fintype (X i)]
    (P : ∀ i, FiniteLaw (X i)) : ProductBlockIID (FiniteLaw.productLaw P) id P := by
  intro z
  simp [FiniteLaw.prob, FiniteLaw.productLaw, eq_comm]

/-- Single-draw variance proxy and real reciprocals, not natural division. -/
def singleGold : GoldExperiment Unit where
  n := fun _ _ => 1
  n_pos := by intros; decide
  p := fun _ b => if b then 1 else 0
  p_nonneg := by intro _ b; cases b <;> norm_num
  p_le_one := by intro _ b; cases b <;> norm_num
  sign := fun _ => 1
  sign_valid := by intro _; exact Or.inr rfl
example : singleGold.varianceProxy () = 2 := by norm_num [GoldExperiment.varianceProxy, singleGold]
example : singleGold.direction () = 1 := by norm_num [GoldExperiment.direction, singleGold]

/-- Inclusive planning has a distinct answer from strict floor-plus-one at an integer. -/
example : Nat.ceil (3 : ℝ) = 3 ∧ Int.floor (3 : ℝ) + 1 = 4 := by norm_num

/-- The retained two-class reference space is inhabited by an exact rank-two model. -/
def binaryDesign : TripleDesign (Fin 3) where
  edges := {Finset.univ}
  edges_nonempty := by simp
  edge_card := by intro e he; simp only [Finset.mem_singleton] at he; subst e; simp
  covered := by intro g; exact ⟨Finset.univ, by simp, by simp⟩

def pointLaw (t : Bool) : FiniteLaw Bool where
  mass := fun y => if y = t then 1 else 0
  nonneg := by intro y; split_ifs <;> norm_num
  total := by simp

def binaryTheta : Theta2 binaryDesign (fun _ => Bool) where
  prevalence := fun _ => bernoulliLaw (1/2) (by norm_num) (by norm_num)
  prevalence_pos := by intro c t; cases t <;> norm_num [bernoulliLaw, bernMass]
  kernel := fun _ t => pointLaw t
  rank_two := by
    intro g u v h
    have h0 := h false
    have h1 := h true
    simpa [pointLaw] using And.intro h0 h1

example : Nonempty (Theta2 binaryDesign (fun _ => Bool)) := ⟨binaryTheta⟩

/-- The explicit witnesses include all four-state laws, rank4 and distinct semantic worlds. -/
example : Ext.Hidden.worldA ∈ Ext.Hidden.Rank4Fiber ∧
    Ext.Hidden.worldB ∈ Ext.Hidden.Rank4Fiber :=
  ⟨Ext.Hidden.worldA_rank4, Ext.Hidden.worldB_rank4⟩
example : ¬ Ext.Hidden.SemEq Ext.Hidden.worldA Ext.Hidden.worldB :=
  Ext.Hidden.worlds_not_semantically_equivalent
example : Ext.Hidden.atomImage = ({(1:ℝ)/2, 1} : Set ℝ) :=
  Ext.Hidden.atomImage_exact
example : Ext.Hidden.width Ext.Hidden.atomImage = (1:ℝ)/2 := Ext.Hidden.C_T2.2.2.2

end Ext.Regression
