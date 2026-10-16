import Ext.Core
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open scoped BigOperators Classical
noncomputable section
namespace Ext.Hidden

abbrev Latent := Bool × Bool
abbrev Group := Fin 3
abbrev Output := Fin 4

/-- The full real parameter space for the single covered triple. No rank or atom restriction. -/
structure ModelH where
  weight : Latent → ℝ
  weight_pos : ∀ z, 0 < weight z
  weight_total : ∑ z, weight z = 1
  kernel : Group → Output → Latent → ℝ
  kernel_nonneg : ∀ g y z, 0 ≤ kernel g y z
  kernel_total : ∀ g z, ∑ y, kernel g y z = 1

namespace ModelH

@[ext] theorem ext {m n : ModelH} (hw : m.weight = n.weight)
    (hk : m.kernel = n.kernel) : m = n := by
  cases m
  cases n
  cases hw
  cases hk
  rfl

def observed (m : ModelH) (x y z : Output) : ℝ :=
  ∑ l, m.weight l * m.kernel 0 x l * m.kernel 1 y l * m.kernel 2 z l

def truthWeight (m : ModelH) (t : Bool) : ℝ := ∑ h, m.weight (t,h)

lemma truthWeight_pos (m : ModelH) (t : Bool) : 0 < m.truthWeight t := by
  simpa [truthWeight, Fintype.sum_bool] using
    add_pos (m.weight_pos (t,true)) (m.weight_pos (t,false))

lemma truthWeight_total (m : ModelH) : ∑ t, m.truthWeight t = 1 := by
  simpa [truthWeight, Fintype.sum_prod_type] using m.weight_total

/-- The conditional truth kernel uses the actual positive marginal truth weight. -/
def truthKernel (m : ModelH) (g : Group) (y : Output) (t : Bool) : ℝ :=
  (∑ h, m.weight (t,h) * m.kernel g y (t,h)) / m.truthWeight t

lemma truthKernel_nonneg (m : ModelH) (g : Group) (y : Output) (t : Bool) :
    0 ≤ m.truthKernel g y t := by
  exact div_nonneg (Finset.sum_nonneg fun h _ =>
    mul_nonneg (m.weight_pos (t,h)).le (m.kernel_nonneg g y (t,h)))
    (m.truthWeight_pos t).le

lemma truthKernel_total (m : ModelH) (g : Group) (t : Bool) :
    ∑ y, m.truthKernel g y t = 1 := by
  simp only [truthKernel, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, m.kernel_total, mul_one]
  exact div_self (ne_of_gt (m.truthWeight_pos t))

def truthLaw (m : ModelH) (g : Group) (t : Bool) : Ext.FiniteLaw Output where
  mass := fun y => m.truthKernel g y t
  nonneg := fun y => m.truthKernel_nonneg g y t
  total := m.truthKernel_total g t

lemma observed_nonneg (m : ModelH) (x y z : Output) : 0 ≤ m.observed x y z := by
  exact Finset.sum_nonneg fun l _ => mul_nonneg
    (mul_nonneg (mul_nonneg (m.weight_pos l).le (m.kernel_nonneg 0 x l))
      (m.kernel_nonneg 1 y l)) (m.kernel_nonneg 2 z l)

lemma observed_total (m : ModelH) : ∑ x, ∑ y, ∑ z, m.observed x y z = 1 := by
  unfold observed
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun z l => m.weight l * m.kernel 0 _ l * m.kernel 1 _ l * m.kernel 2 z l)]
  simp_rw [← Finset.mul_sum, m.kernel_total, mul_one]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun y l => m.weight l * m.kernel 0 _ l * m.kernel 1 y l)]
  simp_rw [← Finset.mul_sum, m.kernel_total, mul_one]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, m.kernel_total, mul_one]
  exact m.weight_total

/-- Four-column rank is a separate subclass of the full model. -/
def Rank4 (m : ModelH) : Prop := ∀ g, LinearIndependent ℝ (fun l y => m.kernel g y l)

/-- Pullback is closed in the full normalized model for every latent permutation. -/
def reindex (m : ModelH) (e : Latent ≃ Latent) : ModelH where
  weight := fun z => m.weight (e z)
  weight_pos := fun z => m.weight_pos (e z)
  weight_total := by simpa only [Equiv.sum_comp] using m.weight_total
  kernel := fun g y z => m.kernel g y (e z)
  kernel_nonneg := fun g y z => m.kernel_nonneg g y (e z)
  kernel_total := fun g z => m.kernel_total g (e z)

lemma reindex_observed (m : ModelH) (e : Latent ≃ Latent) (x y z : Output) :
    (m.reindex e).observed x y z = m.observed x y z := by
  unfold observed reindex
  exact e.sum_comp (fun l => m.weight l * m.kernel 0 x l * m.kernel 1 y l * m.kernel 2 z l)

lemma reindex_rank4 (m : ModelH) (e : Latent ≃ Latent) (hm : m.Rank4) :
    (m.reindex e).Rank4 := by
  intro g
  exact (hm g).comp e e.injective

end ModelH

/-- Semantic gauges preserve the two truth blocks, allowing a whole-block swap. -/
def semanticMap (a : Bool) (b : Bool → Bool) (z : Latent) : Latent :=
  (xor z.1 a, xor z.2 (b z.1))

lemma semanticMap_bijective (a : Bool) (b : Bool → Bool) :
    Function.Bijective (semanticMap a b) := by
  have hx : ∀ u v : Bool, xor (xor u v) v = u := by decide
  refine ⟨?_, ?_⟩
  · intro x y h
    have ht := congrArg Prod.fst h
    have hh := congrArg Prod.snd h
    have ht' : x.1 = y.1 := by
      have := congrArg (fun t => xor t a) ht
      simpa only [semanticMap, hx] using this
    apply Prod.ext ht'
    have := congrArg (fun t => xor t (b x.1)) hh
    simpa only [semanticMap, ← ht', hx] using this
  · intro z
    refine ⟨(xor z.1 a, xor z.2 (b (xor z.1 a))), ?_⟩
    simp only [semanticMap, hx]

def semanticEquiv (a : Bool) (b : Bool → Bool) : Latent ≃ Latent :=
  Equiv.ofBijective (semanticMap a b) (semanticMap_bijective a b)

def SemEq (m n : ModelH) : Prop :=
  ∃ a b, n = m.reindex (semanticEquiv a b)

lemma semantic_gauge_closure_invariance (m : ModelH) (a : Bool) (b : Bool → Bool) :
    ∃ n : ModelH, n = m.reindex (semanticEquiv a b) ∧
      ∀ x y z, n.observed x y z = m.observed x y z := by
  exact ⟨_, rfl, fun x y z => m.reindex_observed _ x y z⟩

lemma semanticMap_id (z : Latent) : semanticMap false (fun _ => false) z = z := by
  rcases z with ⟨t,h⟩
  cases t <;> cases h <;> rfl

lemma semanticMap_comp (a c : Bool) (b d : Bool → Bool) (z : Latent) :
    semanticMap a b (semanticMap c d z) =
      semanticMap (xor c a) (fun t => xor (d t) (b (xor t c))) z := by
  have hx : ∀ x y z : Bool, xor (xor x y) z = xor x (xor y z) := by decide
  apply Prod.ext <;> simp only [semanticMap, hx]

lemma semanticMap_inverse (a : Bool) (b : Bool → Bool) (z : Latent) :
    semanticMap a b (semanticMap a (fun t => b (xor t a)) z) = z := by
  have hx : ∀ x y : Bool, xor (xor x y) y = x := by decide
  rcases z with ⟨t,h⟩
  simp only [semanticMap, hx]

lemma semantic_refl (m : ModelH) : SemEq m m := by
  refine ⟨false, fun _ => false, ?_⟩
  apply ModelH.ext <;> funext z
  · simp only [ModelH.reindex, semanticEquiv, Equiv.ofBijective_apply, semanticMap_id]
  · funext y l
    simp only [ModelH.reindex, semanticEquiv, Equiv.ofBijective_apply, semanticMap_id]

lemma semantic_symm {m n : ModelH} (h : SemEq m n) : SemEq n m := by
  rcases h with ⟨a,b,rfl⟩
  refine ⟨a, fun t => b (xor t a), ?_⟩
  apply ModelH.ext <;> funext z
  · simp only [ModelH.reindex, semanticEquiv, Equiv.ofBijective_apply, semanticMap_inverse]
  · funext y l
    simp only [ModelH.reindex, semanticEquiv, Equiv.ofBijective_apply, semanticMap_inverse]

lemma semantic_trans {m n p : ModelH} (h : SemEq m n) (k : SemEq n p) : SemEq m p := by
  rcases h with ⟨a,b,rfl⟩
  rcases k with ⟨c,d,rfl⟩
  refine ⟨xor c a, fun t => xor (d t) (b (xor t c)), ?_⟩
  apply ModelH.ext <;> funext z
  · simp only [ModelH.reindex, semanticEquiv, Equiv.ofBijective_apply, semanticMap_comp]
  · funext y l
    simp only [ModelH.reindex, semanticEquiv, Equiv.ofBijective_apply, semanticMap_comp]

lemma truthWeight_semantic (m : ModelH) (a : Bool) (b : Bool → Bool) (t : Bool) :
    (m.reindex (semanticEquiv a b)).truthWeight t = m.truthWeight (xor t a) := by
  simp only [ModelH.truthWeight, ModelH.reindex, semanticEquiv, Equiv.ofBijective_apply,
    semanticMap, Fintype.sum_bool]
  cases hb : b t <;> simp [hb, add_comm]

lemma truthKernel_semantic (m : ModelH) (a : Bool) (b : Bool → Bool)
    (g : Group) (y : Output) (t : Bool) :
    (m.reindex (semanticEquiv a b)).truthKernel g y t = m.truthKernel g y (xor t a) := by
  simp only [ModelH.truthKernel, truthWeight_semantic]
  simp only [ModelH.reindex, semanticEquiv, Equiv.ofBijective_apply, semanticMap,
    Fintype.sum_bool]
  cases hb : b t <;> simp [hb, add_comm]

end Ext.Hidden
