import Ext.Core
import Mathlib.Data.Fintype.Powerset

open scoped BigOperators Classical
noncomputable section
namespace Ext

/-- The number of successes in a finite Boolean sample. -/
def successCount {I : Type*} [Fintype I] (z : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => z i = true).card

lemma successCount_eq_sum {I : Type*} [Fintype I] (z : I → Bool) :
    successCount z = ∑ i, if z i then 1 else 0 := by
  rw [successCount, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma successCount_le {I : Type*} [Fintype I] (z : I → Bool) :
    successCount z ≤ Fintype.card I :=
  Finset.card_filter_le _ _

/-- Bounded counts retain all values, including zero and the full sample size. -/
def boundedSuccessCount {n : ℕ} (z : Fin n → Bool) : Fin (n + 1) :=
  ⟨successCount z, Nat.lt_succ_of_le (by simpa using successCount_le z)⟩

/-- Exact binomial mass over arbitrary real parameters, with ordinary natural powers. -/
def binomialMass (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

private def boolStringFinsetEquiv (I : Type*) [Fintype I] : (I → Bool) ≃ Finset I where
  toFun z := Finset.univ.filter fun i => z i = true
  invFun s i := decide (i ∈ s)
  left_inv z := by
    funext i
    simp
  right_inv s := by
    ext i
    simp

lemma bernoulli_string_mass {I : Type*} [Fintype I] (p : ℝ) (z : I → Bool) :
    (∏ i, bernMass p (z i)) =
      p ^ successCount z * (1 - p) ^ (Fintype.card I - successCount z) := by
  classical
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset I)) (p := fun i => z i = true)
  have hn : (Finset.univ.filter fun i => ¬z i = true).card =
      Fintype.card I - successCount z := by
    simp only [Finset.card_univ] at hc
    unfold successCount
    omega
  simp only [bernMass, Finset.prod_ite, Finset.prod_const]
  rw [hn]
  rfl

/-- Weighted Boolean count fibers have the exact binomial coefficient; this is
combinatorial and does not assume a binomial law. -/
theorem bernoulli_count_fiber_sum {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℝ) (k : ℕ) :
    (∑ z : I → Bool, if successCount z = k then ∏ i, bernMass p (z i) else 0) =
      binomialMass (Fintype.card I) p k := by
  classical
  calc
    _ = ∑ s : Finset I,
        if s.card = k then p ^ k * (1 - p) ^ (Fintype.card I - k) else 0 := by
      apply Fintype.sum_equiv (boolStringFinsetEquiv I)
      intro z
      change (if successCount z = k then ∏ i, bernMass p (z i) else 0) =
        if successCount z = k then p ^ k * (1 - p) ^ (Fintype.card I - k) else 0
      by_cases hz : successCount z = k
      · simp [hz, bernoulli_string_mass]
      · simp [hz]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [binomialMass, mul_assoc]

/-- Assemble two stratum strings into the full sigma-indexed gold block. -/
def joinGoldStrings {n : Bool → ℕ}
    (z : (Fin (n false) → Bool) × (Fin (n true) → Bool))
    (j : (t : Bool) × Fin (n t)) : Bool :=
  match j with
  | ⟨false, i⟩ => z.1 i
  | ⟨true, i⟩ => z.2 i

/-- Actual full-string IID implies the joint marginal of both stratum strings. -/
theorem gold_pair_string_law {Ω A : Type*} [Fintype Ω] [Fintype A]
    (G : GoldExperiment A) (μ : FiniteLaw Ω) (gold : Ω → GoldSpace G)
    (hIID : G.IID μ gold) (a : A)
    (z : (Fin (G.n a false) → Bool) × (Fin (G.n a true) → Bool)) :
    μ.prob (fun ω => (gold ω a false, gold ω a true) = z) =
      (∏ i, bernMass (G.p a false) (z.1 i)) *
        (∏ i, bernMass (G.p a true) (z.2 i)) := by
  have he : (fun ω => (gold ω a false, gold ω a true) = z) =
      (fun ω => (fun j : (t : Bool) × Fin (G.n a t) => gold ω a j.1 j.2) =
        joinGoldStrings z) := by
    funext ω
    apply propext
    constructor
    · intro h
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      funext ⟨t, i⟩
      cases t <;> simp_all [joinGoldStrings]
    · intro h
      apply Prod.ext
      · funext i
        exact congrFun h ⟨false, i⟩
      · funext i
        exact congrFun h ⟨true, i⟩
  rw [he, hIID a]
  simp [bernoulliLaw, Fintype.prod_sigma, joinGoldStrings, mul_comm]

/-- Exact pair-singleton count law, derived from the full IID marginal. -/
theorem gold_count_pair_singleton {Ω A : Type*} [Fintype Ω] [Fintype A]
    (G : GoldExperiment A) (μ : FiniteLaw Ω) (gold : Ω → GoldSpace G)
    (hIID : G.IID μ gold) (a : A) (k0 k1 : ℕ) :
    μ.prob (fun ω => successCount (gold ω a false) = k0 ∧
      successCount (gold ω a true) = k1) =
      binomialMass (G.n a false) (G.p a false) k0 *
        binomialMass (G.n a true) (G.p a true) k1 := by
  classical
  rw [μ.prob_map_event (fun ω => (gold ω a false, gold ω a true))
    (fun z => successCount z.1 = k0 ∧ successCount z.2 = k1)]
  simp_rw [gold_pair_string_law G μ gold hIID a]
  rw [Fintype.sum_prod_type]
  calc
    _ = (∑ z0 : Fin (G.n a false) → Bool,
        if successCount z0 = k0 then ∏ i, bernMass (G.p a false) (z0 i) else 0) *
        (∑ z1 : Fin (G.n a true) → Bool,
        if successCount z1 = k1 then ∏ i, bernMass (G.p a true) (z1 i) else 0) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z0 _
      apply Finset.sum_congr rfl
      intro z1 _
      by_cases h0 : successCount z0 = k0 <;>
        by_cases h1 : successCount z1 = k1 <;> simp [h0, h1]
    _ = _ := by
      have h0 := bernoulli_count_fiber_sum (I := Fin (G.n a false)) (G.p a false) k0
      have h1 := bernoulli_count_fiber_sum (I := Fin (G.n a true)) (G.p a true) k1
      simpa only [Fintype.card_fin] using congrArg₂ (· * ·) h0 h1

namespace GoldExperiment
variable {A : Type*} [Fintype A]

/-- The two bounded, natural-number success counts, ordered as truth 0 then truth 1. -/
def countPair (G : GoldExperiment A) (ω : GoldSpace G) (a : A) :
    Fin (G.n a false + 1) × Fin (G.n a true + 1) :=
  (boundedSuccessCount (ω a false), boundedSuccessCount (ω a true))

lemma countPair_values (G : GoldExperiment A) (ω : GoldSpace G) (a : A) :
    ((G.countPair ω a).1.val, (G.countPair ω a).2.val) =
      (∑ i, if ω a false i then 1 else 0, ∑ i, if ω a true i then 1 else 0) := by
  simp [countPair, boundedSuccessCount, successCount_eq_sum]
end GoldExperiment

/-- A-T0-G for an arbitrary count-pair event and arbitrary coupling of present gold
blocks. Only the actual full two-stratum IID marginal is assumed. -/
theorem gold_count_event_law {Ω A : Type*} [Fintype Ω] [Fintype A]
    (G : GoldExperiment A) (μ : FiniteLaw Ω) (gold : Ω → GoldSpace G)
    (hIID : G.IID μ gold) (a : A)
    (S : Set (Fin (G.n a false + 1) × Fin (G.n a true + 1))) :
    μ.prob (fun ω => G.countPair (gold ω) a ∈ S) =
      ∑ k, if k ∈ S then
        binomialMass (G.n a false) (G.p a false) k.1.val *
        binomialMass (G.n a true) (G.p a true) k.2.val else 0 := by
  classical
  rw [μ.prob_map_event (fun ω => G.countPair (gold ω) a) (· ∈ S)]
  apply Finset.sum_congr rfl
  intro k _
  rcases k with ⟨k0, k1⟩
  split_ifs
  · convert gold_count_pair_singleton G μ gold hIID a k0.val k1.val using 1
    congr 1
    funext ω
    simp [GoldExperiment.countPair, Prod.mk.injEq, boundedSuccessCount, Fin.ext_iff]
  · rfl


/-- The same exact law as a literal sum over the chosen finite count-pair event. -/
theorem gold_count_finset_law {Ω A : Type*} [Fintype Ω] [Fintype A]
    (G : GoldExperiment A) (μ : FiniteLaw Ω) (gold : Ω → GoldSpace G)
    (hIID : G.IID μ gold) (a : A)
    (S : Finset (Fin (G.n a false + 1) × Fin (G.n a true + 1))) :
    μ.prob (fun ω => G.countPair (gold ω) a ∈ S) =
      ∑ k ∈ S,
        ((G.n a false).choose k.1.val : ℝ) * (G.p a false) ^ k.1.val *
          (1 - G.p a false) ^ (G.n a false - k.1.val) *
        (((G.n a true).choose k.2.val : ℝ) * (G.p a true) ^ k.2.val *
          (1 - G.p a true) ^ (G.n a true - k.2.val)) := by
  classical
  simpa [binomialMass] using gold_count_event_law G μ gold hIID a (S : Set _)


end Ext
