import Gen.Separation

open scoped BigOperators
namespace Gen.QEEncoding

/-- Effective finite rational polynomial syntax. Algebraic supplied coefficients can
    be represented by additional real variables constrained by isolating formulas. -/
inductive PolynomialExpr (n : ℕ) where
  | rational : ℚ → PolynomialExpr n
  | var : Fin n → PolynomialExpr n
  | add : PolynomialExpr n → PolynomialExpr n → PolynomialExpr n
  | mul : PolynomialExpr n → PolynomialExpr n → PolynomialExpr n
  | neg : PolynomialExpr n → PolynomialExpr n
  deriving DecidableEq

namespace PolynomialExpr

def eval {n : ℕ} : PolynomialExpr n → (Fin n → ℝ) → ℝ
  | rational q, _ => q
  | var i, x => x i
  | add p q, x => eval p x + eval q x
  | mul p q, x => eval p x * eval q x
  | neg p, x => -(eval p x)

def sum {n : ℕ} : List (PolynomialExpr n) → PolynomialExpr n
  | [] => rational 0
  | p :: ps => add p (sum ps)

def square {n : ℕ} (p : PolynomialExpr n) : PolynomialExpr n := mul p p

def sub {n : ℕ} (p q : PolynomialExpr n) : PolynomialExpr n := add p (neg q)

@[simp] theorem eval_sum {n : ℕ} (ps : List (PolynomialExpr n)) (x : Fin n → ℝ) :
    (sum ps).eval x = (ps.map (fun p => p.eval x)).sum := by
  induction ps with
  | nil => simp [sum, eval]
  | cons p ps ih => simp [sum, eval, ih]

@[simp] theorem eval_square {n : ℕ} (p : PolynomialExpr n) (x : Fin n → ℝ) :
    p.square.eval x = (p.eval x) ^ 2 := by simp [square, eval, pow_two]

@[simp] theorem eval_sub {n : ℕ} (p q : PolynomialExpr n) (x : Fin n → ℝ) :
    (p.sub q).eval x = p.eval x - q.eval x := by simp [sub, eval, sub_eq_add_neg]

/-- Syntactic evaluation is continuous at every real vector, without algebraicity
    assumptions on any quantified model coordinate. -/
theorem eval_continuous {n : ℕ} (p : PolynomialExpr n) : Continuous p.eval := by
  induction p with
  | rational q => exact continuous_const
  | var i => exact continuous_apply i
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq
  | neg p hp => exact hp.neg
end PolynomialExpr

/-- Finite first-order real polynomial formulas, with arbitrary alternation and
    finite real quantifier blocks. No real-equality decision oracle is present. -/
inductive Formula : ℕ → Type where
  | truth : Formula n
  | equal : PolynomialExpr n → PolynomialExpr n → Formula n
  | less : PolynomialExpr n → PolynomialExpr n → Formula n
  | le : PolynomialExpr n → PolynomialExpr n → Formula n
  | conjunction : Formula n → Formula n → Formula n
  | negation : Formula n → Formula n
  | existsBlock (k : ℕ) : Formula (n + k) → Formula n

namespace Formula

def Holds : {n : ℕ} → Formula n → (Fin n → ℝ) → Prop
  | _, truth, _ => True
  | _, equal p q, x => p.eval x = q.eval x
  | _, less p q, x => p.eval x < q.eval x
  | _, le p q, x => p.eval x ≤ q.eval x
  | _, conjunction p q, x => Holds p x ∧ Holds q x
  | _, negation p, x => ¬ Holds p x
  | _, existsBlock k p, x => ∃ y : Fin k → ℝ, Holds p (Fin.addCases x y)

def all {n : ℕ} : List (Formula n) → Formula n
  | [] => truth
  | p :: ps => conjunction p (all ps)

@[simp] theorem holds_all {n : ℕ} (ps : List (Formula n)) (x : Fin n → ℝ) :
    (all ps).Holds x ↔ ∀ p ∈ ps, p.Holds x := by
  induction ps with
  | nil => simp [all, Holds]
  | cons p ps ih => simp [all, Holds, ih]
end Formula

/-- Syntactically build every squared-permutation distance comparison. The complete
    list hypothesis is an exact coverage requirement, not an alignment heuristic. -/
def allPermutationFar {n : ℕ} {Q : Type*} (qs : List Q)
    (distanceSquared : Q → PolynomialExpr n) (radiusSquared : PolynomialExpr n) : Formula n :=
  Formula.all (qs.map (fun q => Formula.le radiusSquared (distanceSquared q)))

theorem allPermutationFar_sound_complete {n : ℕ} {Q : Type*}
    (qs : List Q) (hcomplete : ∀ q, q ∈ qs)
    (distanceSquared : Q → PolynomialExpr n) (radiusSquared : PolynomialExpr n)
    (x : Fin n → ℝ) :
    (allPermutationFar qs distanceSquared radiusSquared).Holds x ↔
      ∀ q, radiusSquared.eval x ≤ (distanceSquared q).eval x := by
  simp only [allPermutationFar, Formula.holds_all, List.forall_mem_map, Formula.Holds]
  constructor
  · intro h q; exact h q (hcomplete q)
  · intro h q _; exact h q

/-- Literal attained minimum semantics, retaining the universal no-smaller-value
    requirement that a feasible numerical pair alone cannot establish. -/
def AttainedMinimum {X : Type*} (Q : X → Prop) (H : X → ℝ) (h : ℝ) : Prop :=
  (∃ x, Q x ∧ H x = h) ∧ ¬ ∃ x, Q x ∧ H x < h

theorem attainedMinimum_iff {X : Type*} (Q : X → Prop) (H : X → ℝ) (h : ℝ) :
    AttainedMinimum Q H h ↔ (∃ x, Q x ∧ H x = h) ∧ ∀ x, Q x → h ≤ H x := by
  simp [AttainedMinimum, not_lt]

theorem attainedMinimum_unique {X : Type*} {Q : X → Prop} {H : X → ℝ} {h k : ℝ}
    (hh : AttainedMinimum Q H h) (hk : AttainedMinimum Q H k) : h = k := by
  obtain ⟨⟨x,hx,hxh⟩,hminh⟩ := (attainedMinimum_iff Q H h).mp hh
  obtain ⟨⟨y,hy,hyk⟩,hmink⟩ := (attainedMinimum_iff Q H k).mp hk
  exact le_antisymm (hyk ▸ hminh y hy) (hxh ▸ hmink x hx)

/-- Denominator clearing for strict direction anchors is valid only with proved
    positive truth denominators. -/
theorem strict_anchor_denominator_clearing {s a b u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    0 < s * (a / u - b / v) ↔ 0 < s * (a*v-b*u) := by
  have heq : s * (a / u - b / v) = (s * (a*v-b*u)) / (u*v) := by
    field_simp
  rw [heq]
  exact div_pos_iff_of_pos_right (mul_pos hu hv)

/-- Verified constructive dyadic stage for an already certified positive rational
    lower squared bound. This is an executable fragment, not real-algebraic QE. -/
theorem rational_dyadic_exists (h : ℚ) (hh : 0 < h) : ∃ k : ℕ, (1/4 : ℚ)^k ≤ h := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (x := h) (y := (1/4 : ℚ)) hh (by norm_num)
  exact ⟨k,hk.le⟩

def rationalDyadicExponent (h : ℚ) (hh : 0 < h) : ℕ :=
  Nat.find (rational_dyadic_exists h hh)

def rationalDyadicSeparation (h : ℚ) (hh : 0 < h) : ℚ :=
  (1/2 : ℚ) ^ rationalDyadicExponent h hh

theorem rationalDyadicExponent_spec (h : ℚ) (hh : 0 < h) :
    (1/4 : ℚ) ^ rationalDyadicExponent h hh ≤ h ∧
      ∀ k < rationalDyadicExponent h hh, h < (1/4 : ℚ)^k := by
  constructor
  · exact Nat.find_spec (rational_dyadic_exists h hh)
  · intro k hk
    exact lt_of_not_ge (Nat.find_min (rational_dyadic_exists h hh) hk)

theorem rationalDyadicSeparation_spec (h : ℚ) (hh : 0 < h) :
    0 < rationalDyadicSeparation h hh ∧ (rationalDyadicSeparation h hh)^2 ≤ h := by
  refine ⟨by unfold rationalDyadicSeparation; positivity, ?_⟩
  have heq : (rationalDyadicSeparation h hh)^2 = (1/4 : ℚ)^rationalDyadicExponent h hh := by
    unfold rationalDyadicSeparation
    rw [← pow_mul, mul_comm (rationalDyadicExponent h hh) 2, pow_mul]
    norm_num
  rw [heq]
  exact (rationalDyadicExponent_spec h hh).1

/-- Kernel-replayed executable regression; no native evaluator axiom. -/
theorem rational_example_exponent : rationalDyadicExponent (1/100) (by norm_num) = 4 := by
  unfold rationalDyadicExponent
  rw [Nat.find_eq_iff]
  constructor
  · norm_num
  · intro n hn; interval_cases n <;> norm_num

theorem rational_example_separation : rationalDyadicSeparation (1/100) (by norm_num) = 1/16 := by
  unfold rationalDyadicSeparation
  rw [rational_example_exponent]
  norm_num

#eval rationalDyadicExponent (1/100) (by norm_num)
#eval rationalDyadicSeparation (1/100) (by norm_num)

end Gen.QEEncoding
