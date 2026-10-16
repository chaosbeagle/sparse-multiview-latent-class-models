import Cover.IntervalDefs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Cover

/-- Literal finite syntax for the constants. Real operations occur only in denotation. -/
inductive ScalarExpr where
  | rat : ℚ → ScalarExpr
  | weight : ScalarExpr
  | sigma : ScalarExpr
  | add : ScalarExpr → ScalarExpr → ScalarExpr
  | mul : ScalarExpr → ScalarExpr → ScalarExpr
  | inv : ScalarExpr → ScalarExpr
  | sqrt : ScalarExpr → ScalarExpr
  | min : ScalarExpr → ScalarExpr → ScalarExpr
  | max : ScalarExpr → ScalarExpr → ScalarExpr
  deriving DecidableEq, Repr

namespace ScalarExpr
noncomputable def eval (w σ : ℝ) : ScalarExpr → ℝ
  | .rat q => q
  | .weight => w
  | .sigma => σ
  | .add a b => eval w σ a + eval w σ b
  | .mul a b => eval w σ a * eval w σ b
  | .inv a => (eval w σ a)⁻¹
  | .sqrt a => Real.sqrt (eval w σ a)
  | .min a b => Min.min (eval w σ a) (eval w σ b)
  | .max a b => Max.max (eval w σ a) (eval w σ b)

def pow : ScalarExpr → Nat → ScalarExpr
  | _, 0 => .rat 1
  | a, n + 1 => .mul (pow a n) a

def sum : List ScalarExpr → ScalarExpr
  | [] => .rat 0
  | a :: as => .add a (sum as)

/-- The zero default is used only on malformed empty designs; an admitted design is nonempty. -/
def maxList : List ScalarExpr → ScalarExpr
  | [] => .rat 0
  | [a] => a
  | a :: b :: as => .max a (maxList (b :: as))

@[simp] theorem eval_pow (w σ : ℝ) (a : ScalarExpr) (n : Nat) :
    (a.pow n).eval w σ = (a.eval w σ) ^ n := by
  induction n with
  | zero => simp [pow, eval]
  | succ n ih => simp [pow, eval, ih, pow_succ]

@[simp] theorem eval_sum (w σ : ℝ) (as : List ScalarExpr) :
    (sum as).eval w σ = (as.map (eval w σ)).sum := by
  induction as with
  | nil => simp [sum, eval]
  | cons a as ih => simp [sum, eval, ih]

lemma le_eval_maxList (w σ : ℝ) {as : List ScalarExpr} {a : ScalarExpr}
    (ha : a ∈ as) : a.eval w σ ≤ (maxList as).eval w σ := by
  induction as with
  | nil => simp at ha
  | cons b as ih =>
    cases as with
    | nil =>
      have hab : a = b := by simpa using ha
      subst a
      exact le_rfl
    | cons c cs =>
      rcases List.mem_cons.mp ha with h | h
      · subst a; exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)
end ScalarExpr

namespace Literal
open ScalarExpr
variable {g : Nat}

def a (n : Fin g → Nat) (i : Fin g) : ScalarExpr :=
  .mul (.add (.rat 1) (.sqrt (.rat (n i)))) (.inv (.mul .weight (ScalarExpr.sigma.pow 2)))

def b (n : Fin g → Nat) (e : List (Fin g)) : ScalarExpr :=
  .add ((ScalarExpr.inv .sigma).pow 3) (.mul (.inv .sigma) (.sum (e.map (a n))))

def edgeB (n : Fin g → Nat) (e : List (Fin g)) : ScalarExpr :=
  .sqrt (.add ((b n e).pow 2) (.sum (e.map fun i => (a n i).pow 2)))

def B (n : Fin g → Nat) (edges : List (List (Fin g))) : ScalarExpr :=
  .maxList (edges.map (edgeB n))

def kappa (n : Fin g → Nat) (edges : List (List (Fin g))) : ScalarExpr :=
  .inv (B n edges)

def m (n : Fin g → Nat) (edges : List (List (Fin g))) : Nat :=
  (edges.map fun e => (e.map n).prod).sum

def M (n : Fin g → Nat) (edges : List (List (Fin g))) : ScalarExpr :=
  .mul (.rat 12) (.sqrt (.rat (m n edges)))

def R (n : Fin g → Nat) (edges : List (List (Fin g))) : ScalarExpr :=
  .min (.rat 1) (.mul (kappa n edges) (.inv (M n edges)))

def D (components r g : Nat) : ScalarExpr :=
  .sqrt (.rat (2 * (components + r * g)))

@[simp] theorem eval_a (n : Fin g → Nat) (w σ : ℝ) (i : Fin g) :
    (a n i).eval w σ = (1 + Real.sqrt (n i)) / (w * σ ^ 2) := by
  simp [a, ScalarExpr.eval, div_eq_mul_inv]

@[simp] theorem eval_b (n : Fin g → Nat) (w σ : ℝ) (e : List (Fin g)) :
    (b n e).eval w σ = σ⁻¹ ^ 3 + σ⁻¹ * (e.map fun i => (1 + Real.sqrt (n i)) / (w * σ ^ 2)).sum := by
  simp [b, ScalarExpr.eval, List.map_map, Function.comp_def]

@[simp] theorem eval_edgeB (n : Fin g → Nat) (w σ : ℝ) (e : List (Fin g)) :
    (edgeB n e).eval w σ = Real.sqrt ((b n e).eval w σ ^ 2 +
      (e.map fun i => (a n i).eval w σ ^ 2).sum) := by
  simp [edgeB, ScalarExpr.eval, List.map_map, Function.comp_def]

lemma eval_a_pos (n : Fin g → Nat) {w σ : ℝ} (hw : 0 < w) (hσ : 0 < σ) (i : Fin g) :
    0 < (a n i).eval w σ := by
  rw [eval_a]; positivity

lemma eval_b_pos (n : Fin g → Nat) {w σ : ℝ} (hw : 0 < w) (hσ : 0 < σ)
    (e : List (Fin g)) : 0 < (b n e).eval w σ := by
  have hsum : 0 ≤ (e.map fun i => (a n i).eval w σ).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact (eval_a_pos n hw hσ i).le
  change 0 < (b n e).eval w σ
  simp only [b, ScalarExpr.eval, ScalarExpr.eval_pow, ScalarExpr.eval_sum,
    List.map_map, Function.comp_def]
  positivity

lemma eval_edgeB_pos (n : Fin g → Nat) {w σ : ℝ} (hw : 0 < w) (hσ : 0 < σ)
    (e : List (Fin g)) : 0 < (edgeB n e).eval w σ := by
  rw [eval_edgeB]
  have hb := eval_b_pos n hw hσ e
  have hsum : 0 ≤ (e.map fun i => (a n i).eval w σ ^ 2).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact sq_nonneg _
  exact Real.sqrt_pos.mpr (by nlinarith)

lemma eval_B_pos (n : Fin g → Nat) {edges : List (List (Fin g))}
    (he : edges ≠ []) {w σ : ℝ} (hw : 0 < w) (hσ : 0 < σ) :
    0 < (B n edges).eval w σ := by
  obtain ⟨e, es, rfl⟩ := List.exists_cons_of_ne_nil he
  exact (eval_edgeB_pos n hw hσ e).trans_le
    (ScalarExpr.le_eval_maxList w σ (by simp))

lemma m_pos (n : Fin g → Nat) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ []) : 0 < m n edges := by
  obtain ⟨e, es, rfl⟩ := List.exists_cons_of_ne_nil he
  unfold m
  simp only [List.map_cons, List.sum_cons]
  have hp : 0 < (e.map n).prod := by
    exact List.prod_pos (fun x hx => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact hn i)
  omega

lemma eval_M_pos (n : Fin g → Nat) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ []) (w σ : ℝ) :
    0 < (M n edges).eval w σ := by
  have hm := m_pos n hn he
  simp only [M, ScalarExpr.eval, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
  positivity

/-- Exact literal R, with no rounding or replacement by an interval endpoint. -/
theorem exactR_properties (n : Fin g → Nat) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ [])
    {w σ : ℝ} (hw : 0 < w) (hσ : 0 < σ) :
    0 < (R n edges).eval w σ ∧ (R n edges).eval w σ ≤ 1 ∧
      (M n edges).eval w σ * (R n edges).eval w σ ≤ (kappa n edges).eval w σ := by
  have hB := eval_B_pos n he hw hσ
  have hM := eval_M_pos n hn he w σ
  have hk : 0 < (kappa n edges).eval w σ := inv_pos.mpr hB
  have hR : (R n edges).eval w σ =
      min 1 ((kappa n edges).eval w σ / (M n edges).eval w σ) := by
    simp only [R, ScalarExpr.eval, Rat.cast_one, div_eq_mul_inv]
  rw [hR]
  refine ⟨lt_min (by norm_num) (div_pos hk hM), min_le_left _ _, ?_⟩
  calc
    _ ≤ (M n edges).eval w σ * ((kappa n edges).eval w σ / (M n edges).eval w σ) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
    _ = (kappa n edges).eval w σ := mul_div_cancel₀ _ (ne_of_gt hM)

end Literal
end Cover
