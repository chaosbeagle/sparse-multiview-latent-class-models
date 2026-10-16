import Cover.IntervalDefs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace Cover
namespace IntPolynomial

/-- Coefficients are stored from constant to leading coefficient. -/
abbrev Coeffs := List ℤ

def trim : Coeffs → Coeffs
  | [] => []
  | a :: as => let ts := trim as
    if ts = [] ∧ a = 0 then [] else a :: ts

def canonical (p : Coeffs) : Prop := trim p = p
instance (p : Coeffs) : Decidable (canonical p) := inferInstanceAs (Decidable (trim p = p))

def horner {R : Type*} [CommRing R] (p : Coeffs) (x : R) : R :=
  match p with
  | [] => 0
  | a :: as => (a : R) + x * horner as x

noncomputable def toPolynomial (p : Coeffs) : Polynomial ℤ :=
  match p with
  | [] => 0
  | a :: as => Polynomial.C a + Polynomial.X * toPolynomial as

def derivativeAux (n : ℕ) : Coeffs → Coeffs
  | [] => []
  | a :: as => (n : ℤ) * a :: derivativeAux (n + 1) as

def derivative : Coeffs → Coeffs
  | [] => []
  | _ :: as => derivativeAux 1 as

def intervalHorner (p : Coeffs) (I : QInterval) : QInterval :=
  match p with
  | [] => .singleton 0
  | a :: as => .add (.singleton (a : ℚ)) (.mul I (intervalHorner as I))

@[simp] theorem trim_idempotent (p : Coeffs) : trim (trim p) = trim p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    simp only [trim]
    split_ifs with h
    · rfl
    · simp only [trim, ih]
      simp only [h, ↓reduceIte]

@[simp] theorem canonical_trim (p : Coeffs) : canonical (trim p) := trim_idempotent p

@[simp] theorem horner_trim {R : Type*} [CommRing R] (p : Coeffs) (x : R) :
    horner (trim p) x = horner p x := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    simp only [trim]
    split_ifs with h
    · obtain ⟨ht, rfl⟩ := h
      have hh : horner as x = 0 := by rw [← ih, ht]; rfl
      simp [horner, hh]
    · simp only [horner, ih]

@[simp] theorem eval_toPolynomial {R : Type*} [CommRing R] (p : Coeffs) (x : R) :
    Polynomial.eval₂ (Int.castRingHom R) x (toPolynomial p) = horner p x := by
  induction p with
  | nil => simp [toPolynomial, horner]
  | cons a as ih =>
    rw [toPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, ih]
    rfl

@[simp] theorem toPolynomial_trim (p : Coeffs) : toPolynomial (trim p) = toPolynomial p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    simp only [trim]
    split_ifs with h
    · obtain ⟨ht, rfl⟩ := h
      have hh : toPolynomial as = 0 := by rw [← ih, ht]; rfl
      simp [toPolynomial, hh]
    · simp [toPolynomial, ih]

 theorem derivativeAux_toPolynomial (n : ℕ) (p : Coeffs) :
    toPolynomial (derivativeAux n p) =
      Polynomial.C (n : ℤ) * toPolynomial p +
      Polynomial.X * Polynomial.derivative (toPolynomial p) := by
  induction p generalizing n with
  | nil => simp [derivativeAux, toPolynomial]
  | cons a as ih =>
    simp [derivativeAux, toPolynomial, ih, Polynomial.derivative_mul,
      Polynomial.derivative_add, Nat.cast_add, Nat.cast_one]
    ring

@[simp] theorem derivative_toPolynomial (p : Coeffs) :
    toPolynomial (derivative p) = Polynomial.derivative (toPolynomial p) := by
  cases p with
  | nil => simp [derivative, toPolynomial]
  | cons a as =>
    simp [derivative, toPolynomial, derivativeAux_toPolynomial,
      Polynomial.derivative_mul, Polynomial.derivative_add]

@[simp] theorem cast_horner (p : Coeffs) (q : ℚ) :
    ((horner p q : ℚ) : ℝ) = horner p (q : ℝ) := by
  induction p with
  | nil => simp [horner]
  | cons a as ih => simp [horner, ih]

 theorem continuous_horner (p : Coeffs) : Continuous (horner p : ℝ → ℝ) := by
  induction p with
  | nil => simpa [horner] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  | cons a as ih => exact continuous_const.add (continuous_id.mul ih)

end IntPolynomial

inductive AlgCode where
  | rat (q : ℚ)
  | root (polynomial : IntPolynomial.Coeffs) (bracket : QInterval)
  deriving DecidableEq, Repr

namespace AlgCode

def interval : AlgCode → QInterval
  | .rat q => .singleton q
  | .root _ I => I

def validRoot (p : IntPolynomial.Coeffs) (I : QInterval) : Prop :=
  IntPolynomial.canonical p ∧ 2 ≤ p.length ∧ I.lower < I.upper ∧
  IntPolynomial.horner p I.lower * IntPolynomial.horner p I.upper < 0 ∧
  ((IntPolynomial.intervalHorner (IntPolynomial.derivative p) I).upper < 0 ∨
   0 < (IntPolynomial.intervalHorner (IntPolynomial.derivative p) I).lower)

instance (p : IntPolynomial.Coeffs) (I : QInterval) : Decidable (validRoot p I) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def valid : AlgCode → Prop
  | .rat _ => True
  | .root p I => validRoot p I
instance (c : AlgCode) : Decidable c.valid := by cases c <;> unfold valid <;> infer_instance

def validate (c : AlgCode) : Bool := decide c.valid

/-- A relation, never a real-valued executable selector. -/
def denotes : AlgCode → ℝ → Prop
  | .rat q, x => x = (q : ℝ)
  | .root p I, x => IntPolynomial.horner p x = 0 ∧ (I.lower : ℝ) < x ∧ x < (I.upper : ℝ)

@[simp] theorem validate_iff (c : AlgCode) : c.validate = true ↔ c.valid := by
  simp [validate]

/-- Each branch compares rationals only. A zero midpoint returns an exact rational. -/
def refine : AlgCode → AlgCode
  | .rat q => .rat q
  | .root p I =>
    let m := I.midpoint
    if IntPolynomial.horner p m = 0 then .rat m
    else if IntPolynomial.horner p I.lower * IntPolynomial.horner p m < 0 then
      .root p ⟨I.lower, m⟩
    else .root p ⟨m, I.upper⟩

def iterate (c : AlgCode) : ℕ → AlgCode
  | 0 => c
  | n + 1 => refine (iterate c n)

/-- Resource exhaustion is represented by none, never by invalidity. -/
def refineToPrecision (h : ℚ) : ℕ → AlgCode → Option AlgCode
  | 0, c => if c.interval.width ≤ h then some c else none
  | n + 1, c => if c.interval.width ≤ h then some c else refineToPrecision h n c.refine

def positiveBracket : ℕ → AlgCode → Option AlgCode
  | 0, c => if 0 < c.interval.lower then some c else none
  | n + 1, c => if 0 < c.interval.lower then some c else positiveBracket n c.refine

end AlgCode
end Cover
