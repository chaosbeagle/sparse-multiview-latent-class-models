import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

namespace Cover

/-- Finite exact endpoints; malformed endpoint order remains representable and rejectable. -/
structure QInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

namespace QInterval

def valid (I : QInterval) : Prop := I.lower ≤ I.upper
instance (I : QInterval) : Decidable I.valid := inferInstanceAs (Decidable (I.lower ≤ I.upper))
def contains (I : QInterval) (x : ℝ) : Prop := (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)
def width (I : QInterval) : ℚ := I.upper - I.lower
def singleton (q : ℚ) : QInterval := ⟨q, q⟩
def add (I J : QInterval) : QInterval := ⟨I.lower + J.lower, I.upper + J.upper⟩
def neg (I : QInterval) : QInterval := ⟨-I.upper, -I.lower⟩
def mul (I J : QInterval) : QInterval :=
  ⟨min (min (I.lower * J.lower) (I.lower * J.upper))
      (min (I.upper * J.lower) (I.upper * J.upper)),
   max (max (I.lower * J.lower) (I.lower * J.upper))
      (max (I.upper * J.lower) (I.upper * J.upper))⟩
def invPos (I : QInterval) : QInterval := ⟨I.upper⁻¹, I.lower⁻¹⟩
def min (I J : QInterval) : QInterval := ⟨Min.min I.lower J.lower, Min.min I.upper J.upper⟩
def max (I J : QInterval) : QInterval := ⟨Max.max I.lower J.lower, Max.max I.upper J.upper⟩
def midpoint (I : QInterval) : ℚ := (I.lower + I.upper) / 2
end QInterval

/-- Finite polynomial-expression syntax with rational constants and named scalar leaves. -/
inductive PolyExpr (n a : Nat) where
  | rat : ℚ → PolyExpr n a
  | scalar : Fin a → PolyExpr n a
  | var : Fin n → PolyExpr n a
  | add : PolyExpr n a → PolyExpr n a → PolyExpr n a
  | neg : PolyExpr n a → PolyExpr n a
  | mul : PolyExpr n a → PolyExpr n a → PolyExpr n a
  deriving DecidableEq, Repr

namespace PolyExpr
noncomputable def eval (cs : Fin a → ℝ) (x : Fin n → ℝ) : PolyExpr n a → ℝ
  | .rat q => q
  | .scalar i => cs i
  | .var i => x i
  | .add p q => eval cs x p + eval cs x q
  | .neg p => -eval cs x p
  | .mul p q => eval cs x p * eval cs x q

def interval (cs : Fin a → QInterval) (box : Fin n → QInterval) : PolyExpr n a → QInterval
  | .rat q => .singleton q
  | .scalar i => cs i
  | .var i => box i
  | .add p q => .add (interval cs box p) (interval cs box q)
  | .neg p => .neg (interval cs box p)
  | .mul p q => .mul (interval cs box p) (interval cs box q)
end PolyExpr
end Cover
