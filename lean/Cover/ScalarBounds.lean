import Cover.ScalarSyntax
import Cover.SqrtBounds

namespace Cover.ScalarExpr

/-- Total finite scalar syntax evaluation, failing closed if a denominator or radicand
is not certified legal. All arithmetic in this definition is exact rational arithmetic. -/
def bounds (s : Nat) (w σ : QInterval) : ScalarExpr → Option QInterval
  | .rat q => some (.singleton q)
  | .weight => some w
  | .sigma => some σ
  | .add a b => do return .add (← bounds s w σ a) (← bounds s w σ b)
  | .mul a b => do return .mul (← bounds s w σ a) (← bounds s w σ b)
  | .inv a => do
    let I ← bounds s w σ a
    if 0 < I.lower then some I.invPos else none
  | .sqrt a => do
    let I ← bounds s w σ a
    if 0 ≤ I.lower then some (DyadicSqrt.bounds s I) else none
  | .min a b => do return .min (← bounds s w σ a) (← bounds s w σ b)
  | .max a b => do return .max (← bounds s w σ a) (← bounds s w σ b)

/-- No successful scalar evaluation can claim an enclosure without replaying every
operation and its exact rational legality check. -/
theorem evalScalarBounds_sound (p : ScalarExpr) {s : Nat} {w σ : QInterval}
    {w₀ σ₀ : ℝ} (hw : w.contains w₀) (hσ : σ.contains σ₀)
    {I : QInterval} (h : p.bounds s w σ = some I) : I.contains (p.eval w₀ σ₀) := by
  induction p generalizing I with
  | rat q =>
    simp only [bounds, Option.some.injEq] at h
    subst I
    exact QInterval.singleton_contains q
  | weight => cases h; exact hw
  | sigma => cases h; exact hσ
  | add a b ia ib =>
    cases ha : a.bounds s w σ with
    | none => simp [bounds, ha] at h
    | some A =>
      cases hb : b.bounds s w σ with
      | none => simp [bounds, ha, hb] at h
      | some B =>
        simp [bounds, ha, hb] at h
        subst I
        exact QInterval.add_contains (ia ha) (ib hb)
  | mul a b ia ib =>
    cases ha : a.bounds s w σ with
    | none => simp [bounds, ha] at h
    | some A =>
      cases hb : b.bounds s w σ with
      | none => simp [bounds, ha, hb] at h
      | some B =>
        simp [bounds, ha, hb] at h
        subst I
        exact QInterval.mul_contains (ia ha) (ib hb)
  | inv a ia =>
    cases ha : a.bounds s w σ with
    | none => simp [bounds, ha] at h
    | some A =>
      by_cases hp : 0 < A.lower
      · simp [bounds, ha, hp] at h
        subst I
        exact QInterval.invPos_contains hp (ia ha)
      · simp [bounds, ha, hp] at h
  | sqrt a ia =>
    cases ha : a.bounds s w σ with
    | none => simp [bounds, ha] at h
    | some A =>
      by_cases hp : 0 ≤ A.lower
      · simp [bounds, ha, hp] at h
        subst I
        exact DyadicSqrt.bounds_contains s hp (ia ha)
      · simp [bounds, ha, hp] at h
  | min a b ia ib =>
    cases ha : a.bounds s w σ with
    | none => simp [bounds, ha] at h
    | some A =>
      cases hb : b.bounds s w σ with
      | none => simp [bounds, ha, hb] at h
      | some B =>
        simp [bounds, ha, hb] at h
        subst I
        exact QInterval.min_contains (ia ha) (ib hb)
  | max a b ia ib =>
    cases ha : a.bounds s w σ with
    | none => simp [bounds, ha] at h
    | some A =>
      cases hb : b.bounds s w σ with
      | none => simp [bounds, ha, hb] at h
      | some B =>
        simp [bounds, ha, hb] at h
        subst I
        exact QInterval.max_contains (ia ha) (ib hb)

end Cover.ScalarExpr
