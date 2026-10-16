import Cover.ScalarBounds
import Cover.Horner
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace Cover
namespace QInterval

/-- Both exact rational endpoints converge to the denoted real value. -/
def EndpointsTendTo (I : ℕ → QInterval) (x : ℝ) : Prop :=
  Tendsto (fun s => ((I s).lower : ℝ)) atTop (𝓝 x) ∧
  Tendsto (fun s => ((I s).upper : ℝ)) atTop (𝓝 x)

theorem endpoints_of_width_tendsto {I : ℕ → QInterval} {x : ℝ}
    (hx : ∀ s, (I s).contains x)
    (hw : Tendsto (fun s => ((I s).width : ℝ)) atTop (𝓝 0)) : EndpointsTendTo I x := by
  have hlow : Tendsto (fun s => x - ((I s).width : ℝ)) atTop (𝓝 x) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hw
  have hupp : Tendsto (fun s => x + ((I s).width : ℝ)) atTop (𝓝 x) := by
    simpa only [add_zero] using tendsto_const_nhds.add hw
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    · intro s; have h := (endpoint_errors_le_width (hx s)).1; linarith
    · intro s; exact (hx s).1
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupp
    · intro s; exact (hx s).2
    · intro s; have h := (endpoint_errors_le_width (hx s)).2; linarith

theorem EndpointsTendTo.width {I : ℕ → QInterval} {x : ℝ} (h : EndpointsTendTo I x) :
    Tendsto (fun s => ((I s).width : ℝ)) atTop (𝓝 0) := by
  simpa only [QInterval.width, Rat.cast_sub, sub_self] using h.2.sub h.1

theorem EndpointsTendTo.add {I J : ℕ → QInterval} {x y : ℝ}
    (hI : EndpointsTendTo I x) (hJ : EndpointsTendTo J y) :
    EndpointsTendTo (fun s => (I s).add (J s)) (x+y) := by
  constructor
  · simpa only [QInterval.add, Rat.cast_add] using hI.1.add hJ.1
  · simpa only [QInterval.add, Rat.cast_add] using hI.2.add hJ.2

theorem EndpointsTendTo.mul {I J : ℕ → QInterval} {x y : ℝ}
    (hI : EndpointsTendTo I x) (hJ : EndpointsTendTo J y) :
    EndpointsTendTo (fun s => (I s).mul (J s)) (x*y) := by
  constructor
  · simpa only [QInterval.mul, Rat.cast_min, Rat.cast_mul, min_self] using
      ((hI.1.mul hJ.1).min (hI.1.mul hJ.2)).min ((hI.2.mul hJ.1).min (hI.2.mul hJ.2))
  · simpa only [QInterval.mul, Rat.cast_max, Rat.cast_mul, max_self] using
      ((hI.1.mul hJ.1).max (hI.1.mul hJ.2)).max ((hI.2.mul hJ.1).max (hI.2.mul hJ.2))

theorem EndpointsTendTo.min {I J : ℕ → QInterval} {x y : ℝ}
    (hI : EndpointsTendTo I x) (hJ : EndpointsTendTo J y) :
    EndpointsTendTo (fun s => (I s).min (J s)) (Min.min x y) := by
  constructor
  · simpa only [QInterval.min, Rat.cast_min] using hI.1.min hJ.1
  · simpa only [QInterval.min, Rat.cast_min] using hI.2.min hJ.2

theorem EndpointsTendTo.max {I J : ℕ → QInterval} {x y : ℝ}
    (hI : EndpointsTendTo I x) (hJ : EndpointsTendTo J y) :
    EndpointsTendTo (fun s => (I s).max (J s)) (Max.max x y) := by
  constructor
  · simpa only [QInterval.max, Rat.cast_max] using hI.1.max hJ.1
  · simpa only [QInterval.max, Rat.cast_max] using hI.2.max hJ.2

theorem EndpointsTendTo.invPos {I : ℕ → QInterval} {x : ℝ}
    (hI : EndpointsTendTo I x) (hx : x ≠ 0) :
    EndpointsTendTo (fun s => (I s).invPos) x⁻¹ := by
  constructor
  · simpa only [QInterval.invPos, Rat.cast_inv] using hI.2.inv₀ hx
  · simpa only [QInterval.invPos, Rat.cast_inv] using hI.1.inv₀ hx

theorem width_tendsto_of_dyadic_mesh {I : ℕ → QInterval}
    (hvalid : ∀ s, (I s).valid) (hwidth : ∀ s, (I s).width ≤ DyadicSqrt.mesh s)
    (hmesh : Tendsto (fun s => (DyadicSqrt.mesh s : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun s => ((I s).width : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun s => ?_) (fun s => ?_) hmesh
  · exact_mod_cast QInterval.width_nonneg (hvalid s)
  · exact_mod_cast hwidth s

end QInterval

namespace DyadicSqrt

theorem mesh_tendsto_zero : Tendsto (fun s => (mesh s : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1 : ℝ)/2 < 1)).mul_const (1/4 : ℝ)
  have he : (fun s => (mesh s : ℝ)) = (fun s => (1/2 : ℝ)^s * (1/4)) := by
    funext s
    simp only [mesh, scale, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, pow_add,
      mul_inv, one_div, inv_pow]
    norm_num
  rw [he]
  simpa only [zero_mul] using h

theorem endpoints_tendsto {I : ℕ → QInterval} {x : ℝ}
    (hI : QInterval.EndpointsTendTo I x) (hv : ∀ s, (I s).valid)
    (hl : ∀ s, 0 ≤ (I s).lower) :
    QInterval.EndpointsTendTo (fun s => bounds s (I s)) (Real.sqrt x) := by
  constructor
  · have hlo := hI.1.sqrt
    have hlomesh : Tendsto (fun s => Real.sqrt ((I s).lower : ℝ) - (mesh s : ℝ)) atTop (𝓝 (Real.sqrt x)) := by
      simpa only [sub_zero] using hlo.sub mesh_tendsto_zero
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlomesh hlo
    · intro s
      have h := sqrt_lt_lower_add_mesh s (hl s)
      change Real.sqrt ((I s).lower : ℝ) - (mesh s : ℝ) ≤ (lower s (I s).lower : ℝ)
      linarith
    · intro s; exact lower_le_sqrt s (hl s)
  · have hup := hI.2.sqrt
    have hupmesh : Tendsto (fun s => Real.sqrt ((I s).upper : ℝ) + (mesh s : ℝ)) atTop (𝓝 (Real.sqrt x)) := by
      simpa only [add_zero] using hup.add mesh_tendsto_zero
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hup hupmesh
    · intro s; exact sqrt_le_upper s ((hl s).trans (hv s))
    · intro s
      have h := lower_le_sqrt s ((hl s).trans (hv s))
      have hu : (upper s (I s).upper : ℝ) ≤ (lower s (I s).upper : ℝ) + mesh s := by
        exact_mod_cast upper_le_lower_add_mesh s (I s).upper
      change (upper s (I s).upper : ℝ) ≤ Real.sqrt ((I s).upper : ℝ) + mesh s
      linarith

end DyadicSqrt

namespace ScalarExpr

private theorem binary_parts (A B : Option QInterval) (f : QInterval → QInterval → QInterval)
    {I : QInterval} (h : (do return f (← A) (← B)) = some I) :
    A = some (A.getD (.singleton 0)) ∧ B = some (B.getD (.singleton 0)) ∧
      I = f (A.getD (.singleton 0)) (B.getD (.singleton 0)) := by
  cases A with
  | none => simp at h
  | some A =>
    cases B with
    | none => simp at h
    | some B => simp_all

private theorem inv_parts (A : Option QInterval) {I : QInterval}
    (h : (do let a ← A; if 0 < a.lower then some a.invPos else none) = some I) :
    A = some (A.getD (.singleton 0)) ∧ 0 < (A.getD (.singleton 0)).lower ∧
      I = (A.getD (.singleton 0)).invPos := by
  cases A with
  | none => simp at h
  | some A =>
    by_cases hp : 0 < A.lower
    · simp_all
    · simp [hp] at h

private theorem sqrt_parts (A : Option QInterval) {I : QInterval} {s : ℕ}
    (h : (do let a ← A; if 0 ≤ a.lower then some (DyadicSqrt.bounds s a) else none) = some I) :
    A = some (A.getD (.singleton 0)) ∧ 0 ≤ (A.getD (.singleton 0)).lower ∧
      I = DyadicSqrt.bounds s (A.getD (.singleton 0)) := by
  cases A with
  | none => simp at h
  | some A =>
    by_cases hp : 0 ≤ A.lower
    · simp_all
    · simp [hp] at h

/-- Every successful stage uses the actual recursive interval evaluator. No exact
real arithmetic or selected certificate enters its executable dependency graph. -/
theorem bounds_endpoints_tendsto (p : ScalarExpr)
    (w σ : ℕ → QInterval) (w₀ σ₀ : ℝ)
    (hw : ∀ s, (w s).contains w₀) (hσ : ∀ s, (σ s).contains σ₀)
    (hww : Tendsto (fun s => ((w s).width : ℝ)) atTop (𝓝 0))
    (hσw : Tendsto (fun s => ((σ s).width : ℝ)) atTop (𝓝 0))
    (I : ℕ → QInterval) (hI : ∀ s, p.bounds s (w s) (σ s) = some (I s)) :
    QInterval.EndpointsTendTo I (p.eval w₀ σ₀) := by
  induction p generalizing I with
  | rat q =>
      have he : I = fun _ => QInterval.singleton q := by
        funext s; exact (Option.some.inj (hI s)).symm
      subst I
      exact ⟨tendsto_const_nhds,tendsto_const_nhds⟩
  | weight =>
      have he : I = w := by funext s; exact (Option.some.inj (hI s)).symm
      subst I
      exact QInterval.endpoints_of_width_tendsto hw hww
  | sigma =>
      have he : I = σ := by funext s; exact (Option.some.inj (hI s)).symm
      subst I
      exact QInterval.endpoints_of_width_tendsto hσ hσw
  | add a b ia ib =>
      let A := fun s => (a.bounds s (w s) (σ s)).getD (.singleton 0)
      let B := fun s => (b.bounds s (w s) (σ s)).getD (.singleton 0)
      have hp := fun s => binary_parts _ _ QInterval.add (hI s)
      have ha := ia A (fun s => (hp s).1)
      have hb := ib B (fun s => (hp s).2.1)
      have he : I = fun s => (A s).add (B s) := funext (fun s => (hp s).2.2)
      rw [he]
      exact ha.add hb
  | mul a b ia ib =>
      let A := fun s => (a.bounds s (w s) (σ s)).getD (.singleton 0)
      let B := fun s => (b.bounds s (w s) (σ s)).getD (.singleton 0)
      have hp := fun s => binary_parts _ _ QInterval.mul (hI s)
      have ha := ia A (fun s => (hp s).1)
      have hb := ib B (fun s => (hp s).2.1)
      have he : I = fun s => (A s).mul (B s) := funext (fun s => (hp s).2.2)
      rw [he]
      exact ha.mul hb
  | min a b ia ib =>
      let A := fun s => (a.bounds s (w s) (σ s)).getD (.singleton 0)
      let B := fun s => (b.bounds s (w s) (σ s)).getD (.singleton 0)
      have hp := fun s => binary_parts _ _ QInterval.min (hI s)
      have ha := ia A (fun s => (hp s).1)
      have hb := ib B (fun s => (hp s).2.1)
      have he : I = fun s => (A s).min (B s) := funext (fun s => (hp s).2.2)
      rw [he]
      exact ha.min hb
  | max a b ia ib =>
      let A := fun s => (a.bounds s (w s) (σ s)).getD (.singleton 0)
      let B := fun s => (b.bounds s (w s) (σ s)).getD (.singleton 0)
      have hp := fun s => binary_parts _ _ QInterval.max (hI s)
      have ha := ia A (fun s => (hp s).1)
      have hb := ib B (fun s => (hp s).2.1)
      have he : I = fun s => (A s).max (B s) := funext (fun s => (hp s).2.2)
      rw [he]
      exact ha.max hb
  | inv a ia =>
      let A := fun s => (a.bounds s (w s) (σ s)).getD (.singleton 0)
      have hp := fun s => inv_parts _ (hI s)
      have ha := ia A (fun s => (hp s).1)
      have hden : 0 < a.eval w₀ σ₀ := by
        have hc := a.evalScalarBounds_sound (hw 0) (hσ 0) (hp 0).1
        have hl : (0 : ℝ) < (A 0).lower := by exact_mod_cast (hp 0).2.1
        exact hl.trans_le hc.1
      have he : I = fun s => (A s).invPos := funext (fun s => (hp s).2.2)
      rw [he]
      exact ha.invPos (ne_of_gt hden)
  | sqrt a ia =>
      let A := fun s => (a.bounds s (w s) (σ s)).getD (.singleton 0)
      have hp := fun s => sqrt_parts _ (hI s)
      have ha := ia A (fun s => (hp s).1)
      have hv : ∀ s, (A s).valid := fun s => QInterval.valid_of_contains
        (a.evalScalarBounds_sound (hw s) (hσ s) (hp s).1)
      have he : I = fun s => DyadicSqrt.bounds s (A s) := funext (fun s => (hp s).2.2)
      rw [he]
      exact DyadicSqrt.endpoints_tendsto ha hv (fun s => (hp s).2.1)

/-- Width convergence of the actual scalar evaluator. Successful all-stage
execution is a separate, explicit premise discharged for the literal constants. -/
theorem scalarBounds_width_tendsto_zero (p : ScalarExpr)
    (w σ : ℕ → QInterval) (w₀ σ₀ : ℝ)
    (hw : ∀ s, (w s).contains w₀) (hσ : ∀ s, (σ s).contains σ₀)
    (hww : Tendsto (fun s => ((w s).width : ℝ)) atTop (𝓝 0))
    (hσw : Tendsto (fun s => ((σ s).width : ℝ)) atTop (𝓝 0))
    (I : ℕ → QInterval) (hI : ∀ s, p.bounds s (w s) (σ s) = some (I s)) :
    Tendsto (fun s => ((I s).width : ℝ)) atTop (𝓝 0) :=
  (bounds_endpoints_tendsto p w σ w₀ σ₀ hw hσ hww hσw I hI).width

/-- A finite collection of literal scalar expressions has one common rational
precision threshold; the quantifier over expressions follows the stage threshold. -/
theorem scalarFamily_widths_refine (ps : Fin a → ScalarExpr)
    (w σ : ℕ → QInterval) (w₀ σ₀ : ℝ)
    (hw : ∀ s, (w s).contains w₀) (hσ : ∀ s, (σ s).contains σ₀)
    (hww : Tendsto (fun s => ((w s).width : ℝ)) atTop (𝓝 0))
    (hσw : Tendsto (fun s => ((σ s).width : ℝ)) atTop (𝓝 0))
    (I : ℕ → Fin a → QInterval) (hI : ∀ s i, (ps i).bounds s (w s) (σ s) = some (I s i)) :
    ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (I s i).width ≤ δ := by
  intro δ hδ
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have heach : ∀ i : Fin a, ∀ᶠ s in atTop, (I s i).width ≤ δ := by
    intro i
    have ht := scalarBounds_width_tendsto_zero (ps i) w σ w₀ σ₀ hw hσ hww hσw
      (fun s => I s i) (fun s => hI s i)
    filter_upwards [ht.eventually_lt_const hδr] with s hs
    exact_mod_cast hs.le
  exact eventually_atTop.mp (eventually_all.mpr heach)

end ScalarExpr
end Cover
