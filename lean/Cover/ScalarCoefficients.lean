import Cover.MarginValidation
import Cover.AlgebraicTotal
import Cover.EveryStage
import Cover.ScalarConvergence

open Filter
open scoped Topology

namespace Cover
namespace AlgCode

/-- The actual executable preparation first obtains a positive bracket and then
refines that current code to the mandated dyadic mesh. -/
def preparedBracket (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt)
    (s : ℕ) : QInterval :=
  (refinePrecisely (positiveTotal c hv hp) (DyadicSqrt.mesh s)).interval

theorem preparedBracket_sound {c : AlgCode} {x : ℝ} (hv : c.valid) (hx : c.denotes x)
    (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    (preparedBracket c hv hp s).valid ∧ (preparedBracket c hv hp s).contains x ∧
      0 < (preparedBracket c hv hp s).lower ∧
      (preparedBracket c hv hp s).width ≤ DyadicSqrt.mesh s := by
  obtain ⟨hvalid,hden,hpos,hnest⟩ := positiveTotal_sound hv hx hp
  obtain ⟨hv',hx',hw',hn'⟩ := refinePrecisely_sound hvalid hden (DyadicSqrt.mesh_pos s)
  exact ⟨valid_interval hv',denotes_contains hx',hpos.trans_le hn'.1,hw'⟩

theorem preparedBracket_width_tendsto {c : AlgCode} {x : ℝ} (hv : c.valid)
    (hx : c.denotes x) (hp : compareTotal c hv 0 = .gt) :
    Tendsto (fun s => ((preparedBracket c hv hp s).width : ℝ)) atTop (𝓝 0) :=
  QInterval.width_tendsto_of_dyadic_mesh
    (fun s => (preparedBracket_sound hv hx hp s).1)
    (fun s => (preparedBracket_sound hv hx hp s).2.2.2) DyadicSqrt.mesh_tendsto_zero

end AlgCode

namespace Literal

/-- Only the three scalar leaves used by the full-real polynomial compiler. -/
def coefficientSyntax (n : Fin g → ℕ) (edges : List (List (Fin g))) : Fin 3 → ScalarExpr :=
  ![.weight, ScalarExpr.sigma.pow 2, (R n edges).pow 2]

def coefficientBounds (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (s : ℕ) (w σ : QInterval) : Fin 3 → QInterval :=
  fun i => ((coefficientSyntax n edges i).bounds s w σ).getD (.singleton 0)

private theorem eq_some_getD {I : Option QInterval} (h : I.isSome = true) :
    I = some (I.getD (.singleton 0)) := by
  cases I with
  | none => contradiction
  | some I => rfl

/-- At every natural stage, including zero, the fallback branch of coefficientBounds
is unreachable for prepared admitted margins. -/
theorem coefficientBounds_defined (n : Fin g → ℕ) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ []) (s : ℕ) (w σ : QInterval)
    (hw : w.valid) (hσ : σ.valid) (hw0 : 0 < w.lower) (hσ0 : 0 < σ.lower)
    {σ₀ : ℝ} (hσc : σ.contains σ₀) (hσ₀ : σ₀ ≤ 1)
    (hσwid : σ.width ≤ DyadicSqrt.mesh s) (i : Fin 3) :
    (coefficientSyntax n edges i).bounds s w σ = some (coefficientBounds n edges s w σ i) := by
  apply eq_some_getD
  have hσu := prepared_sigma_upper_le hσc hσ₀ hσwid
  have hdef := every_stage_denominators_positive (s := s) n hn he hw hσ hw0 hσ0 hσu
  fin_cases i
  · rfl
  · exact hasLower_isSome ((sigma_hasLower (s := s) (w := w) hσ).pow hσ0.le 2)
  · obtain ⟨l,hl,hR⟩ := hdef.2.2.2
    exact hasLower_isSome (hR.pow hl.le 2)

@[simp] theorem coefficientSyntax_eval (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (w σ : ℝ) : (fun i => (coefficientSyntax n edges i).eval w σ) =
      ![w, σ^2, ((R n edges).eval w σ)^2] := by
  funext i
  fin_cases i <;> simp [coefficientSyntax, ScalarExpr.eval]

end Literal

/-- The three coefficient intervals are computed from finite algebraic margin codes.
Proof arguments are finite validator/comparator evidence and erase at extraction. -/
def scalarCoefficients (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (w σ : AlgCode) (hw : w.valid) (hσ : σ.valid)
    (hwp : w.compareTotal hw 0 = .gt) (hσp : σ.compareTotal hσ 0 = .gt)
    (s : ℕ) : Fin 3 → QInterval :=
  Literal.coefficientBounds n edges s (w.preparedBracket hw hwp s) (σ.preparedBracket hσ hσp s)

theorem scalarCoefficients_sound (n : Fin g → ℕ) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ [])
    (w σ : AlgCode) (hw : w.valid) (hσ : σ.valid)
    (hwp : w.compareTotal hw 0 = .gt) (hσp : σ.compareTotal hσ 0 = .gt)
    {w₀ σ₀ : ℝ} (hwd : w.denotes w₀) (hσd : σ.denotes σ₀) (hσ₀ : σ₀ ≤ 1)
    (s : ℕ) (i : Fin 3) :
    (scalarCoefficients n edges w σ hw hσ hwp hσp s i).contains
      (![w₀, σ₀^2, ((Literal.R n edges).eval w₀ σ₀)^2] i) := by
  have hwv := w.preparedBracket_sound hw hwd hwp s
  have hσv := σ.preparedBracket_sound hσ hσd hσp s
  have hd := Literal.coefficientBounds_defined n hn he s _ _ hwv.1 hσv.1 hwv.2.2.1 hσv.2.2.1
    hσv.2.1 hσ₀ hσv.2.2.2 i
  have hs := (Literal.coefficientSyntax n edges i).evalScalarBounds_sound hwv.2.1 hσv.2.1 hd
  have hv := congrFun (Literal.coefficientSyntax_eval n edges w₀ σ₀) i
  rw [hv] at hs
  exact hs

theorem scalarCoefficients_widths_refine (n : Fin g → ℕ) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ [])
    (w σ : AlgCode) (hw : w.valid) (hσ : σ.valid)
    (hwp : w.compareTotal hw 0 = .gt) (hσp : σ.compareTotal hσ 0 = .gt)
    {w₀ σ₀ : ℝ} (hwd : w.denotes w₀) (hσd : σ.denotes σ₀) (hσ₀ : σ₀ ≤ 1) :
    ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i,
      (scalarCoefficients n edges w σ hw hσ hwp hσp s i).width ≤ δ := by
  apply ScalarExpr.scalarFamily_widths_refine (Literal.coefficientSyntax n edges)
    (w.preparedBracket hw hwp) (σ.preparedBracket hσ hσp) w₀ σ₀
    (fun s => (w.preparedBracket_sound hw hwd hwp s).2.1)
    (fun s => (σ.preparedBracket_sound hσ hσd hσp s).2.1)
    (w.preparedBracket_width_tendsto hw hwd hwp)
    (σ.preparedBracket_width_tendsto hσ hσd hσp)
  intro s i
  have hwv := w.preparedBracket_sound hw hwd hwp s
  have hσv := σ.preparedBracket_sound hσ hσd hσp s
  exact Literal.coefficientBounds_defined n hn he s _ _ hwv.1 hσv.1 hwv.2.2.1 hσv.2.2.1
    hσv.2.1 hσ₀ hσv.2.2.2 i

namespace Margins

theorem valid_positive_comparisons {r : ℕ} {w σ : AlgCode} (h : Valid r w σ) :
    w.compareTotal (valid_codes h).1 0 = .gt ∧ σ.compareTotal (valid_codes h).2 0 = .gt := by
  obtain ⟨hw,hσ,hwp,hwu,hσp,hσu⟩ := valid_comparisons h
  exact ⟨hwp,hσp⟩

theorem sigma_le_one_of_denotes {r : ℕ} {w σ : AlgCode} (h : Valid r w σ)
    {σ₀ : ℝ} (hσd : σ.denotes σ₀) : σ₀ ≤ 1 := by
  obtain ⟨hw,hσ,hwp,hwu,hσp,hσu⟩ := valid_comparisons h
  apply le_of_not_gt
  intro hlt
  apply hσu
  exact (AlgCode.compareTotal_eq_gt_iff hσ hσd 1).2 (by simpa using hlt)

end Margins

/-- End-to-end finite-data coefficient preparation after the exact margin validator.
No denoted real number is an argument to this executable function. -/
def validatedScalarCoefficients (n : Fin g → ℕ) (edges : List (List (Fin g)))
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ) : ℕ → Fin 3 → QInterval :=
  scalarCoefficients n edges w σ (Margins.valid_codes h).1 (Margins.valid_codes h).2
    (Margins.valid_positive_comparisons h).1 (Margins.valid_positive_comparisons h).2

theorem validatedScalarCoefficients_sound (n : Fin g → ℕ) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ [])
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ)
    {w₀ σ₀ : ℝ} (hwd : w.denotes w₀) (hσd : σ.denotes σ₀) (s : ℕ) (i : Fin 3) :
    (validatedScalarCoefficients n edges r w σ h s i).contains
      (![w₀,σ₀^2,((Literal.R n edges).eval w₀ σ₀)^2] i) :=
  scalarCoefficients_sound n hn he w σ _ _ _ _ hwd hσd
    (Margins.sigma_le_one_of_denotes h hσd) s i

theorem validatedScalarCoefficients_widths_refine (n : Fin g → ℕ) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ [])
    (r : ℕ) (w σ : AlgCode) (h : Margins.Valid r w σ) :
    ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i,
      (validatedScalarCoefficients n edges r w σ h s i).width ≤ δ := by
  obtain ⟨w₀,hwd,_⟩ := AlgCode.validAlgBracket_denotes_unique w (Margins.valid_codes h).1
  obtain ⟨σ₀,hσd,_⟩ := AlgCode.validAlgBracket_denotes_unique σ (Margins.valid_codes h).2
  exact scalarCoefficients_widths_refine n hn he w σ _ _ _ _ hwd hσd
    (Margins.sigma_le_one_of_denotes h hσd)

end Cover
