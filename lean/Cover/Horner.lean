import Cover.PolyConvergence
import Cover.IntervalMonotone

namespace Cover.QInterval

theorem mag_le_abs_add_width {I : QInterval} {x : ℝ} (hx : I.contains x) :
    (I.mag : ℝ) ≤ |x| + (I.width : ℝ) := by
  simp only [mag, Rat.cast_max, Rat.cast_abs, width, Rat.cast_sub]
  apply max_le
  · apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, le_abs_self x, neg_le_abs x]
  · apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, le_abs_self x, neg_le_abs x]

end Cover.QInterval

namespace Cover

/-- Coefficients are ordered from constant coefficient upward; Horner uses exact
rational additions and the all-four-products interval multiplication. -/
def hornerExpr : List ℚ → PolyExpr 1 0
  | [] => .rat 0
  | c :: cs => .add (.rat c) (.mul (.var 0) (hornerExpr cs))

def hornerInterval (cs : List ℚ) (I : QInterval) : QInterval :=
  PolyExpr.interval Fin.elim0 (fun _ => I) (hornerExpr cs)

noncomputable def hornerValue (cs : List ℚ) (x : ℝ) : ℝ :=
  cs.foldr (fun (c : ℚ) (y : ℝ) => (c : ℝ) + x*y) 0

@[simp] theorem hornerInterval_nil (I : QInterval) : hornerInterval [] I = QInterval.singleton 0 := rfl
@[simp] theorem hornerInterval_cons (c : ℚ) (cs : List ℚ) (I : QInterval) :
    hornerInterval (c::cs) I = QInterval.add (QInterval.singleton c) (QInterval.mul I (hornerInterval cs I)) := rfl

theorem hornerExpr_eval (cs : List ℚ) (x : ℝ) :
    (hornerExpr cs).eval Fin.elim0 (fun _ => x) = hornerValue cs x := by
  induction cs with
  | nil => simp [hornerExpr, PolyExpr.eval, hornerValue]
  | cons c cs ih => simp only [hornerExpr, PolyExpr.eval, ih, hornerValue, List.foldr_cons]

theorem hornerInterval_sound (cs : List ℚ) {I : QInterval} {x : ℝ} (hx : I.contains x) :
    (hornerInterval cs I).contains (hornerValue cs x) := by
  rw [← hornerExpr_eval]
  exact (hornerExpr cs).interval_sound (fun i => Fin.elim0 i) (fun _ => hx)

theorem hornerInterval_valid (cs : List ℚ) {I : QInterval} (hI : I.valid) :
    (hornerInterval cs I).valid :=
  (hornerExpr cs).interval_valid (fun i => Fin.elim0 i) (fun _ => hI)

theorem hornerInterval_subinterval (cs : List ℚ) {I J : QInterval} (hI : I.valid)
    (hIJ : I.Subinterval J) : (hornerInterval cs I).Subinterval (hornerInterval cs J) :=
  (hornerExpr cs).interval_subinterval (fun i => Fin.elim0 i) (fun _ => hI)
    (fun i => Fin.elim0 i) (fun _ => hIJ)

/-- Uniform over every rational interval containing the designated real point,
not merely a selected sequence of brackets. -/
theorem hornerInterval_converges_at (cs : List ℚ) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ I : QInterval, I.contains x → I.width ≤ δ →
      hornerValue cs x - (hornerInterval cs I).lower < ε ∧
      ((hornerInterval cs I).upper : ℝ) - hornerValue cs x < ε := by
  obtain ⟨M,hM⟩ := exists_rat_gt (|x|+1)
  have hM0 : (0 : ℚ) ≤ M := by
    have : (0 : ℝ) ≤ M := by linarith [abs_nonneg x]
    exact_mod_cast this
  obtain ⟨δ,hδ,hconv⟩ := PolyExpr.uniform_joint_convergence [hornerExpr cs] hM0 hε
  refine ⟨min 1 δ, lt_min (by norm_num) hδ, ?_⟩
  intro I hx hw
  have hw1 : I.width ≤ 1 := hw.trans (min_le_left _ _)
  have hmag : I.mag ≤ M := by
    have hwidth : (I.width : ℝ) ≤ 1 := by exact_mod_cast hw1
    have := QInterval.mag_le_abs_add_width hx
    have : (I.mag : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have h := hconv Fin.elim0 (fun _ => I) Fin.elim0 (fun _ => x)
    (fun i => Fin.elim0 i) (fun _ => hx) (fun i => Fin.elim0 i) (fun _ => hmag)
    (fun i => Fin.elim0 i) (fun _ => hw.trans (min_le_right _ _))
    (hornerExpr cs) (List.mem_singleton_self _)
  simpa only [hornerExpr_eval, hornerInterval] using h

/-- A nonzero polynomial value admits a genuine Horner derivative-sign certificate
on every sufficiently narrow rational bracket around it. -/
theorem hornerInterval_eventually_excludes_zero (cs : List ℚ) (x : ℝ)
    (hne : hornerValue cs x ≠ 0) : ∃ δ : ℚ, 0 < δ ∧
    ∀ I : QInterval, I.contains x → I.width ≤ δ →
      0 < (hornerInterval cs I).lower ∨ (hornerInterval cs I).upper < 0 := by
  have habs : 0 < |hornerValue cs x| := abs_pos.mpr hne
  obtain ⟨δ,hδ,hconv⟩ := hornerInterval_converges_at cs x (half_pos habs)
  refine ⟨δ,hδ,?_⟩
  intro I hx hw
  have h := hconv I hx hw
  rcases lt_or_gt_of_ne hne with hn | hp
  · right
    have hneg : ((hornerInterval cs I).upper : ℝ) < 0 := by
      rw [abs_of_neg hn] at h
      linarith [h.2]
    exact_mod_cast hneg
  · left
    have hpos : (0 : ℝ) < (hornerInterval cs I).lower := by
      rw [abs_of_pos hp] at h
      linarith [h.1]
    exact_mod_cast hpos

end Cover
