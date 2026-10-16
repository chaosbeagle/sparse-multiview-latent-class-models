import Cover.Horner
import Cover.Mesh
import Cover.UniformStages

namespace Cover

theorem splitBox_subinterval (B : QBox n) (hB : B.Valid) (i : Fin n) (right : Bool) (j : Fin n) :
    (splitBox B i right j).Subinterval (B j) := by
  by_cases hj : j = i
  · subst j
    have hi := hB i
    cases right <;> simp [splitBox, QInterval.Subinterval, QInterval.midpoint, QInterval.valid] at * <;> linarith
  · simp [splitBox, hj, QInterval.Subinterval]

theorem cyclicBox_subinterval_unit (hn : 0 < n) (h : CyclicBox hn depth B) (i : Fin n) :
    (B i).Subinterval (unitBox n i) := by
  induction h with
  | root => exact ⟨le_refl _, le_refl _⟩
  | @child depth B h right ih =>
      have hs := splitBox_subinterval B (cyclicBox_valid hn h) ⟨depth%n, Nat.mod_lt _ hn⟩ right i
      exact ⟨(ih.1).trans hs.1, hs.2.trans ih.2⟩

theorem mag_le_one_of_subinterval_unit {I : QInterval} (hI : I.valid)
    (hsub : I.Subinterval ⟨0,1⟩) : I.mag ≤ 1 := by
  have hl : 0 ≤ I.lower := hsub.1
  have hu : I.upper ≤ 1 := hsub.2
  apply max_le
  · rw [abs_of_nonneg hl]; exact hI.trans hu
  · rw [abs_of_nonneg (hl.trans hI)]; exact hu

theorem cyclicBox_mag_le_one (hn : 0 < n) (h : CyclicBox hn depth B) (i : Fin n) :
    (B i).mag ≤ 1 := mag_le_one_of_subinterval_unit (cyclicBox_valid hn h i)
      (cyclicBox_subinterval_unit hn h i)

theorem cyclicBox_lower_in_unit (hn : 0 < n) (h : CyclicBox hn depth B) :
    (unitBox n).Contains (fun i => (B i).lower) := by
  intro i
  exact QInterval.subinterval_contains (cyclicBox_subinterval_unit hn h i)
    (QInterval.contains_lower (cyclicBox_valid hn h i))

/-- Real fixed coefficient values and vanishing coefficient widths imply an
independent, uniform magnitude bound after a finite stage. -/
theorem coefficient_magnitude_eventually_bounded (ics : ℕ → Fin a → QInterval)
    (cs : Fin a → ℝ) (hcs : ∀ s i, (ics s i).contains (cs i))
    (hcw : ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (ics s i).width ≤ δ) :
    ∃ M : ℚ, 1 ≤ M ∧ ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (ics s i).mag ≤ M := by
  obtain ⟨M,hM⟩ := exists_rat_gt ((∑ i, |cs i|)+1)
  have hsum : (0 : ℝ) ≤ ∑ i, |cs i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hM1 : (1 : ℚ) ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  obtain ⟨s₀,hs₀⟩ := hcw 1 (by norm_num)
  refine ⟨M,hM1,s₀,?_⟩
  intro s hs i
  have hi : |cs i| ≤ ∑ k, |cs k| := Finset.single_le_sum (f := fun k => |cs k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  have hwidth : ((ics s i).width : ℝ) ≤ 1 := by exact_mod_cast hs₀ s hs i
  have hmag := QInterval.mag_le_abs_add_width (hcs s i)
  have : ((ics s i).mag : ℝ) ≤ M := by linarith
  exact_mod_cast this

theorem box_mag_le_one_of_contained (B : QBox n) (hB : B.Valid)
    (hsub : ∀ x, B.Contains x → (unitBox n).Contains x) (i : Fin n) : (B i).mag ≤ 1 := by
  have hl := hsub (fun k => ((B k).lower : ℝ)) (fun k => QInterval.contains_lower (hB k)) i
  have hu := hsub (fun k => ((B k).upper : ℝ)) (fun k => QInterval.contains_upper (hB k)) i
  simp only [unitBox, QInterval.contains, Rat.cast_zero, Rat.cast_one] at hl hu
  apply mag_le_one_of_subinterval_unit (hB i)
  constructor
  · exact_mod_cast hl.1
  · exact_mod_cast hu.2

/-- Uniform endpoint error on every rational subbox of the closed unit box,
including degenerate boxes and every real point, with a single stage threshold. -/
theorem coverInterval_uniform_convergence (ps : List (PolyExpr n a))
    (ics : ℕ → Fin a → QInterval) (cs : Fin a → ℝ)
    (hcs : ∀ s i, (ics s i).contains (cs i))
    (hcw : ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (ics s i).width ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ (B : QBox n), B.Valid →
      (∀ x, B.Contains x → (unitBox n).Contains x) →
      (∀ i, (B i).width ≤ dyadic s) → ∀ x, B.Contains x → ∀ p ∈ ps,
        p.eval cs x - ((p.interval (ics s) B).lower : ℝ) < ε ∧
        ((p.interval (ics s) B).upper : ℝ) - p.eval cs x < ε := by
  obtain ⟨M,hM,sM,hsM⟩ := coefficient_magnitude_eventually_bounded ics cs hcs hcw
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  obtain ⟨δ,hδ,hconv⟩ := PolyExpr.uniform_joint_convergence ps hM0 hε
  obtain ⟨sc,hsc⟩ := hcw δ hδ
  obtain ⟨sx,hsx⟩ := PolyExpr.dyadic_mesh_eventually_le hδ
  refine ⟨max sM (max sc sx),?_⟩
  intro s hs B hB hsub hw x hx p hp
  have hsM' : sM ≤ s := (le_max_left _ _).trans hs
  have hsc' : sc ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hsx' : sx ≤ s := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  apply hconv (ics s) B cs x (hcs s) hx (hsM s hsM')
    (fun i => (box_mag_le_one_of_contained B hB hsub i).trans hM) (hsc s hsc') ?_ p hp
  intro i
  apply (hw i).trans
  simpa only [dyadic, inv_pow, one_div] using hsx s hsx'

theorem cyclicInterval_uniform_convergence (ps : List (PolyExpr n a)) (hn : 0 < n)
    (ics : ℕ → Fin a → QInterval) (cs : Fin a → ℝ)
    (hcs : ∀ s i, (ics s i).contains (cs i))
    (hcw : ∀ δ : ℚ, 0 < δ → ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ i, (ics s i).width ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ : ℕ, ∀ s ≥ s₀, ∀ (B : QBox n), CyclicBox hn (n*s) B →
      ∀ x, B.Contains x → ∀ p ∈ ps,
        p.eval cs x - ((p.interval (ics s) B).lower : ℝ) < ε ∧
        ((p.interval (ics s) B).upper : ℝ) - p.eval cs x < ε := by
  obtain ⟨s₀,hs₀⟩ := coverInterval_uniform_convergence ps ics cs hcs hcw hε
  refine ⟨s₀,?_⟩
  intro s hs B hB x hx p hp
  exact hs₀ s hs B (cyclicBox_valid hn hB)
    (fun y hy i => QInterval.subinterval_contains (cyclicBox_subinterval_unit hn hB i) (hy i))
    (fun i => (full_depth_mesh_width hn s hB i).le) x hx p hp

end Cover
