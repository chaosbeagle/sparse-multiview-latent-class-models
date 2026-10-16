import Cover.MarginValidation

namespace Cover.AlgCode

/-- Stage mesh fixed by the frozen scalar specification. -/
def marginMesh (s : ℕ) : ℚ := 1 / (2 : ℚ)^(s+2)

theorem marginMesh_pos (s : ℕ) : 0 < marginMesh s := by
  exact one_div_pos.mpr (pow_pos (by norm_num) _)

theorem marginMesh_le_quarter (s : ℕ) : marginMesh s ≤ 1/4 := by
  have hpow : (4 : ℚ) ≤ (2 : ℚ)^(s+2) := by
    calc
      (4 : ℚ) = (2 : ℚ)^2 := by norm_num
      _ ≤ (2 : ℚ)^(s+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact (one_div_le_one_div_of_le (by norm_num) hpow)

/-- Actual total preprocessing: positive current bracket, then rational precision. -/
def prepareMargin (c : AlgCode) (hv : c.valid) (hp : compareTotal c hv 0 = .gt) (s : ℕ) : AlgCode :=
  refinePrecisely (positiveTotal c hv hp) (marginMesh s)

 theorem prepareMargin_sound {c : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    (prepareMargin c hv hp s).valid ∧ (prepareMargin c hv hp s).denotes x ∧
      0 < (prepareMargin c hv hp s).interval.lower ∧
      (prepareMargin c hv hp s).interval.width ≤ marginMesh s ∧
      (prepareMargin c hv hp s).interval.subset c.interval := by
  obtain ⟨hpv, hpd, hpp, hps⟩ := positiveTotal_sound hv hx hp
  obtain ⟨hdv, hdd, hdw, hds⟩ := refinePrecisely_sound hpv hpd (marginMesh_pos s)
  exact ⟨hdv, hdd, hpp.trans_le hds.1, hdw, hps.1.trans hds.1, hds.2.trans hps.2⟩

 theorem prepareMargin_contains {c : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) (hp : compareTotal c hv 0 = .gt) (s : ℕ) :
    (prepareMargin c hv hp s).interval.contains x :=
  denotes_contains (prepareMargin_sound hv hx hp s).2.1

 theorem prepareMargin_upper_le {c : AlgCode} {x u : ℝ}
    (hv : c.valid) (hx : c.denotes x) (hp : compareTotal c hv 0 = .gt) (s : ℕ) (hxu : x ≤ u) :
    ((prepareMargin c hv hp s).interval.upper : ℝ) ≤ u + (marginMesh s : ℝ) := by
  have hs := prepareMargin_sound hv hx hp s
  have hc := denotes_contains hs.2.1
  have hw : ((prepareMargin c hv hp s).interval.width : ℝ) ≤ marginMesh s := by
    exact_mod_cast hs.2.2.2.1
  dsimp [QInterval.width] at hw
  push_cast at hw
  linarith [hc.1]

 theorem prepareMargin_sigma_upper {c : AlgCode} {x : ℝ}
    (hv : c.valid) (hx : c.denotes x) (hp : compareTotal c hv 0 = .gt) (s : ℕ) (hx1 : x ≤ 1) :
    (prepareMargin c hv hp s).interval.upper ≤ 5/4 := by
  have hu := prepareMargin_upper_le hv hx hp s hx1
  have hm : (marginMesh s : ℝ) ≤ 1/4 := by
    have hr := (Rat.cast_le (K := ℝ)).2 (marginMesh_le_quarter s)
    norm_num at hr
    exact hr
  have hh : ((prepareMargin c hv hp s).interval.upper : ℝ) ≤ 5/4 := by linarith
  apply (Rat.cast_le (K := ℝ)).1
  norm_num
  exact hh

end Cover.AlgCode
