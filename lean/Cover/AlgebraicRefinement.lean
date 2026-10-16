import Cover.AlgebraicDefs

namespace Cover
namespace QInterval

def subset (I J : QInterval) : Prop := J.lower ≤ I.lower ∧ I.upper ≤ J.upper

 theorem midpoint_bounds {I : QInterval} (h : I.valid) :
    I.lower ≤ I.midpoint ∧ I.midpoint ≤ I.upper := by
  dsimp [valid, midpoint] at *
  constructor <;> linarith

 theorem midpoint_strict {I : QInterval} (h : I.lower < I.upper) :
    I.lower < I.midpoint ∧ I.midpoint < I.upper := by
  dsimp [midpoint]
  constructor <;> linarith

 theorem contains_of_subset {I J : QInterval} {x : ℝ}
    (h : I.subset J) (hx : I.contains x) : J.contains x := by
  exact ⟨le_trans (by exact_mod_cast h.1) hx.1,
    le_trans hx.2 (by exact_mod_cast h.2)⟩

end QInterval
namespace AlgCode

 theorem refine_nested (c : AlgCode) (h : c.interval.valid) :
    c.refine.interval.subset c.interval := by
  cases c with
  | rat q => exact ⟨le_rfl, le_rfl⟩
  | root p I =>
    have hm := QInterval.midpoint_bounds h
    simp only [refine]
    split_ifs <;> simp_all [interval, QInterval.subset, QInterval.singleton]

 theorem refine_interval_valid (c : AlgCode) (h : c.interval.valid) :
    c.refine.interval.valid := by
  cases c with
  | rat q => exact le_rfl
  | root p I =>
    have hm := QInterval.midpoint_bounds h
    simp only [refine]
    split_ifs <;> simp_all [interval, QInterval.valid, QInterval.singleton]

 theorem refine_width (c : AlgCode) :
    c.refine.interval.width = 0 ∨
    c.refine.interval.width = c.interval.width / 2 := by
  cases c with
  | rat q => left; simp [refine, interval, QInterval.width, QInterval.singleton]
  | root p I =>
    simp only [refine]
    split_ifs
    · left; simp [interval, QInterval.width, QInterval.singleton]
    · right; simp only [interval, QInterval.width, QInterval.midpoint]; ring
    · right; simp only [interval, QInterval.width, QInterval.midpoint]; ring

 theorem refine_width_le (c : AlgCode) (h : c.interval.valid) :
    c.refine.interval.width ≤ c.interval.width / 2 := by
  rcases refine_width c with hz | he
  · rw [hz]; exact div_nonneg (sub_nonneg.mpr h) (by norm_num)
  · exact le_of_eq he

 theorem iterate_valid (c : AlgCode) (h : c.interval.valid) (n : ℕ) :
    (c.iterate n).interval.valid := by
  induction n with
  | zero => exact h
  | succ n ih => exact refine_interval_valid _ ih

 theorem iterate_nested (c : AlgCode) (h : c.interval.valid) (n : ℕ) :
    (c.iterate n).interval.subset c.interval := by
  induction n with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    have hs := refine_nested (c.iterate n) (iterate_valid c h n)
    exact ⟨ih.1.trans hs.1, hs.2.trans ih.2⟩

 theorem iterate_width (c : AlgCode) (h : c.interval.valid) (n : ℕ) :
    (c.iterate n).interval.width ≤ c.interval.width / (2 : ℚ)^n := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    calc
      (c.iterate (n+1)).interval.width ≤ (c.iterate n).interval.width / 2 :=
        refine_width_le _ (iterate_valid c h n)
      _ ≤ (c.interval.width / (2 : ℚ)^n) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
      _ = c.interval.width / (2 : ℚ)^(n+1) := by rw [pow_succ, div_div]

 theorem exists_halving_bound (w h : ℚ) (hh : 0 < h) :
    ∃ n : ℕ, w / (2 : ℚ)^n ≤ h := by
  obtain ⟨n, hn⟩ := exists_nat_gt (w / h)
  refine ⟨n, ?_⟩
  have hp : (n : ℚ) < (2 : ℚ)^n := by exact_mod_cast Nat.lt_two_pow_self (n := n)
  have hwp : w < (2 : ℚ)^n * h := (div_lt_iff₀ hh).mp (hn.trans hp)
  apply (div_le_iff₀ (pow_pos (by norm_num) _)).mpr
  nlinarith

 theorem iterate_succ_left (c : AlgCode) (n : ℕ) :
    c.iterate (n + 1) = c.refine.iterate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (c.iterate (n+1)).refine = (c.refine.iterate n).refine
    rw [ih]

 theorem refineToPrecision_success_of_iterate (h : ℚ) (c : AlgCode) (n : ℕ)
    (hp : (c.iterate n).interval.width ≤ h) :
    ∃ d, refineToPrecision h n c = some d ∧ d.interval.width ≤ h := by
  induction n generalizing c with
  | zero => exact ⟨c, by simp [refineToPrecision, iterate] at hp ⊢; exact hp, hp⟩
  | succ n ih =>
    simp only [refineToPrecision]
    split_ifs with hw
    · exact ⟨c, rfl, hw⟩
    · exact ih c.refine (by rwa [iterate_succ_left] at hp)

 theorem refine_to_precision_terminates (c : AlgCode) (hv : c.interval.valid)
    (h : ℚ) (hh : 0 < h) :
    ∃ n d, refineToPrecision h n c = some d ∧ d.interval.width ≤ h := by
  obtain ⟨n, hn⟩ := exists_halving_bound c.interval.width h hh
  obtain ⟨d, hd⟩ := refineToPrecision_success_of_iterate h c n ((iterate_width c hv n).trans hn)
  exact ⟨n, d, hd⟩

end AlgCode
end Cover
