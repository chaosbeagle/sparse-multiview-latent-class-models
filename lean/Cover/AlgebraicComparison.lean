import Cover.AlgebraicBisection

namespace Cover
namespace AlgCode

def compareStep (c : AlgCode) (t : ℚ) : Option Ordering :=
  match c with
  | .rat q => some (if q < t then .lt else if q = t then .eq else .gt)
  | .root p I =>
    if t ≤ I.lower then some .gt
    else if I.upper ≤ t then some .lt
    else if IntPolynomial.horner p t = 0 then some .eq else none

def compareBracketRat (t : ℚ) : ℕ → AlgCode → Option Ordering
  | 0, c => compareStep c t
  | n+1, c => match compareStep c t with
      | some o => some o
      | none => compareBracketRat t n c.refine

def comparisonMeaning (o : Ordering) (x : ℝ) (t : ℚ) : Prop :=
  match o with
  | .lt => x < (t : ℝ)
  | .eq => x = (t : ℝ)
  | .gt => (t : ℝ) < x

 theorem compareStep_correct {c : AlgCode} {x : ℝ} {t : ℚ} {o : Ordering}
    (hv : c.valid) (hx : c.denotes x) (ho : compareStep c t = some o) :
    comparisonMeaning o x t := by
  cases c with
  | rat q =>
    change x = (q : ℝ) at hx
    subst x
    simp only [compareStep] at ho
    split_ifs at ho with hlt heq
    · cases ho; dsimp [comparisonMeaning]; exact_mod_cast hlt
    · cases ho; dsimp [comparisonMeaning]; exact_mod_cast heq
    · cases ho; dsimp [comparisonMeaning]; exact_mod_cast (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq))
  | root p I =>
    simp only [compareStep] at ho
    split_ifs at ho with hl hu hp
    · cases ho
      exact lt_of_le_of_lt (by exact_mod_cast hl) hx.2.1
    · cases ho
      exact lt_of_lt_of_le hx.2.2 (by exact_mod_cast hu)
    · cases ho
      have hpr : IntPolynomial.horner p (t : ℝ) = 0 := by
        rw [← IntPolynomial.cast_horner, hp, Rat.cast_zero]
      exact IntPolynomial.unique_on_of_derivative_excludes p hv.2.2.2.2
        ⟨hx.2.1.le, hx.2.2.le⟩
        ⟨by exact_mod_cast (le_of_lt (lt_of_not_ge hl)), by exact_mod_cast (le_of_lt (lt_of_not_ge hu))⟩
        (hx.1.trans hpr.symm)

 theorem compareBracketRat_correct {c : AlgCode} {x : ℝ} {t : ℚ} {o : Ordering}
    (hv : c.valid) (hx : c.denotes x) (n : ℕ) (ho : compareBracketRat t n c = some o) :
    comparisonMeaning o x t := by
  induction n generalizing c with
  | zero => exact compareStep_correct hv hx ho
  | succ n ih =>
    simp only [compareBracketRat] at ho
    cases hs : compareStep c t with
    | none =>
      rw [hs] at ho
      exact ih (refine_valid hv) (refine_denotes hv hx) ho
    | some a =>
      rw [hs] at ho
      cases ho
      exact compareStep_correct hv hx hs

 theorem compareStep_eq_success {c : AlgCode} {x : ℝ} {t : ℚ}
    (hx : c.denotes x) (he : x = (t : ℝ)) : ∃ o, compareStep c t = some o := by
  cases c with
  | rat q => exact ⟨_, rfl⟩
  | root p I =>
    have hp : IntPolynomial.horner p t = 0 := by
      have hr := hx.1
      rw [he, ← IntPolynomial.cast_horner] at hr
      exact_mod_cast hr
    simp only [compareStep]
    split_ifs <;> exact ⟨_, rfl⟩

 theorem compareStep_success_of_width {c : AlgCode} {x : ℝ} {t : ℚ}
    (hx : c.denotes x) (hw : (c.interval.width : ℝ) < |x - (t : ℝ)|) :
    ∃ o, compareStep c t = some o := by
  cases c with
  | rat q => exact ⟨_, rfl⟩
  | root p I =>
    simp only [compareStep]
    split_ifs with hl hu hp
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · have htl : (I.lower : ℝ) < t := by exact_mod_cast lt_of_not_ge hl
      have htu : (t : ℝ) < I.upper := by exact_mod_cast lt_of_not_ge hu
      have hb : |x - (t : ℝ)| ≤ (I.width : ℝ) := by
        rw [abs_le]
        simp only [QInterval.width, Rat.cast_sub]
        constructor <;> linarith [hx.2.1, hx.2.2]
      exact False.elim (not_lt_of_ge hb hw)

 theorem compareBracketRat_success_of_iterate (c : AlgCode) (t : ℚ) (n : ℕ)
    (hs : ∃ o, compareStep (c.iterate n) t = some o) :
    ∃ o, compareBracketRat t n c = some o := by
  induction n generalizing c with
  | zero => exact hs
  | succ n ih =>
    simp only [compareBracketRat]
    cases ho : compareStep c t with
    | some o => exact ⟨o, rfl⟩
    | none => exact ih c.refine (by rwa [iterate_succ_left] at hs)

 theorem compareBracketRat_terminates (c : AlgCode) (hv : c.valid) (t : ℚ) :
    ∃ n o, compareBracketRat t n c = some o := by
  obtain ⟨x, hx, _⟩ := validAlgBracket_denotes_unique c hv
  by_cases he : x = (t : ℝ)
  · obtain ⟨o, ho⟩ := compareStep_eq_success hx he
    exact ⟨0, o, ho⟩
  · have ha : 0 < |x - (t : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr he)
    obtain ⟨h, hh0, hh⟩ := exists_rat_btwn ha
    have hq : (0 : ℚ) < h := by exact_mod_cast hh0
    obtain ⟨n, hn⟩ := exists_halving_bound c.interval.width h hq
    have hw := (iterate_width c (valid_interval hv) n).trans hn
    have hwr : ((c.iterate n).interval.width : ℝ) < |x - (t : ℝ)| :=
      lt_of_le_of_lt (by exact_mod_cast hw) hh
    obtain ⟨o, ho⟩ := compareBracketRat_success_of_iterate c t n
      (compareStep_success_of_width (iterate_denotes hv hx n) hwr)
    exact ⟨n, o, ho⟩

 theorem positiveBracket_success_of_iterate (c : AlgCode) (n : ℕ)
    (hs : 0 < (c.iterate n).interval.lower) :
    ∃ d, positiveBracket n c = some d ∧ 0 < d.interval.lower := by
  induction n generalizing c with
  | zero => exact ⟨c, by simp [positiveBracket, iterate] at hs ⊢; exact hs, hs⟩
  | succ n ih =>
    simp only [positiveBracket]
    split_ifs with hc
    · exact ⟨c, rfl, hc⟩
    · exact ih c.refine (by rwa [iterate_succ_left] at hs)

 theorem positiveBracket_terminates (c : AlgCode) (hv : c.valid)
    {x : ℝ} (hx : c.denotes x) (hp : 0 < x) :
    ∃ n d, positiveBracket n c = some d ∧ 0 < d.interval.lower := by
  obtain ⟨h, hh0, hh⟩ := exists_rat_btwn hp
  have hq : (0 : ℚ) < h := by exact_mod_cast hh0
  obtain ⟨n, hn⟩ := exists_halving_bound c.interval.width h hq
  have hw := (iterate_width c (valid_interval hv) n).trans hn
  have hwr : ((c.iterate n).interval.width : ℝ) < x := lt_of_le_of_lt (by exact_mod_cast hw) hh
  have hc := denotes_contains (iterate_denotes hv hx n)
  have hl : (0 : ℝ) < (c.iterate n).interval.lower := by
    dsimp [QInterval.width] at hwr
    push_cast at hwr
    linarith [hc.2]
  obtain ⟨d, hd⟩ := positiveBracket_success_of_iterate c n (by exact_mod_cast hl)
  exact ⟨n, d, hd⟩

end AlgCode
end Cover
