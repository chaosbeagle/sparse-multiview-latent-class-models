import Cover.ScalarPositivity

namespace Cover.Literal
open ScalarExpr
variable {g s : Nat} {w σ : QInterval}

lemma weight_hasLower (hw : w.valid) : HasLower s w σ .weight w.lower :=
  ⟨w, rfl, hw, le_rfl⟩
lemma sigma_hasLower (hσ : σ.valid) : HasLower s w σ .sigma σ.lower :=
  ⟨σ, rfl, hσ, le_rfl⟩

lemma sigma_inverse_coarse (hσ : σ.valid) (hσ0 : 0 < σ.lower)
    (hσu : σ.upper ≤ 5/4) : HasLower s w σ (.inv .sigma) (4/5) := by
  have hup := hσ0.trans_le hσ
  refine ⟨σ.invPos, by simp [ScalarExpr.bounds, hσ0], QInterval.invPos_valid hσ0 hσ, ?_⟩
  change (4/5 : ℚ) ≤ σ.upper⁻¹
  calc
    4/5 = (5/4 : ℚ)⁻¹ := by norm_num
    _ ≤ σ.upper⁻¹ := (inv_le_inv₀ (by norm_num : (0 : ℚ) < 5/4) hup).mpr hσu

lemma a_has_positive_lower (n : Fin g → Nat) (i : Fin g)
    (hw : w.valid) (hσ : σ.valid) (hw0 : 0 < w.lower) (hσ0 : 0 < σ.lower) :
    ∃ l : ℚ, 0 < l ∧ HasLower s w σ (a n i) l := by
  have hwp := weight_hasLower (s := s) (σ := σ) hw
  have hsp := (sigma_hasLower (s := s) (w := w) hσ).pow hσ0.le 2
  have hd := hwp.mul hsp hw0.le (sq_nonneg σ.lower)
  obtain ⟨l, hl, hi⟩ := hd.inv_positive (mul_pos hw0 (sq_pos_of_pos hσ0))
  have hn : HasLower s w σ (.sqrt (.rat (n i))) 0 :=
    ((HasLower.rat (s := s) (w := w) (σ := σ) (n i)).weaken (Nat.cast_nonneg _)).sqrt_nonneg
  have hnum := (HasLower.rat (s := s) (w := w) (σ := σ) 1).add hn
  refine ⟨l, hl, ?_⟩
  simpa only [a, add_zero, one_mul] using hnum.mul hi (by norm_num) hl.le

lemma a_has_nonnegative_lower (n : Fin g → Nat) (i : Fin g)
    (hw : w.valid) (hσ : σ.valid) (hw0 : 0 < w.lower) (hσ0 : 0 < σ.lower) :
    HasLower s w σ (a n i) 0 := by
  obtain ⟨l, hl, hi⟩ := a_has_positive_lower (s := s) n i hw hσ hw0 hσ0
  exact hi.weaken hl.le

lemma b_lower_64_125 (n : Fin g → Nat) (e : List (Fin g))
    (hw : w.valid) (hσ : σ.valid) (hw0 : 0 < w.lower) (hσ0 : 0 < σ.lower)
    (hσu : σ.upper ≤ 5/4) : HasLower s w σ (b n e) (64/125) := by
  have hinv := sigma_inverse_coarse (s := s) (w := w) hσ hσ0 hσu
  have hp := hinv.pow (by norm_num : (0 : ℚ) ≤ 4/5) 3
  have hsum : HasLower s w σ (.sum (e.map (a n))) 0 := by
    apply HasLower.sum
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact a_has_nonnegative_lower n i hw hσ hw0 hσ0
  have hmul := hinv.mul hsum (by norm_num) (by norm_num)
  have hadd := hp.add hmul
  norm_num only at hadd
  exact hadd

lemma edgeB_lower_half (n : Fin g → Nat) (e : List (Fin g))
    (hw : w.valid) (hσ : σ.valid) (hw0 : 0 < w.lower) (hσ0 : 0 < σ.lower)
    (hσu : σ.upper ≤ 5/4) : HasLower s w σ (edgeB n e) (1/2) := by
  have hb := (b_lower_64_125 (s := s) n e hw hσ hw0 hσ0 hσu).pow (by norm_num) 2
  have hsum : HasLower s w σ (.sum (e.map fun i => (a n i).pow 2)) 0 := by
    apply HasLower.sum
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      (a_has_nonnegative_lower (s := s) n i hw hσ hw0 hσ0).pow (le_refl 0) 2
  have hh := (hb.add hsum).weaken (by norm_num : (1/4 : ℚ) ≤ (64/125)^2 + 0)
  exact hh.sqrt_half

lemma B_lower_half (n : Fin g → Nat) {edges : List (List (Fin g))} (he : edges ≠ [])
    (hw : w.valid) (hσ : σ.valid) (hw0 : 0 < w.lower) (hσ0 : 0 < σ.lower)
    (hσu : σ.upper ≤ 5/4) : HasLower s w σ (B n edges) (1/2) := by
  apply HasLower.maxList
  · simpa using he
  · intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact edgeB_lower_half n e hw hσ hw0 hσ0 hσu

lemma M_lower_twelve (n : Fin g → Nat) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ []) : HasLower s w σ (M n edges) 12 := by
  have hm : (1 : ℚ) ≤ m n edges := by exact_mod_cast m_pos n hn he
  have hs := ((HasLower.rat (s := s) (w := w) (σ := σ) (m n edges)).weaken hm).sqrt_one
  simpa only [M, mul_one] using (HasLower.rat (s := s) (w := w) (σ := σ) 12).mul hs (by norm_num) (by norm_num)

/-- Every actual scalar formula is executable at every natural precision, including zero.
The hypotheses are exactly the prepared positive margin brackets and their proved coarse
sigma upper bound; no positive denominator is assumed for a derived expression. -/
theorem every_stage_denominators_positive (n : Fin g → Nat) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ [])
    (hw : w.valid) (hσ : σ.valid) (hw0 : 0 < w.lower) (hσ0 : 0 < σ.lower)
    (hσu : σ.upper ≤ 5/4) :
    HasLower s w σ (B n edges) (1/2) ∧
    HasLower s w σ (M n edges) 12 ∧
    (∃ l : ℚ, 0 < l ∧ HasLower s w σ (kappa n edges) l) ∧
    (∃ l : ℚ, 0 < l ∧ HasLower s w σ (R n edges) l) := by
  have hB := B_lower_half (s := s) n he hw hσ hw0 hσ0 hσu
  have hM := M_lower_twelve (s := s) (w := w) (σ := σ) n hn he
  obtain ⟨k, hk, hκ⟩ := hB.inv_positive (by norm_num)
  obtain ⟨m, hm, hMi⟩ := hM.inv_positive (by norm_num)
  have hp := hκ.mul hMi hk.le hm.le
  have hR := (HasLower.rat (s := s) (w := w) (σ := σ) 1).min hp
  exact ⟨hB, hM, ⟨k,hk,hκ⟩, ⟨Min.min 1 (k*m), lt_min (by norm_num) (mul_pos hk hm), hR⟩⟩

/-- The mandated mesh, containment, and σ₀ ≤ 1 imply the coarse bound even at s=0. -/
theorem prepared_sigma_upper_le {σ₀ : ℝ} (hc : σ.contains σ₀) (hσ₀ : σ₀ ≤ 1)
    (hwid : σ.width ≤ DyadicSqrt.mesh s) : σ.upper ≤ 5/4 := by
  have hm := DyadicSqrt.mesh_le_quarter s
  have hr0 : (σ.width : ℝ) ≤ ((1/4 : ℚ) : ℝ) := Rat.cast_le.mpr (hwid.trans hm)
  have hr : (σ.width : ℝ) ≤ (1 : ℝ)/4 := by simpa using hr0
  have he : (σ.width : ℝ) = (σ.upper : ℝ) - σ.lower := by simp [QInterval.width]
  have hl := hc.1
  have hu : (σ.upper : ℝ) ≤ (5 : ℝ)/4 := by linarith
  have hu0 : (σ.upper : ℝ) ≤ ((5/4 : ℚ) : ℝ) := by simpa using hu
  exact Rat.cast_le.mp hu0

/-- The exact finite list of every named scalar formula used by COVER. -/
def constantFamily (n : Fin g → Nat) (edges : List (List (Fin g))) (c r : Nat) : List ScalarExpr :=
  (List.finRange g).map (a n) ++ edges.map (b n) ++
    [B n edges, kappa n edges, .rat (m n edges), M n edges, R n edges, D c r g]

lemma hasLower_isSome {p : ScalarExpr} {l : ℚ} (h : HasLower s w σ p l) :
    (p.bounds s w σ).isSome = true := by
  obtain ⟨I, hi, _⟩ := h
  simp [hi]

/-- No denominator-error/radicand-error branch occurs in any literal scalar formula. -/
theorem literal_all_constants_defined (n : Fin g → Nat) (hn : ∀ i, 0 < n i)
    {edges : List (List (Fin g))} (he : edges ≠ []) (c r : Nat)
    (hw : w.valid) (hσ : σ.valid) (hw0 : 0 < w.lower) (hσ0 : 0 < σ.lower)
    {σ₀ : ℝ} (hc : σ.contains σ₀) (hσ₀ : σ₀ ≤ 1)
    (hwid : σ.width ≤ DyadicSqrt.mesh s) :
    ∀ p ∈ constantFamily n edges c r, (p.bounds s w σ).isSome = true := by
  have hσu := prepared_sigma_upper_le hc hσ₀ hwid
  have hs := every_stage_denominators_positive (s := s) n hn he hw hσ hw0 hσ0 hσu
  intro p hp
  simp only [constantFamily, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with (⟨i, hi, rfl⟩ | ⟨e, he, rfl⟩) | hp
  · exact hasLower_isSome (a_has_nonnegative_lower n i hw hσ hw0 hσ0)
  · exact hasLower_isSome (b_lower_64_125 n e hw hσ hw0 hσ0 hσu)
  · rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hasLower_isSome hs.1
    · obtain ⟨l, hl, hh⟩ := hs.2.2.1; exact hasLower_isSome hh
    · rfl
    · exact hasLower_isSome hs.2.1
    · obtain ⟨l, hl, hh⟩ := hs.2.2.2; exact hasLower_isSome hh
    · apply hasLower_isSome
      apply HasLower.sqrt_nonneg
      exact (HasLower.rat _).weaken (by positivity)

end Cover.Literal
