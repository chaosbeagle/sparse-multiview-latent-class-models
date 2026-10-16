import Cover.Interval

namespace Cover.QInterval

def mag (I : QInterval) : ℚ := Max.max |I.lower| |I.upper|

theorem mag_nonneg (I : QInterval) : 0 ≤ I.mag := (abs_nonneg _).trans (le_max_left _ _)
theorem abs_lower_le_mag (I : QInterval) : |I.lower| ≤ I.mag := le_max_left _ _
theorem abs_upper_le_mag (I : QInterval) : |I.upper| ≤ I.mag := le_max_right _ _

theorem abs_le_mag_of_between {I : QInterval} {x : ℚ} (hx : I.lower ≤ x ∧ x ≤ I.upper) :
    |x| ≤ I.mag := by
  apply abs_le.mpr
  constructor
  · have h := (abs_le.mp I.abs_lower_le_mag).1; linarith [hx.1]
  · exact hx.2.trans (abs_le.mp I.abs_upper_le_mag).2

theorem abs_sub_le_width {I : QInterval} {x y : ℚ}
    (hx : I.lower ≤ x ∧ x ≤ I.upper) (hy : I.lower ≤ y ∧ y ≤ I.upper) :
    |x-y| ≤ I.width := by
  apply abs_le.mpr
  dsimp [width]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

private theorem four_choice (f : ℚ → ℚ → ℚ) (hf : ∀ a b, f a b = a ∨ f a b = b)
    (a b c d : ℚ) : f (f a b) (f c d) = a ∨ f (f a b) (f c d) = b ∨
    f (f a b) (f c d) = c ∨ f (f a b) (f c d) = d := by
  rcases hf (f a b) (f c d) with h | h
  · rw [h]; rcases hf a b with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rw [h]; rcases hf c d with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

theorem mul_lower_choice (I J : QInterval) : ∃ a b : ℚ,
    (a = I.lower ∨ a = I.upper) ∧ (b = J.lower ∨ b = J.upper) ∧ (mul I J).lower = a*b := by
  rcases four_choice Min.min min_choice (I.lower*J.lower) (I.lower*J.upper)
    (I.upper*J.lower) (I.upper*J.upper) with h | h | h | h
  · exact ⟨_, _, Or.inl rfl, Or.inl rfl, h⟩
  · exact ⟨_, _, Or.inl rfl, Or.inr rfl, h⟩
  · exact ⟨_, _, Or.inr rfl, Or.inl rfl, h⟩
  · exact ⟨_, _, Or.inr rfl, Or.inr rfl, h⟩

theorem mul_upper_choice (I J : QInterval) : ∃ a b : ℚ,
    (a = I.lower ∨ a = I.upper) ∧ (b = J.lower ∨ b = J.upper) ∧ (mul I J).upper = a*b := by
  rcases four_choice Max.max max_choice (I.lower*J.lower) (I.lower*J.upper)
    (I.upper*J.lower) (I.upper*J.upper) with h | h | h | h
  · exact ⟨_, _, Or.inl rfl, Or.inl rfl, h⟩
  · exact ⟨_, _, Or.inl rfl, Or.inr rfl, h⟩
  · exact ⟨_, _, Or.inr rfl, Or.inl rfl, h⟩
  · exact ⟨_, _, Or.inr rfl, Or.inr rfl, h⟩

theorem endpoint_between {I : QInterval} {x : ℚ} (hI : I.valid)
    (hx : x = I.lower ∨ x = I.upper) : I.lower ≤ x ∧ x ≤ I.upper := by
  rcases hx with rfl | rfl
  · exact ⟨le_refl _, hI⟩
  · exact ⟨hI, le_refl _⟩

theorem abs_endpoint_le_mag {I : QInterval} {x : ℚ}
    (hx : x = I.lower ∨ x = I.upper) : |x| ≤ I.mag := by
  rcases hx with rfl | rfl
  · exact I.abs_lower_le_mag
  · exact I.abs_upper_le_mag

theorem mul_width_le {I J : QInterval} (hI : I.valid) (hJ : J.valid) :
    (mul I J).width ≤ I.mag * J.width + J.mag * I.width := by
  obtain ⟨a,b,ha,hb,hl⟩ := mul_lower_choice I J
  obtain ⟨c,d,hc,hd,hu⟩ := mul_upper_choice I J
  have hbd := abs_sub_le_width (endpoint_between hJ hd) (endpoint_between hJ hb)
  have hca := abs_sub_le_width (endpoint_between hI hc) (endpoint_between hI ha)
  calc
    (mul I J).width = c*d-a*b := by simp only [width, hl, hu]
    _ ≤ |c*d-a*b| := le_abs_self _
    _ = |c*(d-b)+b*(c-a)| := by congr 1; ring
    _ ≤ |c*(d-b)| + |b*(c-a)| := abs_add_le _ _
    _ = |c| * |d-b| + |b| * |c-a| := by rw [abs_mul, abs_mul]
    _ ≤ I.mag*J.width + J.mag*I.width := add_le_add
      (mul_le_mul (abs_endpoint_le_mag hc) hbd (abs_nonneg _) I.mag_nonneg)
      (mul_le_mul (abs_endpoint_le_mag hb) hca (abs_nonneg _) J.mag_nonneg)

@[simp] theorem singleton_mag (q : ℚ) : (singleton q).mag = |q| := max_self _
@[simp] theorem neg_mag (I : QInterval) : (neg I).mag = I.mag := by
  simp only [mag, neg, abs_neg]; exact max_comm _ _

theorem add_mag_le (I J : QInterval) : (add I J).mag ≤ I.mag + J.mag := by
  apply max_le
  · exact (abs_add_le _ _).trans (add_le_add I.abs_lower_le_mag J.abs_lower_le_mag)
  · exact (abs_add_le _ _).trans (add_le_add I.abs_upper_le_mag J.abs_upper_le_mag)

theorem mul_mag_le (I J : QInterval) : (mul I J).mag ≤ I.mag * J.mag := by
  obtain ⟨a,b,ha,hb,hl⟩ := mul_lower_choice I J
  obtain ⟨c,d,hc,hd,hu⟩ := mul_upper_choice I J
  apply max_le
  · rw [hl, abs_mul]
    exact mul_le_mul (abs_endpoint_le_mag ha) (abs_endpoint_le_mag hb) (abs_nonneg _) I.mag_nonneg
  · rw [hu, abs_mul]
    exact mul_le_mul (abs_endpoint_le_mag hc) (abs_endpoint_le_mag hd) (abs_nonneg _) I.mag_nonneg

theorem min_width_le (I J : QInterval) : (min I J).width ≤ Max.max I.width J.width := by
  rcases min_choice I.lower J.lower with h | h
  · change Min.min I.upper J.upper - Min.min I.lower J.lower ≤ _
    rw [h]
    exact (sub_le_sub_right (min_le_left _ _) _).trans (le_max_left _ _)
  · change Min.min I.upper J.upper - Min.min I.lower J.lower ≤ _
    rw [h]
    exact (sub_le_sub_right (min_le_right _ _) _).trans (le_max_right _ _)

theorem max_width_le (I J : QInterval) : (max I J).width ≤ Max.max I.width J.width := by
  rcases max_choice I.upper J.upper with h | h
  · change Max.max I.upper J.upper - Max.max I.lower J.lower ≤ _
    rw [h]
    exact (sub_le_sub_left (le_max_left _ _) _).trans (le_max_left _ _)
  · change Max.max I.upper J.upper - Max.max I.lower J.lower ≤ _
    rw [h]
    exact (sub_le_sub_left (le_max_right _ _) _).trans (le_max_right _ _)

end Cover.QInterval
