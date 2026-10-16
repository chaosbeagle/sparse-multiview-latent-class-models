import Gen.Uniqueness

/-!
Common-permutation alignment component of Stegeman--Sidiropoulos (2007),
Linear Algebra and its Applications 420, 540--552, Section 3, equations (3.11)--(3.16).
Primary source: https://pure.rug.nl/ws/portalfiles/portal/190306816/On_Kruskal_s_uniqueness_condition_for_the_Candecomp_Parafac_decomposition.pdf
This module supplies proved linear-algebra/combinatorial components, not an unchecked
assumption that Kruskal uniqueness holds.
-/
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
noncomputable section
namespace Gen.KruskalAlignment

variable {Z O : Type*} [Fintype Z] [DecidableEq Z]

/-- Exact-k independence implies independence on every smaller selected column set. -/
theorem column_independent_of_card_le (A : O → Z → ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card Z) (hA : Gen.ColumnKruskalIndependent A k)
    (S : Finset Z) (hS : S.card ≤ k) :
    LinearIndependent ℝ (fun z : S => fun y => A y z.val) := by
  obtain ⟨T,hST,hT⟩ := Finset.exists_superset_card_eq hS hk
  have h := (hA T hT).comp (fun z : S => (⟨z.val,hST z.property⟩ : T))
    (fun a b h => Subtype.ext (congrArg (fun z : T => z.val) h))
  exact h

/-- Useful raw monotonicity for the independently developed permutation lemma. -/
theorem columnKruskalIndependent_mono (A : O → Z → ℝ) {j k : ℕ}
    (hk : k ≤ Fintype.card Z) (hjk : j ≤ k) (hA : Gen.ColumnKruskalIndependent A k) :
    Gen.ColumnKruskalIndependent A j := by
  intro S hS
  exact column_independent_of_card_le A hk hA S (hS ▸ hjk)

/-- A selected independent family yields a real row functional which kills S
and takes exactly value one on the distinguished column. -/
theorem exists_separating_row [Fintype O] (A : O → Z → ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card Z) (hA : Gen.ColumnKruskalIndependent A k)
    (S : Finset Z) (r : Z) (hr : r ∉ S) (hS : S.card < k) :
    ∃ v : O → ℝ, (∑ y, v y * A y r) = 1 ∧ ∀ z ∈ S, (∑ y, v y * A y z) = 0 := by
  let T := insert r S
  have hT : T.card ≤ k := by simp only [T, Finset.card_insert_of_notMem hr]; omega
  have hi := column_independent_of_card_le A hk hA T hT
  obtain ⟨L,hL⟩ := Gen.Uniqueness.exists_leftDual_of_linearIndependent
    (fun y (z : T) => A y z.val) hi
  let rt : T := ⟨r,Finset.mem_insert_self _ _⟩
  refine ⟨L rt, ?_, ?_⟩
  · simpa using hL rt rt
  · intro z hz
    let zt : T := ⟨z,Finset.mem_insert_of_mem hz⟩
    have he : rt ≠ zt := by
      intro h
      have hrz : r = z := congrArg Subtype.val h
      exact hr (hrz ▸ hz)
    simpa only [if_neg he] using hL rt zt

/-- A relation supported on at most k columns has zero coefficients. -/
theorem sparse_relation_zero (A : O → Z → ℝ) {k : ℕ}
    (hk : k ≤ Fintype.card Z) (hA : Gen.ColumnKruskalIndependent A k)
    (p : Z → ℝ) (hs : (Finset.univ.filter (fun z => p z ≠ 0)).card ≤ k)
    (hrel : ∀ y, ∑ z, p z * A y z = 0) : ∀ z, p z = 0 := by
  let S := Finset.univ.filter (fun z => p z ≠ 0)
  have hi := column_independent_of_card_le A hk hA S hs
  rw [Fintype.linearIndependent_iff] at hi
  have hsum : ∑ z : S, p z.val • (fun y => A y z.val) = 0 := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← Finset.sum_subtype S (fun z => Iff.rfl) (fun z => p z * A y z)]
    calc
      (∑ z ∈ S, p z * A y z) = ∑ z, p z * A y z := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro z _ hz
        have hz0 : p z = 0 := by simpa [S] using hz
        simp [hz0]
      _ = 0 := hrel y
  intro z
  by_cases hz : p z = 0
  · exact hz
  · exact hi (fun z : S => p z.val) hsum ⟨z,by simp [S,hz]⟩

/-- Construct the two annihilation sets from distinct permutations. This is the
finite covering construction immediately preceding equation (3.16). -/
theorem permutation_cover (a b : Equiv.Perm Z) (hab : a ≠ b) {k : ℕ}
    (hk0 : 2 ≤ k) (hk : k ≤ Fintype.card Z) :
    ∃ (r : Z) (S T : Finset Z), r ∉ S ∧ r ∉ T ∧
      S.card = k - 1 ∧ T.card = Fintype.card Z - (k - 1) ∧
      ∀ z, a z ∈ S ∨ b z ∈ T := by
  have hex : ∃ s, a s ≠ b s := by
    by_contra h
    push Not at h
    exact hab (Equiv.ext h)
  obtain ⟨s,hs⟩ := hex
  let t := b.symm (a s)
  have ht : t ≠ s := by
    intro h
    have h' := congrArg b h
    simp only [t, b.apply_symm_apply] at h'
    exact hs h'
  have hAv : ((Finset.univ.erase s).erase t).card = Fintype.card Z - 2 := by
    rw [Finset.card_erase_of_mem (by simp [ht]), Finset.card_erase_of_mem (Finset.mem_univ s)]
    simp only [Finset.card_univ]
    omega
  obtain ⟨U,hU,hUc⟩ := Finset.exists_subset_card_eq
    (show k - 2 ≤ ((Finset.univ.erase s).erase t).card by rw [hAv]; omega)
  have htU : t ∉ U := fun h => (Finset.mem_erase.mp (hU h)).1 rfl
  have hsU : s ∉ U := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (hU h)).2).1 rfl
  let V := insert t U
  have hsV : s ∉ V := by simp [V,Ne.symm ht,hsU]
  have htV : t ∈ V := Finset.mem_insert_self _ _
  have hVc : V.card = k - 1 := by simp only [V,Finset.card_insert_of_notMem htU,hUc]; omega
  refine ⟨a s,V.image a,Vᶜ.image b,?_,?_,?_,?_,?_⟩
  · rintro h
    obtain ⟨z,hz,hz'⟩ := Finset.mem_image.mp h
    exact hsV (a.injective hz' ▸ hz)
  · rintro h
    obtain ⟨z,hz,hz'⟩ := Finset.mem_image.mp h
    have hzt : z = t := b.injective (hz'.trans (b.apply_symm_apply (a s)).symm)
    subst z
    exact (Finset.mem_compl.mp hz) htV
  · simpa only [Finset.card_image_of_injective _ a.injective] using hVc
  · rw [Finset.card_image_of_injective _ b.injective,Finset.card_compl,hVc]
  · intro z
    by_cases hz : z ∈ V
    · exact Or.inl (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨z,Finset.mem_compl.mpr hz,rfl⟩)

section Tensor
variable {X Y T : Type*} [Fintype X] [Fintype Y] [Fintype T]

def tensor (A : X → Z → ℝ) (B : Y → Z → ℝ) (C : T → Z → ℝ)
    (x : X) (y : Y) (t : T) : ℝ := ∑ z, A x z * B y z * C t z

def rowDot (A : X → Z → ℝ) (v : X → ℝ) (z : Z) : ℝ := ∑ x, v x * A x z

lemma rowDot_scaled (A A' : X → Z → ℝ) (v : X → ℝ)
    (q : Equiv.Perm Z) (d : Z → ℝ) (h : ∀ x z, A' x z = d z * A x (q z)) (z : Z) :
    rowDot A' v z = d z * rowDot A v (q z) := by
  simp only [rowDot, h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Contracting the equality of full tensors by two arbitrary real rows. -/
lemma double_contract (A : X → Z → ℝ) (B : Y → Z → ℝ) (C : T → Z → ℝ)
    (v : X → ℝ) (w : Y → ℝ) (t : T) :
    (∑ z, rowDot A v z * rowDot B w z * C t z) =
      ∑ x, ∑ y, v x * w y * tensor A B C x y t := by
  simp only [rowDot, tensor, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma tensor_eq_double_contract (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ)
    (C C' : T → Z → ℝ) (heq : ∀ x y t, tensor A B C x y t = tensor A' B' C' x y t)
    (v : X → ℝ) (w : Y → ℝ) (t : T) :
    (∑ z, rowDot A v z * rowDot B w z * C t z) =
      ∑ z, rowDot A' v z * rowDot B' w z * C' t z := by
  rw [double_contract, double_contract]
  simp_rw [heq]

/-- The key equation (3.16) contradiction: separate column matches of the first
two factors must use the same permutation under the genuine Kruskal condition. -/
theorem first_two_permutations_equal (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ)
    (C C' : T → Z → ℝ) {kA kB kC : ℕ}
    (hAk : kA ≤ Fintype.card Z) (hBk : kB ≤ Fintype.card Z) (hCk : kC ≤ Fintype.card Z)
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hC : Gen.ColumnKruskalIndependent C kC)
    (hK : 2 * Fintype.card Z + 2 ≤ kA + kB + kC)
    (qa qb : Equiv.Perm Z) (da db : Z → ℝ)
    (hAm : ∀ x z, A' x z = da z * A x (qa z))
    (hBm : ∀ y z, B' y z = db z * B y (qb z))
    (heq : ∀ x y t, tensor A B C x y t = tensor A' B' C' x y t) : qa = qb := by
  by_contra hneq
  have hA2 : 2 ≤ kA := by omega
  obtain ⟨r,S,U,hrS,hrU,hSc,hUc,hcover⟩ := permutation_cover qa qb hneq hA2 hAk
  obtain ⟨v,hvr,hvS⟩ := exists_separating_row A hAk hA S r hrS (by omega)
  obtain ⟨w,hwr,hwU⟩ := exists_separating_row B hBk hB U r hrU (by omega)
  let p : Z → ℝ := fun z => rowDot A v z * rowDot B w z
  have hpr : p r = 1 := by simp only [p,rowDot,hvr,hwr,mul_one]
  have hright (z : Z) : rowDot A' v z * rowDot B' w z = 0 := by
    rw [rowDot_scaled A A' v qa da hAm, rowDot_scaled B B' w qb db hBm]
    rcases hcover z with hz | hz
    · have h := hvS (qa z) hz
      simp only [rowDot] at *
      rw [h]
      ring
    · have h := hwU (qb z) hz
      simp only [rowDot] at *
      rw [h]
      ring
  have hrel (t : T) : ∑ z, p z * C t z = 0 := by
    have h := tensor_eq_double_contract A A' B B' C C' heq v w t
    simpa only [p,hright,zero_mul,Finset.sum_const_zero] using h
  have hsupport : (Finset.univ.filter (fun z => p z ≠ 0)).card ≤ kC := by
    have hsub : Finset.univ.filter (fun z => p z ≠ 0) ⊆ Sᶜ := by
      intro z hz
      apply Finset.mem_compl.mpr
      intro hzS
      have hh := (Finset.mem_filter.mp hz).2
      apply hh
      simp only [p,rowDot,hvS z hzS,zero_mul]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_compl,hSc] at hc
    omega
  have hz := sparse_relation_zero C hCk hC p hsupport hrel r
  linarith
/-- Sufficient joint k-ranks give rows which isolate any one matched rank-one pair. -/
theorem exists_pair_isolating_rows (A : X → Z → ℝ) (B : Y → Z → ℝ)
    {kA kB : ℕ} (hA1 : 1 ≤ kA) (hAk : kA ≤ Fintype.card Z) (hBk : kB ≤ Fintype.card Z)
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hK : Fintype.card Z + 1 ≤ kA + kB) (r : Z) :
    ∃ (v : X → ℝ) (w : Y → ℝ), ∀ z,
      rowDot A v z * rowDot B w z = if z = r then 1 else 0 := by
  have hc : (Finset.univ.erase r).card = Fintype.card Z - 1 := by simp
  obtain ⟨S,hS,hSc⟩ := Finset.exists_subset_card_eq
    (show kA - 1 ≤ (Finset.univ.erase r).card by rw [hc]; omega)
  let U := (Finset.univ.erase r) \ S
  have hrS : r ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
  have hrU : r ∉ U := fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl
  have hUc : U.card = (Fintype.card Z - 1) - (kA - 1) := by
    dsimp only [U]
    rw [Finset.card_sdiff_of_subset hS,hc,hSc]
  obtain ⟨v,hvr,hvS⟩ := exists_separating_row A hAk hA S r hrS (by omega)
  obtain ⟨w,hwr,hwU⟩ := exists_separating_row B hBk hB U r hrU (by omega)
  refine ⟨v,w,?_⟩
  intro z
  by_cases hz : z = r
  · subst z
    simp only [rowDot,hvr,hwr,ite_true,mul_one]
  · rw [if_neg hz]
    by_cases hzS : z ∈ S
    · simp only [rowDot,hvS z hzS,zero_mul]
    · have hzU : z ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hz,Finset.mem_univ _⟩,hzS⟩
      simp only [rowDot,hwU z hzU,mul_zero]

lemma tensor_swap_second_third (A : X → Z → ℝ) (B : Y → Z → ℝ) (C : T → Z → ℝ)
    (x : X) (y : Y) (t : T) : tensor A C B x t y = tensor A B C x y t := by
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Once the permutation agrees, exact pair isolation forces the product of scales
on every component to be one. This is the normalization-free content of Lemma 3.5. -/
theorem same_permutation_scale_product (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ)
    (C C' : T → Z → ℝ) {kA kB kC : ℕ}
    (hAk : kA ≤ Fintype.card Z) (hBk : kB ≤ Fintype.card Z) (hCk : kC ≤ Fintype.card Z)
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hC : Gen.ColumnKruskalIndependent C kC)
    (hK : 2 * Fintype.card Z + 2 ≤ kA + kB + kC)
    (q : Equiv.Perm Z) (da db dc : Z → ℝ)
    (hAm : ∀ x z, A' x z = da z * A x (q z))
    (hBm : ∀ y z, B' y z = db z * B y (q z))
    (hCm : ∀ t z, C' t z = dc z * C t (q z))
    (heq : ∀ x y t, tensor A B C x y t = tensor A' B' C' x y t) :
    ∀ z, da z * db z * dc z = 1 := by
  intro z0
  obtain ⟨v,w,hpair⟩ := exists_pair_isolating_rows A B (by omega) hAk hBk hA hB (by omega) (q z0)
  have hrel (t : T) : C t (q z0) = (da z0 * db z0 * dc z0) * C t (q z0) := by
    have h := tensor_eq_double_contract A A' B B' C C' heq v w t
    have hleft : (∑ z, rowDot A v z * rowDot B w z * C t z) = C t (q z0) := by
      simp_rw [hpair]
      simp
    have hterm (z : Z) : rowDot A' v z * rowDot B' w z * C' t z =
        if z = z0 then (da z0 * db z0 * dc z0) * C t (q z0) else 0 := by
      rw [rowDot_scaled A A' v q da hAm, rowDot_scaled B B' w q db hBm,hCm]
      calc
        _ = (da z * db z * dc z) * (rowDot A v (q z) * rowDot B w (q z)) * C t (q z) := by ring
        _ = _ := by
          rw [hpair]
          by_cases hz : z = z0 <;> simp [q.injective.eq_iff,hz]
    rw [hleft] at h
    simpa only [hterm,Finset.sum_ite_eq',Finset.mem_univ,if_true] using h
  have hi := column_independent_of_card_le C hCk hC {q z0} (by simp; omega)
  have hnonzero : (fun t => C t (q z0)) ≠ 0 := LinearIndependent.ne_zero
    (⟨q z0,Finset.mem_singleton_self _⟩ : ({q z0} : Finset Z)) hi
  have hex : ∃ t, C t (q z0) ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hnonzero
    funext t
    exact hh t
  obtain ⟨t,ht⟩ := hex
  apply mul_right_cancel₀ ht
  simpa only [one_mul] using (hrel t).symm

/-- Full common-permutation and reciprocal-scaling conclusion from separate
column matches, using only the reference Kruskal conditions and actual tensor equality.
The comparison arrays are otherwise unrestricted. -/
theorem common_permutation_alignment (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ)
    (C C' : T → Z → ℝ) {kA kB kC : ℕ}
    (hAk : kA ≤ Fintype.card Z) (hBk : kB ≤ Fintype.card Z) (hCk : kC ≤ Fintype.card Z)
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hC : Gen.ColumnKruskalIndependent C kC)
    (hK : 2 * Fintype.card Z + 2 ≤ kA + kB + kC)
    (qa qb qc : Equiv.Perm Z) (da db dc : Z → ℝ)
    (hAm : ∀ x z, A' x z = da z * A x (qa z))
    (hBm : ∀ y z, B' y z = db z * B y (qb z))
    (hCm : ∀ t z, C' t z = dc z * C t (qc z))
    (heq : ∀ x y t, tensor A B C x y t = tensor A' B' C' x y t) :
    qa = qb ∧ qb = qc ∧ ∀ z, da z * db z * dc z = 1 := by
  have hab := first_two_permutations_equal A A' B B' C C' hAk hBk hCk hA hB hC hK qa qb da db hAm hBm heq
  have hac := first_two_permutations_equal A A' C C' B B' hAk hCk hBk hA hC hB
    (by omega) qa qc da dc hAm hCm
    (fun x t y => (tensor_swap_second_third A B C x y t).trans
      ((heq x y t).trans (tensor_swap_second_third A' B' C' x y t).symm))
  refine ⟨hab,hab.symm.trans hac,?_⟩
  apply same_permutation_scale_product A A' B B' C C' hAk hBk hCk hA hB hC hK qa da db dc hAm
  · intro y z
    simpa only [hab] using hBm y z
  · intro t z
    simpa only [hac] using hCm t z
  · exact heq

end Tensor

end Gen.KruskalAlignment
