import Gen.Graph
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators Classical
noncomputable section
namespace Gen.KruskalPermutation

/-- The finite incidence-count step in Stegeman--Sidiropoulos (2007), Lemma 4.2.
    Counts are real only to avoid truncated subtraction; all summands are 0 or 1. -/
theorem incidence_count_descent {I Z : Type*} [Fintype I] [Fintype Z]
    (PA PB : I → Z → Prop) (pa pb : Z → Prop)
    (hI : 2 ≤ Fintype.card I)
    (hA : ∀ z, (∑ i, if PA i z then (1:ℝ) else 0) ≤
      1 + (Fintype.card I - 1 : ℝ) * (if pa z then 1 else 0))
    (hB : ∀ z, (∑ i, if PB i z then (1:ℝ) else 0) =
      1 + (Fintype.card I - 1 : ℝ) * (if pb z then 1 else 0))
    (hAB : ∀ i, (∑ z, if PB i z then (1:ℝ) else 0) ≤
      ∑ z, if PA i z then (1:ℝ) else 0) :
    (∑ z, if pb z then (1:ℝ) else 0) ≤ ∑ z, if pa z then (1:ℝ) else 0 := by
  have ha := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hA z)
  have hb := Finset.sum_congr (s₁ := Finset.univ) rfl (fun z _ => hB z)
  have hab := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hAB i)
  rw [Finset.sum_comm] at hab
  rw [Finset.sum_comm (f := fun i z => if PA i z then (1:ℝ) else 0)] at hab
  rw [hb] at hab
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Finset.mul_sum] at ha hab
  have hn : (2:ℝ) ≤ Fintype.card I := by exact_mod_cast hI
  nlinarith

variable {Z V : Type*} [Fintype Z] [AddCommGroup V] [Module ℝ V]

/-- All column spans and counts refer to the actual, possibly repeated or zero columns. -/
def totalSpan (B : Z → V) : Submodule ℝ V := Submodule.span ℝ (Set.range B)
def columnSet (B : Z → V) (S : Submodule ℝ V) : Finset Z :=
  Finset.univ.filter (fun z => B z ∈ S)
def count (B : Z → V) (S : Submodule ℝ V) : ℕ := (columnSet B S).card

def ColumnFlat (B : Z → V) (S : Submodule ℝ V) : Prop :=
  S = Submodule.span ℝ (B '' {z | B z ∈ S})

@[simp] lemma mem_columnSet (B : Z → V) (S : Submodule ℝ V) (z : Z) :
    z ∈ columnSet B S ↔ B z ∈ S := by simp [columnSet]

lemma count_eq_sum (B : Z → V) (S : Submodule ℝ V) :
    (count B S : ℝ) = ∑ z, if B z ∈ S then (1:ℝ) else 0 := by
  simp [count, columnSet, Finset.sum_boole]

lemma flat_le_total {B : Z → V} {S : Submodule ℝ V} (hS : ColumnFlat B S) :
    S ≤ totalSpan B := by
  rw [hS]
  exact Submodule.span_mono (Set.image_subset_range B _)

lemma total_is_flat (B : Z → V) : ColumnFlat B (totalSpan B) := by
  unfold ColumnFlat totalSpan
  congr 1
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, Submodule.subset_span ⟨z, rfl⟩, rfl⟩
  · rintro ⟨z, _, rfl⟩
    exact ⟨z, rfl⟩

lemma bot_is_flat (B : Z → V) : ColumnFlat B (⊥ : Submodule ℝ V) := by
  apply le_antisymm bot_le
  apply Submodule.span_le.mpr
  rintro v ⟨z, hz, rfl⟩
  exact hz

/-- All one-dimensional extensions obtained by adjoining a column outside S. -/
def extensions (B : Z → V) (S : Submodule ℝ V) : Finset (Submodule ℝ V) :=
  ((Finset.univ : Finset Z).filter (fun z => B z ∉ S)).image
    (fun z => S ⊔ Submodule.span ℝ {B z})

lemma mem_extensions {B : Z → V} {S T : Submodule ℝ V} :
    T ∈ extensions B S ↔ ∃ z, B z ∉ S ∧ S ⊔ Submodule.span ℝ {B z} = T := by
  simp [extensions]

lemma le_of_mem_extensions {B : Z → V} {S T : Submodule ℝ V}
    (hT : T ∈ extensions B S) : S ≤ T := by
  obtain ⟨z, _, rfl⟩ := mem_extensions.mp hT
  exact le_sup_left

lemma extension_le_total {B : Z → V} {S T : Submodule ℝ V} (hS : S ≤ totalSpan B)
    (hT : T ∈ extensions B S) : T ≤ totalSpan B := by
  obtain ⟨z, _, rfl⟩ := mem_extensions.mp hT
  exact sup_le hS (Submodule.span_le.mpr (by
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact Submodule.subset_span ⟨z, rfl⟩))

lemma extension_is_flat {B : Z → V} {S T : Submodule ℝ V}
    (hS : ColumnFlat B S) (hT : T ∈ extensions B S) : ColumnFlat B T := by
  obtain ⟨z, hz, rfl⟩ := mem_extensions.mp hT
  apply le_antisymm
  · apply sup_le
    · rw [hS]
      apply Submodule.span_mono
      rintro v ⟨i, hi, rfl⟩
      exact ⟨i, Submodule.mem_sup_left (hS ▸ hi), rfl⟩
    · apply Submodule.span_le.mpr
      intro v hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      apply Submodule.subset_span
      exact ⟨z, Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)), rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨i, hi, rfl⟩
    exact hi

variable [FiniteDimensional ℝ V]

lemma extension_finrank {B : Z → V} {S T : Submodule ℝ V}
    (hT : T ∈ extensions B S) : Module.finrank ℝ T = Module.finrank ℝ S + 1 := by
  obtain ⟨z, hz, rfl⟩ := mem_extensions.mp hT
  exact Submodule.finrank_sup_span_singleton hz

/-- Lemma 4.3: a vector outside S is in at most one distinct one-dimensional extension. -/
theorem extension_unique {B : Z → V} {S T U : Submodule ℝ V}
    (hT : T ∈ extensions B S) (hU : U ∈ extensions B S)
    {v : V} (hv : v ∉ S) (hvT : v ∈ T) (hvU : v ∈ U) : T = U := by
  have hspanT : S ⊔ Submodule.span ℝ {v} ≤ T :=
    sup_le (le_of_mem_extensions hT) (Submodule.span_le.mpr (by simpa))
  have hspanU : S ⊔ Submodule.span ℝ {v} ≤ U :=
    sup_le (le_of_mem_extensions hU) (Submodule.span_le.mpr (by simpa))
  have heT := Submodule.eq_of_le_of_finrank_eq hspanT
    ((Submodule.finrank_sup_span_singleton hv).trans (extension_finrank hT).symm)
  have heU := Submodule.eq_of_le_of_finrank_eq hspanU
    ((Submodule.finrank_sup_span_singleton hv).trans (extension_finrank hU).symm)
  exact heT.symm.trans heU

lemma extension_count_strict {B : Z → V} {S T : Submodule ℝ V}
    (hT : T ∈ extensions B S) : count B S < count B T := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    exact (mem_columnSet B T z).mpr (le_of_mem_extensions hT ((mem_columnSet B S z).mp hz))
  · intro heq
    obtain ⟨z, hz, hTz⟩ := mem_extensions.mp hT
    have hzT : z ∈ columnSet B T := by
      rw [mem_columnSet, ← hTz]
      exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
    rw [← heq] at hzT
    exact hz ((mem_columnSet B S z).mp hzT)


lemma exists_column_outside {B : Z → V} {S : Submodule ℝ V} (h : ¬ totalSpan B ≤ S) :
    ∃ z, B z ∉ S := by
  by_contra hn
  push_neg at hn
  apply h
  apply Submodule.span_le.mpr
  rintro v ⟨z, rfl⟩
  exact hn z

lemma extensions_card_two_le {B : Z → V} {S : Submodule ℝ V}
    (hS : S ≤ totalSpan B) (hne : S ≠ totalSpan B)
    (hcodim : Module.finrank ℝ S + 1 ≠ Module.finrank ℝ (totalSpan B)) :
    2 ≤ (extensions B S).card := by
  obtain ⟨z, hz⟩ := exists_column_outside (B := B) (S := S)
    (fun h => hne (le_antisymm hS h))
  let T := S ⊔ Submodule.span ℝ {B z}
  have hT : T ∈ extensions B S := mem_extensions.mpr ⟨z, hz, rfl⟩
  have hTne : T ≠ totalSpan B := by
    intro heq
    exact hcodim ((extension_finrank hT).symm.trans (congrArg (fun Q : Submodule ℝ V => Module.finrank ℝ Q) heq))
  obtain ⟨j, hj⟩ := exists_column_outside (B := B) (S := T)
    (fun h => hTne (le_antisymm (extension_le_total hS hT) h))
  have hjS : B j ∉ S := fun h => hj (le_of_mem_extensions hT h)
  let U := S ⊔ Submodule.span ℝ {B j}
  have hU : U ∈ extensions B S := mem_extensions.mpr ⟨j, hjS, rfl⟩
  have hTU : T ≠ U := by
    intro heq
    apply hj
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  exact Finset.one_lt_card.mpr ⟨T, hT, U, hU, hTU⟩

lemma extension_incidence_le_one {B : Z → V} {S : Submodule ℝ V} {v : V} (hv : v ∉ S) :
    ((Finset.univ : Finset (↑(extensions B S))).filter (fun T => v ∈ T.val)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro T hT U hU
  apply Subtype.ext
  exact extension_unique T.property U.property hv
    (Finset.mem_filter.mp hT).2 (Finset.mem_filter.mp hU).2

lemma column_extension_incidence_eq_one {B : Z → V} {S : Submodule ℝ V} {z : Z}
    (hz : B z ∉ S) :
    ((Finset.univ : Finset (↑(extensions B S))).filter (fun T => B z ∈ T.val)).card = 1 := by
  apply Nat.le_antisymm (extension_incidence_le_one hz)
  apply Finset.one_le_card.mpr
  refine ⟨⟨S ⊔ Submodule.span ℝ {B z}, mem_extensions.mpr ⟨z, hz, rfl⟩⟩, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))⟩

/-- The descent from all one-dimensional extensions to S, with all incidences proved. -/
theorem extension_count_descent (A B : Z → V) (S : Submodule ℝ V)
    (hN : 2 ≤ (extensions B S).card)
    (hExt : ∀ T ∈ extensions B S, count B T ≤ count A T) : count B S ≤ count A S := by
  have hh := incidence_count_descent
    (I := ↑(extensions B S)) (Z := Z)
    (fun T z => A z ∈ T.val) (fun T z => B z ∈ T.val)
    (fun z => A z ∈ S) (fun z => B z ∈ S)
    (by simpa only [Fintype.card_coe] using hN)
  have hA : ∀ z, (∑ T : ↑(extensions B S), if A z ∈ T.val then (1:ℝ) else 0) ≤
      1 + (Fintype.card ↑(extensions B S) - 1 : ℝ) * (if A z ∈ S then 1 else 0) := by
    intro z
    by_cases hz : A z ∈ S
    · have ha : ∀ T : ↑(extensions B S), A z ∈ T.val :=
        fun T => le_of_mem_extensions T.property hz
      simp [ha, hz]
    · have hc := extension_incidence_le_one (B := B) hz
      simp only [hz, if_false, mul_zero, add_zero]
      simpa only [Finset.sum_boole] using (show
        (((Finset.univ : Finset ↑(extensions B S)).filter (fun T => A z ∈ T.val)).card : ℝ) ≤ 1
        by exact_mod_cast hc)
  have hB : ∀ z, (∑ T : ↑(extensions B S), if B z ∈ T.val then (1:ℝ) else 0) =
      1 + (Fintype.card ↑(extensions B S) - 1 : ℝ) * (if B z ∈ S then 1 else 0) := by
    intro z
    by_cases hz : B z ∈ S
    · have hb : ∀ T : ↑(extensions B S), B z ∈ T.val :=
        fun T => le_of_mem_extensions T.property hz
      simp [hb, hz]
    · have hc := column_extension_incidence_eq_one (B := B) hz
      simp only [hz, if_false, mul_zero, add_zero]
      simpa only [Finset.sum_boole] using (show
        (((Finset.univ : Finset ↑(extensions B S)).filter (fun T => B z ∈ T.val)).card : ℝ) = 1
        by exact_mod_cast hc)
  have hAB : ∀ T : ↑(extensions B S),
      (∑ z, if B z ∈ T.val then (1:ℝ) else 0) ≤ ∑ z, if A z ∈ T.val then (1:ℝ) else 0 := by
    intro T
    rw [← count_eq_sum, ← count_eq_sum]
    exact_mod_cast hExt T.val T.property
  have hr := hh hA hB hAB
  rw [← count_eq_sum, ← count_eq_sum] at hr
  exact_mod_cast hr

/-- Complete finite-flat counting induction. The only base input concerns codimension-one
    column flats; it will be derived from the actual restricted support comparison. -/
theorem all_flat_counts_of_hyperplane_counts (A B : Z → V)
    (hA : ∀ z, A z ∈ totalSpan B)
    (hBase : ∀ S : Submodule ℝ V, ColumnFlat B S →
      Module.finrank ℝ S + 1 = Module.finrank ℝ (totalSpan B) → count B S ≤ count A S) :
    ∀ S : Submodule ℝ V, ColumnFlat B S → count B S ≤ count A S := by
  intro S hS
  generalize hn : Fintype.card Z - count B S = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases heq : S = totalSpan B
    · subst S
      have hB : ∀ z, B z ∈ totalSpan B := fun z => Submodule.subset_span ⟨z, rfl⟩
      simp [count, columnSet, hA, hB]
    · by_cases hcodim : Module.finrank ℝ S + 1 = Module.finrank ℝ (totalSpan B)
      · exact hBase S hS hcodim
      · apply extension_count_descent A B S (extensions_card_two_le (flat_le_total hS) heq hcodim)
        intro T hT
        have hstrict := extension_count_strict hT
        have hbound : count B T ≤ Fintype.card Z := Finset.card_le_univ _
        have hmeasure : Fintype.card Z - count B T < n := by omega
        exact ih (Fintype.card Z - count B T) hmeasure T (extension_is_flat hS hT) rfl


/-- Number of columns not annihilated by the testing linear functional. -/
def support (C : Z → V) (ℓ : Module.Dual ℝ V) : ℕ :=
  ((Finset.univ : Finset Z).filter (fun z => ℓ (C z) ≠ 0)).card

lemma support_eq_zero_iff (C : Z → V) (ℓ : Module.Dual ℝ V) :
    support C ℓ = 0 ↔ ∀ z, ℓ (C z) = 0 := by
  simp [support, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- Literal hypothesis of the source permutation lemma, in basis-free dual notation. -/
def RestrictedSupportComparison (A B : Z → V) : Prop :=
  ∀ ℓ : Module.Dual ℝ V,
    support B ℓ ≤ Fintype.card Z - Module.finrank ℝ (totalSpan B) + 1 →
    support A ℓ ≤ support B ℓ

lemma columns_mem_total_of_support_comparison {A B : Z → V}
    (h : RestrictedSupportComparison A B) : ∀ z, A z ∈ totalSpan B := by
  intro z
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (totalSpan B) (A z)).mp
  intro ℓ hℓ
  have hzB : support B ℓ = 0 := (support_eq_zero_iff B ℓ).mpr (by
    intro j
    exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ (B j) (Submodule.subset_span ⟨j, rfl⟩))
  have hzA : support A ℓ = 0 := Nat.eq_zero_of_le_zero (by simpa only [hzB] using h ℓ (by omega))
  exact (support_eq_zero_iff A ℓ).mp hzA z

lemma flat_finrank_le_count {B : Z → V} {S : Submodule ℝ V} (hS : ColumnFlat B S) :
    Module.finrank ℝ S ≤ count B S := by
  have he : Set.range (fun z : {z // B z ∈ S} => B z.val) = B '' {z | B z ∈ S} := by
    ext v
    simp
  have hf := finrank_range_le_card (R := ℝ) (fun z : {z // B z ∈ S} => B z.val)
  change Module.finrank ℝ (Submodule.span ℝ (Set.range _)) ≤ _ at hf
  rw [he, ← hS] at hf
  simpa only [Fintype.card_subtype, count, columnSet] using hf

/-- A hyperplane in the total column span is cut out there by one actual linear functional. -/
lemma hyperplane_annihilator {B : Z → V} {S : Submodule ℝ V} (hS : ColumnFlat B S)
    (hdim : Module.finrank ℝ S + 1 = Module.finrank ℝ (totalSpan B)) :
    ∃ ℓ : Module.Dual ℝ V, ∀ v ∈ totalSpan B, ℓ v = 0 ↔ v ∈ S := by
  have hne : S ≠ totalSpan B := by
    intro heq
    have hh := congrArg (fun Q : Submodule ℝ V => Module.finrank ℝ Q) heq
    omega
  obtain ⟨z, hz⟩ := exists_column_outside (B := B) (S := S)
    (fun h => hne (le_antisymm (flat_le_total hS) h))
  have hsep : ¬ ∀ ℓ : Module.Dual ℝ V, ℓ ∈ S.dualAnnihilator → ℓ (B z) = 0 := by
    intro hh
    exact hz ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S (B z)).mp hh)
  push Not at hsep
  obtain ⟨ℓ, hℓ, hnonzero⟩ := hsep
  have hST : S ≤ totalSpan B ⊓ LinearMap.ker ℓ := by
    apply le_inf (flat_le_total hS)
    intro v hv
    exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ v hv
  have hTlt : totalSpan B ⊓ LinearMap.ker ℓ < totalSpan B := by
    apply lt_of_le_of_ne inf_le_left
    intro heq
    have hzT : B z ∈ totalSpan B ⊓ LinearMap.ker ℓ := by
      rw [heq]
      exact Submodule.subset_span ⟨z, rfl⟩
    exact hnonzero hzT.2
  have hlt := Submodule.finrank_lt_finrank_of_lt hTlt
  have heq : S = totalSpan B ⊓ LinearMap.ker ℓ :=
    Submodule.eq_of_le_of_finrank_le hST (by omega)
  refine ⟨ℓ, ?_⟩
  intro v hv
  rw [heq]
  simp only [Submodule.mem_inf, LinearMap.mem_ker, hv, true_and]

lemma support_add_count_eq_card (C : Z → V) (S : Submodule ℝ V) (ℓ : Module.Dual ℝ V)
    (h : ∀ z, ℓ (C z) = 0 ↔ C z ∈ S) : support C ℓ + count C S = Fintype.card Z := by
  have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun z : Z => ℓ (C z) = 0)
  simpa only [support, count, columnSet, ← h, Finset.card_univ, add_comm] using hh

/-- The source's entire Lemma 4.2, proved from the actual restricted support tests. -/
theorem flat_count_of_restricted_support_comparison {A B : Z → V}
    (h : RestrictedSupportComparison A B) :
    ∀ S : Submodule ℝ V, ColumnFlat B S → count B S ≤ count A S := by
  have hA := columns_mem_total_of_support_comparison h
  apply all_flat_counts_of_hyperplane_counts A B hA
  intro S hS hdim
  obtain ⟨ℓ, hℓ⟩ := hyperplane_annihilator hS hdim
  have hBmem : ∀ z, B z ∈ totalSpan B := fun z => Submodule.subset_span ⟨z, rfl⟩
  have hb := support_add_count_eq_card B S ℓ (fun z => hℓ (B z) (hBmem z))
  have ha := support_add_count_eq_card A S ℓ (fun z => hℓ (A z) (hA z))
  have hrank : Module.finrank ℝ (totalSpan B) ≤ Fintype.card Z :=
    finrank_range_le_card (R := ℝ) B
  have hflat := flat_finrank_le_count hS
  have hsupport : support B ℓ ≤ Fintype.card Z - Module.finrank ℝ (totalSpan B) + 1 := by omega
  have hh := h ℓ hsupport
  omega


/-- No zero or proportional distinct columns. This is proved below from the actual 2-column test. -/
def ProjectivelyDistinct (A : Z → V) : Prop :=
  (∀ z, A z ≠ 0) ∧ ∀ i j, A i ∈ Submodule.span ℝ {A j} → i = j

lemma span_singleton_eq_of_mem {v w : V} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : v ∈ Submodule.span ℝ {w}) : Submodule.span ℝ {v} = Submodule.span ℝ {w} := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact h
  · rw [finrank_span_singleton hv, finrank_span_singleton hw]

lemma singleton_column_span_flat (B : Z → V) (z : Z) :
    ColumnFlat B (Submodule.span ℝ {B z}) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact Submodule.subset_span ⟨z, Submodule.subset_span (Set.mem_singleton _), rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨j, hj, rfl⟩
    exact hj

lemma line_count_le_one {A : Z → V} (hA : ProjectivelyDistinct A) {v : V} (hv : v ≠ 0) :
    count A (Submodule.span ℝ {v}) ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (mem_columnSet A _ i).mp hi
  have hj' := (mem_columnSet A _ j).mp hj
  have hji := span_singleton_eq_of_mem (hA.1 j) hv hj'
  apply hA.2 i j
  rwa [hji]

lemma candidate_nonzero {A B : Z → V} (hA : ProjectivelyDistinct A)
    (h : RestrictedSupportComparison A B) : ∀ z, B z ≠ 0 := by
  have hc := flat_count_of_restricted_support_comparison h ⊥ (bot_is_flat B)
  have ha : count A (⊥ : Submodule ℝ V) = 0 := by simp [count, columnSet, hA.1]
  have hb : count B (⊥ : Submodule ℝ V) = 0 := by omega
  intro z hz
  have hzB : z ∈ columnSet B (⊥ : Submodule ℝ V) := by simp [columnSet, hz]
  have hzero : columnSet B (⊥ : Submodule ℝ V) = ∅ := Finset.card_eq_zero.mp hb
  simpa only [hzero, Finset.notMem_empty] using hzB

/-- Exact permutation lemma: same number of arbitrary real columns, rank-two reference,
    and only the source's sparse test-vector premise. No competitor rank premise is added. -/
theorem permutation_of_restricted_support_comparison {A B : Z → V}
    (hA : ProjectivelyDistinct A) (h : RestrictedSupportComparison A B) :
    ∃ q : Equiv.Perm Z, ∃ d : Z → ℝ, (∀ z, d z ≠ 0) ∧ ∀ z, B z = d z • A (q z) := by
  have hB := candidate_nonzero hA h
  have hc := flat_count_of_restricted_support_comparison h
  have hline : ∀ j, count B (Submodule.span ℝ {B j}) ≤ 1 := by
    intro j
    exact (hc _ (singleton_column_span_flat B j)).trans (line_count_le_one hA (hB j))
  have hex : ∀ j, ∃ i, A i ∈ Submodule.span ℝ {B j} := by
    intro j
    have hbpos : 0 < count B (Submodule.span ℝ {B j}) := by
      apply Finset.card_pos.mpr
      exact ⟨j, (mem_columnSet B _ j).mpr (Submodule.subset_span (Set.mem_singleton _))⟩
    have hapos : 0 < count A (Submodule.span ℝ {B j}) :=
      hbpos.trans_le (hc _ (singleton_column_span_flat B j))
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hapos
    exact ⟨i, (mem_columnSet A _ i).mp hi⟩
  choose f hf using hex
  have hfeq : ∀ j, Submodule.span ℝ {A (f j)} = Submodule.span ℝ {B j} :=
    fun j => span_singleton_eq_of_mem (hA.1 (f j)) (hB j) (hf j)
  have hinj : Function.Injective f := by
    intro j k hjk
    have hsp : Submodule.span ℝ {B j} = Submodule.span ℝ {B k} := by
      rw [← hfeq j, ← hfeq k, hjk]
    apply Finset.card_le_one.mp (hline j)
    · exact (mem_columnSet B _ j).mpr (Submodule.subset_span (Set.mem_singleton _))
    · apply (mem_columnSet B _ k).mpr
      rw [hsp]
      exact Submodule.subset_span (Set.mem_singleton _)
  let q : Equiv.Perm Z := Equiv.ofBijective f (⟨hinj, Finite.surjective_of_injective hinj⟩)
  have hscale : ∀ j, ∃ u : ℝˣ, u • A (q j) = B j := by
    intro j
    exact Submodule.span_singleton_eq_span_singleton.mp (hfeq j)
  choose d hd using hscale
  exact ⟨q, (fun z => (d z : ℝ)), fun z => (d z).ne_zero,
    fun z => by simpa only [Units.smul_def] using (hd z).symm⟩

/-- Kruskal rank at least two implies the precise projective-distinctness input. -/
theorem projectivelyDistinct_of_pair_independence (A : Z → V) (hZ : 2 ≤ Fintype.card Z)
    (hPair : ∀ s : Finset Z, s.card = 2 → LinearIndependent ℝ (fun z : s => A z.val)) :
    ProjectivelyDistinct A := by
  have he : ∃ a b : Z, a ≠ b := by
    obtain ⟨a, _, b, _, hab⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ : Finset Z).card by simp only [Finset.card_univ]; omega)
    exact ⟨a, b, hab⟩
  have hne : ∀ z : Z, ∃ j : Z, z ≠ j := by
    intro z
    obtain ⟨a, b, hab⟩ := he
    by_cases hza : z = a
    · exact ⟨b, by simpa only [hza] using hab⟩
    · exact ⟨a, hza⟩
  constructor
  · intro z
    obtain ⟨j, hzj⟩ := hne z
    have hi := hPair {z,j} (by simp [hzj])
    exact hi.ne_zero ⟨z, by simp⟩
  · intro i j hij
    by_contra hne
    have hi := hPair {i,j} (by simp [hne])
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hij
    have heq : (⟨i, by simp⟩ : ({i,j} : Finset Z)) = ⟨j, by simp⟩ :=
      hi.eq_of_smul_apply_eq_smul_apply 1 a _ _ one_ne_zero (by simpa using ha.symm)
    exact hne (congrArg Subtype.val heq)


/-- The source's uniqueness of both permutation and nonzero diagonal factors. -/
theorem permutation_scaling_unique {A B : Z → V} (hA : ProjectivelyDistinct A)
    (q p : Equiv.Perm Z) (d c : Z → ℝ) (hd : ∀ z, d z ≠ 0)
    (hq : ∀ z, B z = d z • A (q z)) (hp : ∀ z, B z = c z • A (p z)) :
    q = p ∧ d = c := by
  have hqp : q = p := by
    apply Equiv.ext
    intro z
    apply hA.2
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(d z)⁻¹ * c z, ?_⟩
    have h := (hq z).symm.trans (hp z)
    rw [mul_smul, ← h, ← mul_smul, inv_mul_cancel₀ (hd z), one_smul]
  refine ⟨hqp, ?_⟩
  funext z
  apply smul_left_injective ℝ (hA.1 (q z))
  exact (hq z).symm.trans (by simpa only [hqp] using hp z)

end Gen.KruskalPermutation
