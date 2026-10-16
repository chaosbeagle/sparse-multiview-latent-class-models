import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option maxHeartbeats 800000
open scoped BigOperators Classical
noncomputable section
namespace Gen.Estimator

/-- The exact lexicographic minimum in the supplied order 0,...,n-1:
each coordinate is smallest among points matching all earlier coordinates. -/
def LexLeast {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K ∧ ∀ i : Fin n, ∀ y ∈ K,
    (∀ j : Fin n, j.val < i.val → y j = x j) → x i ≤ y i

/-- Successive compact coordinate minimizations preserve all earlier minima. -/
theorem exists_prefix_min {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty) : ∀ k : ℕ, k ≤ n →
    ∃ x ∈ K, ∀ i : Fin n, i.val < k → ∀ y ∈ K,
      (∀ j : Fin n, j.val < i.val → y j = x j) → x i ≤ y i := by
  intro k
  induction k with
  | zero =>
      intro _
      obtain ⟨x,hx⟩ := hne
      exact ⟨x,hx,fun i hi => (Nat.not_lt_zero i.val hi).elim⟩
  | succ k ih =>
      intro hk
      obtain ⟨x,hx,hxmin⟩ := ih (by omega)
      let i : Fin n := ⟨k, by omega⟩
      let S : Set (EuclideanSpace ℝ (Fin n)) := K ∩
        {y | ∀ j : Fin n, j.val < k → y j = x j}
      have hclosed : IsClosed {y : EuclideanSpace ℝ (Fin n) |
          ∀ j : Fin n, j.val < k → y j = x j} := by
        simp only [Set.setOf_forall]
        apply isClosed_iInter
        intro j
        apply isClosed_iInter
        intro _
        exact isClosed_eq (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j) continuous_const
      have hS : IsCompact S := hK.inter_right hclosed
      have hSne : S.Nonempty := ⟨x,hx,fun _ _ => rfl⟩
      obtain ⟨z,hz,hzmin⟩ := hS.exists_isMinOn hSne
        (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousOn
      refine ⟨z,hz.1,?_⟩
      intro j hj y hy hprefix
      by_cases hjk : j.val < k
      · rw [hz.2 j hjk]
        apply hxmin j hjk y hy
        intro l hl
        exact (hprefix l hl).trans (hz.2 l (hl.trans hjk))
      · have hji : j = i := Fin.ext (by dsimp [i]; omega)
        subst j
        apply hzmin
        exact ⟨hy,fun l hl => (hprefix l hl).trans (hz.2 l hl)⟩

/-- Every nonempty compact set has a coordinatewise lexicographic least member. -/
theorem exists_lexLeast {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty) : ∃ x, LexLeast K x := by
  obtain ⟨x,hx,hxmin⟩ := exists_prefix_min K hK hne n le_rfl
  exact ⟨x,hx,fun i => hxmin i i.isLt⟩

/-- The lexicographic least point is genuinely unique as a full Euclidean array. -/
theorem LexLeast.unique {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : LexLeast K x) (hy : LexLeast K y) : x = y := by
  have hcoord : ∀ k : ℕ, ∀ i : Fin n, i.val = k → x i = y i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro i hi
        have hp : ∀ j : Fin n, j.val < i.val → x j = y j := by
          intro j hj
          exact ih j.val (hi ▸ hj) j rfl
        exact le_antisymm (hx.2 i y hy.1 (fun j hj => (hp j hj).symm))
          (hy.2 i x hx.1 hp)
  ext i
  exact hcoord i.val i rfl

/-- Exact mathematical uniqueness, independent of any implementation of real algebraic QE. -/
theorem existsUnique_lexLeast {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty) : ∃! x, LexLeast K x := by
  obtain ⟨x,hx⟩ := exists_lexLeast K hK hne
  exact ⟨x,hx,fun y hy => hy.unique hx⟩


/-- Standard strict lexicographic comparison by the first unequal coordinate. -/
def LexLess {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ i : Fin n, (∀ j : Fin n, j.val < i.val → x j = y j) ∧ x i < y i

/-- Prefix minimization really is a minimum in the standard lexicographic order. -/
theorem LexLeast.eq_or_lexLess {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : LexLeast K x)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ K) : x = y ∨ LexLess x y := by
  by_cases heq : x = y
  · exact Or.inl heq
  · right
    have hex : ∃ i : Fin n, x i ≠ y i := by
      by_contra hh
      push Not at hh
      apply heq
      ext i
      exact hh i
    let S := Finset.univ.filter (fun i : Fin n => x i ≠ y i)
    have hS : S.Nonempty := by
      obtain ⟨i,hi⟩ := hex
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    let i := S.min' hS
    have hi : x i ≠ y i := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
    have hp : ∀ j : Fin n, j.val < i.val → x j = y j := by
      intro j hj
      by_contra hne
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩
      have hle : i ≤ j := Finset.min'_le S j hjS
      exact (not_le_of_gt hj) hle
    exact ⟨i,hp,lt_of_le_of_ne (hx.2 i y hy (fun j hj => (hp j hj).symm)) hi⟩

/-- Noncomputable mathematical selection. This is not an executable optimization algorithm. -/
def lexSelect {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty) : EuclideanSpace ℝ (Fin n) :=
  Classical.choose (exists_lexLeast K hK hne)

theorem lexSelect_spec {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty) : LexLeast K (lexSelect K hK hne) :=
  Classical.choose_spec (exists_lexLeast K hK hne)

/-- Full global real minimizer set, not stationary points or local optima. -/
def minimizers {A : Type*} (K : Set A) (loss : A → ℝ) : Set A :=
  {x | x ∈ K ∧ ∀ y ∈ K, loss x ≤ loss y}

theorem minimizers_nonempty {A : Type*} [TopologicalSpace A]
    (K : Set A) (hK : IsCompact K) (hne : K.Nonempty)
    (loss : A → ℝ) (hcont : Continuous loss) : (minimizers K loss).Nonempty := by
  obtain ⟨x,hx,hxmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  exact ⟨x,hx,hxmin⟩

theorem minimizers_compact {A : Type*} [TopologicalSpace A]
    (K : Set A) (hK : IsCompact K) (hne : K.Nonempty)
    (loss : A → ℝ) (hcont : Continuous loss) : IsCompact (minimizers K loss) := by
  obtain ⟨x,hx,hxmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have heq : minimizers K loss = K ∩ {y | loss y = loss x} := by
    ext y
    constructor
    · rintro ⟨hy,hymin⟩
      exact ⟨hy,le_antisymm (hymin x hx) (hxmin hy)⟩
    · rintro ⟨hy,he⟩
      exact ⟨hy,fun z hz => he ▸ hxmin hz⟩
  rw [heq]
  exact hK.inter_right (isClosed_eq hcont continuous_const)

/-- The specified baseline is the unique lexicographic member of global minimizers. -/
theorem existsUnique_lexMinimizer {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty)
    (loss : EuclideanSpace ℝ (Fin n) → ℝ) (hcont : Continuous loss) :
    ∃! x, LexLeast (minimizers K loss) x :=
  existsUnique_lexLeast _ (minimizers_compact K hK hne loss hcont)
    (minimizers_nonempty K hK hne loss hcont)

/-- Mathematical selection only; effectiveness over algebraic encodings is not claimed. -/
def lexMinimizer {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty)
    (loss : EuclideanSpace ℝ (Fin n) → ℝ) (hcont : Continuous loss) :
    EuclideanSpace ℝ (Fin n) :=
  lexSelect (minimizers K loss) (minimizers_compact K hK hne loss hcont)
    (minimizers_nonempty K hK hne loss hcont)

theorem lexMinimizer_spec {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty)
    (loss : EuclideanSpace ℝ (Fin n) → ℝ) (hcont : Continuous loss) :
    LexLeast (minimizers K loss) (lexMinimizer K hK hne loss hcont) :=
  lexSelect_spec _ _ _

theorem lexMinimizer_mem {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty)
    (loss : EuclideanSpace ℝ (Fin n) → ℝ) (hcont : Continuous loss) :
    lexMinimizer K hK hne loss hcont ∈ K := (lexMinimizer_spec K hK hne loss hcont).1.1

theorem lexMinimizer_optimal {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty)
    (loss : EuclideanSpace ℝ (Fin n) → ℝ) (hcont : Continuous loss) :
    ∀ y ∈ K, loss (lexMinimizer K hK hne loss hcont) ≤ loss y :=
  (lexMinimizer_spec K hK hne loss hcont).1.2

section LeastSquares
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H]

/-- The baseline minimizes squared Euclidean residual and then the supplied coordinate order. -/
def leastSquares {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ (Fin n) → H) (hF : Continuous F) (data : H) :
    EuclideanSpace ℝ (Fin n) :=
  lexMinimizer K hK hne (fun x => ‖F x - data‖ ^ 2) (by fun_prop)

theorem leastSquares_mem (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ (Fin n) → H) (hF : Continuous F) (data : H) :
    leastSquares K hK hne F hF data ∈ K := lexMinimizer_mem _ _ _ _ _

/-- Exact global residual comparison, including every possible data vector. -/
theorem leastSquares_optimal (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ (Fin n) → H) (hF : Continuous F) (data : H) :
    ∀ y ∈ K, ‖F (leastSquares K hK hne F hF data) - data‖ ≤ ‖F y - data‖ := by
  intro y hy
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact lexMinimizer_optimal K hK hne (fun x => ‖F x-data‖^2) (by fun_prop) y hy

/-- A deterministic function of arbitrary observations, with an all-outcome global guarantee. -/
theorem leastSquares_all_outcomes {Ω : Type*} (data : Ω → H)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ (Fin n) → H) (hF : Continuous F) :
    ∃ fit : Ω → EuclideanSpace ℝ (Fin n),
      (∀ ω, fit ω ∈ K) ∧ (∀ ω, ∀ y ∈ K, ‖F (fit ω) - data ω‖ ≤ ‖F y - data ω‖) ∧
      ∀ ω, LexLeast (minimizers K (fun x => ‖F x-data ω‖^2)) (fit ω) := by
  refine ⟨fun ω => leastSquares K hK hne F hF (data ω), ?_, ?_, ?_⟩
  · exact fun ω => leastSquares_mem K hK hne F hF (data ω)
  · exact fun ω => leastSquares_optimal K hK hne F hF (data ω)
  · exact fun ω => lexMinimizer_spec K hK hne (fun x => ‖F x-data ω‖^2) (by fun_prop)
end LeastSquares

section OrderedCoordinates
variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The declared coordinate order, with exact entrywise Euclidean isometry. -/
def coordinateChart (order : ι ≃ Fin n) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ order

@[simp] theorem coordinateChart_apply (order : ι ≃ Fin n) (x : EuclideanSpace ℝ ι) (i : Fin n) :
    coordinateChart order x i = x (order.symm i) := rfl

/-- Lexicographic order is transported using the explicitly supplied coordinate enumeration. -/
def OrderedLexLeast (order : ι ≃ Fin n) (K : Set (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) : Prop :=
  LexLeast (coordinateChart order '' K) (coordinateChart order x)

theorem existsUnique_orderedLexLeast (order : ι ≃ Fin n)
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃! x, OrderedLexLeast order K x := by
  let c := coordinateChart order
  obtain ⟨z,hz,hzu⟩ := existsUnique_lexLeast (c '' K) (hK.image c.continuous) (hne.image c)
  refine ⟨c.symm z, ?_, ?_⟩
  · simpa only [OrderedLexLeast, c, LinearIsometryEquiv.apply_symm_apply] using hz
  · intro y hy
    apply c.injective
    simpa using hzu (c y) hy

/-- Exact compact least-squares selection in any supplied finite coordinate order. -/
def orderedLeastSquares {H : Type*} [NormedAddCommGroup H] (order : ι ≃ Fin n)
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ ι → H) (hF : Continuous F) (data : H) : EuclideanSpace ℝ ι :=
  let c := coordinateChart order
  c.symm (leastSquares (c '' K) (hK.image c.continuous) (hne.image c)
    (F ∘ c.symm) (hF.comp c.symm.continuous) data)

theorem orderedLeastSquares_mem {H : Type*} [NormedAddCommGroup H] (order : ι ≃ Fin n)
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ ι → H) (hF : Continuous F) (data : H) :
    orderedLeastSquares order K hK hne F hF data ∈ K := by
  let c := coordinateChart order
  have h := leastSquares_mem (c '' K) (hK.image c.continuous) (hne.image c)
    (F ∘ c.symm) (hF.comp c.symm.continuous) data
  obtain ⟨x,hx,hxeq⟩ := h
  change c.symm _ ∈ K
  rw [← hxeq, c.symm_apply_apply]
  exact hx

theorem orderedLeastSquares_optimal {H : Type*} [NormedAddCommGroup H] (order : ι ≃ Fin n)
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ ι → H) (hF : Continuous F) (data : H) :
    ∀ y ∈ K, ‖F (orderedLeastSquares order K hK hne F hF data) - data‖ ≤ ‖F y - data‖ := by
  intro y hy
  let c := coordinateChart order
  have h := leastSquares_optimal (c '' K) (hK.image c.continuous) (hne.image c)
    (F ∘ c.symm) (hF.comp c.symm.continuous) data (c y) ⟨y,hy,rfl⟩
  simpa only [orderedLeastSquares, c, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply] using h

/-- The chosen point is lexicographically least among all global squared-residual minimizers. -/
theorem orderedLeastSquares_lexLeast {H : Type*} [NormedAddCommGroup H] (order : ι ≃ Fin n)
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ ι → H) (hF : Continuous F) (data : H) :
    OrderedLexLeast order (minimizers K (fun x => ‖F x-data‖^2))
      (orderedLeastSquares order K hK hne F hF data) := by
  let c := coordinateChart order
  have heq : c '' minimizers K (fun x => ‖F x-data‖^2) =
      minimizers (c '' K) (fun z => ‖(F ∘ c.symm) z-data‖^2) := by
    ext z
    constructor
    · rintro ⟨x,⟨hx,hxmin⟩,rfl⟩
      refine ⟨⟨x,hx,rfl⟩,?_⟩
      rintro w ⟨y,hy,rfl⟩
      simpa using hxmin y hy
    · rintro ⟨⟨x,hx,rfl⟩,hzmin⟩
      refine ⟨x,⟨hx,?_⟩,rfl⟩
      intro y hy
      simpa using hzmin (c y) ⟨y,hy,rfl⟩
  have h := lexMinimizer_spec (c '' K) (hK.image c.continuous) (hne.image c)
    (fun z => ‖(F ∘ c.symm) z-data‖^2) (by fun_prop)
  change LexLeast (c '' minimizers K (fun x => ‖F x-data‖^2)) (c (c.symm _))
  rw [c.apply_symm_apply, heq]
  exact h

/-- No second point can satisfy the specified lexicographic tie-break rule. -/
theorem orderedLeastSquares_unique {H : Type*} [NormedAddCommGroup H] (order : ι ≃ Fin n)
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ ι → H) (hF : Continuous F) (data : H)
    (x : EuclideanSpace ℝ ι)
    (hx : OrderedLexLeast order (minimizers K (fun x => ‖F x-data‖^2)) x) :
    x = orderedLeastSquares order K hK hne F hF data := by
  apply (coordinateChart order).injective
  exact hx.unique (orderedLeastSquares_lexLeast order K hK hne F hF data)

theorem orderedLeastSquares_all_outcomes {H Ω : Type*} [NormedAddCommGroup H]
    (order : ι ≃ Fin n) (data : Ω → H)
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hne : K.Nonempty)
    (F : EuclideanSpace ℝ ι → H) (hF : Continuous F) :
    ∃ fit : Ω → EuclideanSpace ℝ ι, (∀ ω, fit ω ∈ K) ∧
      (∀ ω, ∀ y ∈ K, ‖F (fit ω) - data ω‖ ≤ ‖F y - data ω‖) ∧
      ∀ ω, OrderedLexLeast order (minimizers K (fun x => ‖F x-data ω‖^2)) (fit ω) := by
  refine ⟨fun ω => orderedLeastSquares order K hK hne F hF (data ω), ?_, ?_, ?_⟩
  · exact fun ω => orderedLeastSquares_mem order K hK hne F hF (data ω)
  · exact fun ω => orderedLeastSquares_optimal order K hK hne F hF (data ω)
  · exact fun ω => orderedLeastSquares_lexLeast order K hK hne F hF (data ω)
end OrderedCoordinates

end Gen.Estimator
