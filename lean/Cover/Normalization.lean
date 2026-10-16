import Gen.Conditioned
import Cover.IntervalDefs

open scoped BigOperators
namespace Cover.Normalization

/-- The last coordinate is eliminated, with no positivity restriction on stored reals. -/
noncomputable def expandBlock {k : ℕ} (u : Fin k → ℝ) : Fin (k+1) → ℝ :=
  Fin.lastCases (1 - ∑ i, u i) u

def projectBlock {k : ℕ} (u : Fin (k+1) → ℝ) : Fin k → ℝ := fun i => u i.castSucc

@[simp] theorem expandBlock_castSucc {k : ℕ} (u : Fin k → ℝ) (i : Fin k) :
    expandBlock u i.castSucc = u i := by simp [expandBlock]
@[simp] theorem expandBlock_last {k : ℕ} (u : Fin k → ℝ) :
    expandBlock u (Fin.last k) = 1 - ∑ i, u i := by simp [expandBlock]
@[simp] theorem project_expand_block {k : ℕ} (u : Fin k → ℝ) :
    projectBlock (expandBlock u) = u := by funext i; simp [projectBlock]
theorem expandBlock_total {k : ℕ} (u : Fin k → ℝ) :
    ∑ i, expandBlock u i = 1 := by
  rw [Fin.sum_univ_castSucc]; simp

theorem expand_project_block {k : ℕ} (u : Fin (k+1) → ℝ) (hu : ∑ i, u i = 1) :
    expandBlock (projectBlock u) = u := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [expandBlock_last]
    rw [Fin.sum_univ_castSucc] at hu
    simp only [projectBlock]
    linarith
  · simp [projectBlock]

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (n : G → ℕ) (k : ℕ)
abbrev ReducedCoordinate := (D.Component × Fin k) ⊕ ((g : G) × (Fin (k+1) × Fin (n g)))
abbrev Full := Gen.Geometry.Ambient D (fun g => Fin (n g+1)) (k+1)
abbrev Reduced := ReducedCoordinate D n k → ℝ

noncomputable def expandNormalized (u : Reduced D n k) : Full D n k :=
  WithLp.toLp 2 fun i => match i with
  | .inl (c,z) => expandBlock (fun j => u (.inl (c,j))) z
  | .inr ⟨g,z,y⟩ => expandBlock (fun j => u (.inr ⟨g,z,j⟩)) y

def projectNormalized (x : Full D n k) : Reduced D n k := fun i => match i with
  | .inl (c,z) => x (.inl (c,z.castSucc))
  | .inr ⟨g,z,y⟩ => x (.inr ⟨g,z,y.castSucc⟩)

@[simp] theorem project_expand (u : Reduced D n k) :
    projectNormalized D n k (expandNormalized D n k u) = u := by
  funext i
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;>
    simp [projectNormalized,expandNormalized]

theorem expand_normalized (u : Reduced D n k) :
    Gen.Geometry.Normalized D (fun g => Fin (n g+1)) (k+1) (expandNormalized D n k u) := by
  constructor
  · intro c; exact expandBlock_total _
  · intro g z; exact expandBlock_total _

@[simp] theorem expand_project (x : Full D n k)
    (hx : Gen.Geometry.Normalized D (fun g => Fin (n g+1)) (k+1) x) :
    expandNormalized D n k (projectNormalized D n k x) = x := by
  ext i
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩
  · exact congrFun (expand_project_block (fun j => x (.inl (c,j))) (hx.1 c)) z
  · exact congrFun (expand_project_block (fun j => x (.inr ⟨g,z,j⟩)) (hx.2 g z)) y

theorem expand_injective : Function.Injective (expandNormalized D n k) := by
  intro u v h
  have := congrArg (projectNormalized D n k) h
  simpa using this

theorem normalized_iff_unique_expansion (x : Full D n k) :
    Gen.Geometry.Normalized D (fun g => Fin (n g+1)) (k+1) x ↔
      ∃! u, expandNormalized D n k u = x := by
  constructor
  · intro hx
    exact ⟨projectNormalized D n k x, expand_project D n k x hx,
      fun u hu => expand_injective D n k (hu.trans (expand_project D n k x hx).symm)⟩
  · rintro ⟨u, rfl, _⟩; exact expand_normalized D n k u

/-- Projection of every real K point lies in the full closed unit cube. -/
theorem project_K_mem_unitBox {w σ : ℝ} (hw : 0 ≤ w) (x : Full D n k)
    (hx : x ∈ Gen.Conditioned.K D (fun g => Fin (n g+1)) (k+1) w σ) :
    ∀ i, projectNormalized D n k x i ∈ Set.Icc (0:ℝ) 1 := by
  intro i
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;>
    exact Gen.Conditioned.coordinate_mem_Icc hw hx _

/-- Number of stored coordinates, before pairing. -/
theorem reduced_dimension :
    Fintype.card (ReducedCoordinate D n k) = Fintype.card D.Component * k +
      (k+1) * ∑ g, n g := by
  classical
  simp [ReducedCoordinate,Fintype.card_sum,Fintype.card_prod,Fintype.card_sigma,
    Finset.mul_sum]

theorem pair_dimension_pos (hk : 0 < k) :
    0 < 2 * Fintype.card (ReducedCoordinate D n k) := by
  letI := D.component_nonempty
  rw [reduced_dimension]
  exact Nat.mul_pos (by decide) (Nat.add_pos_left (Nat.mul_pos Fintype.card_pos hk) _)

end Cover.Normalization
