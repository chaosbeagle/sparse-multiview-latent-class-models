import Gen.RateBridge

open scoped Classical
noncomputable section
namespace Gen.QuotientMetric

variable (Γ E : Type*) [Fintype Γ] [Group Γ] [MetricSpace E]
  [MulAction Γ E] [IsIsometricSMul Γ E]

/-- Exactly the declared finite gauge orbit relation. -/
def orbitSetoid : Setoid E where
  r x y := ∃ q : Γ, x = q • y
  iseqv := by
    constructor
    · intro x; exact ⟨1,by simp⟩
    · rintro x y ⟨q,rfl⟩; exact ⟨q⁻¹,by simp⟩
    · rintro x y z ⟨q,rfl⟩ ⟨p,rfl⟩; exact ⟨q*p,by simp [mul_smul]⟩

abbrev OrbitSpace := Quotient (orbitSetoid Γ E)

def quotientDist (x y : OrbitSpace Γ E) : ℝ :=
  Quotient.liftOn₂ x y (Gen.Rates.orbitDist (Γ := Γ)) (by
    rintro a b a' b' ⟨q,rfl⟩ ⟨p,rfl⟩
    simp only [Gen.Rates.orbitDist_smul_left, Gen.Rates.orbitDist_smul_right])

instance orbitMetric : MetricSpace (OrbitSpace Γ E) where
  dist := quotientDist Γ E
  dist_self := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact Gen.Rates.orbitDist_self x
  dist_comm := by
    intro x y
    induction x,y using Quotient.inductionOn₂ with
    | h x y => exact Gen.Rates.orbitDist_symm x y
  dist_triangle := by
    intro x y z
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        induction z using Quotient.inductionOn with
        | h z => exact Gen.Rates.orbitDist_triangle x y z
  eq_of_dist_eq_zero := by
    intro x y
    induction x,y using Quotient.inductionOn₂ with
    | h x y =>
      intro h
      exact Quotient.sound ((Gen.Rates.orbitDist_eq_zero_iff x y).mp h)

@[simp] theorem dist_mk (x y : E) :
    dist (⟦x⟧ : OrbitSpace Γ E) ⟦y⟧ = Gen.Rates.orbitDist (Γ := Γ) x y := rfl

/-- The model's literal right-pullback minimum is precisely a genuine metric on
    the declared gauge classes of its complete Euclidean coordinate vectors. -/
theorem parameter_distance_eq_quotient
    {G : Type*} [Fintype G] [DecidableEq G]
    (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)
    (H : Subgroup (Gen.W D r)) (θ η : Gen.Parameter D Y r) :
    Gen.RateBridge.parameterDist D Y r H θ η =
      dist (⟦Gen.Geometry.embed D Y r θ⟧ : OrbitSpace H (Gen.Geometry.Ambient D Y r))
        ⟦Gen.Geometry.embed D Y r η⟧ := rfl

end Gen.QuotientMetric
