import Cover.ConcreteCompiler

namespace Cover.PolyExpr
/-- Degree in model variables only: exact named scalar coefficients have degree zero. -/
def variableDegree {n a : ℕ} : PolyExpr n a → ℕ
  | .rat _ | .scalar _ => 0
  | .var _ => 1
  | .add p q => max p.variableDegree q.variableDegree
  | .neg p => p.variableDegree
  | .mul p q => p.variableDegree + q.variableDegree

@[simp] theorem variableDegree_sub {n a : ℕ} (p q : PolyExpr n a) :
    (p.sub q).variableDegree = max p.variableDegree q.variableDegree := rfl
@[simp] theorem variableDegree_square {n a : ℕ} (p : PolyExpr n a) :
    p.square.variableDegree = p.variableDegree + p.variableDegree := rfl

theorem variableDegree_sum_le {n a b : ℕ} (ps : List (PolyExpr n a))
    (h : ∀ p ∈ ps, p.variableDegree ≤ b) : (sum ps).variableDegree ≤ b := by
  induction ps with
  | nil => exact Nat.zero_le _
  | cons p ps ih =>
    exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))
end Cover.PolyExpr

open scoped BigOperators
namespace Cover.Degree
open Gen.QEEncoding Gen.ModelEncoding.Ordered

/-- A grading on legacy variable slots distinguishes model variables from scalar slots. -/
def legacyDegree {v : ℕ} (d : Fin v → ℕ) : PolynomialExpr v → ℕ
  | .rational _ => 0
  | .var i => d i
  | .add p q => max (legacyDegree d p) (legacyDegree d q)
  | .neg p => legacyDegree d p
  | .mul p q => legacyDegree d p + legacyDegree d q

@[simp] theorem legacyDegree_sub {v : ℕ} (d : Fin v → ℕ) (p q : PolynomialExpr v) :
    legacyDegree d (p.sub q) = max (legacyDegree d p) (legacyDegree d q) := rfl
@[simp] theorem legacyDegree_square {v : ℕ} (d : Fin v → ℕ) (p : PolynomialExpr v) :
    legacyDegree d p.square = legacyDegree d p + legacyDegree d p := rfl

def slots (n a : ℕ) : Fin (n+a) → ℕ := Fin.addCases (fun _ => 1) (fun _ => 0)

@[simp] theorem toLegacy_degree {n a : ℕ} (p : PolyExpr n a) :
    legacyDegree (slots n a) p.toLegacy = p.variableDegree := by
  induction p <;> simp_all [PolyExpr.toLegacy,legacyDegree,slots,PolyExpr.variableDegree]

@[simp] theorem fromLegacy_degree {n a : ℕ} (p : PolynomialExpr (n+a)) :
    (PolyExpr.fromLegacy (n := n) (a := a) p).variableDegree = legacyDegree (slots n a) p := by
  induction p with
  | rational q => rfl
  | var i =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [PolyExpr.fromLegacy,legacyDegree,slots,PolyExpr.variableDegree]
  | add p q hp hq => simp [PolyExpr.fromLegacy,legacyDegree,PolyExpr.variableDegree,hp,hq]
  | neg p hp => simp [PolyExpr.fromLegacy,legacyDegree,PolyExpr.variableDegree,hp]
  | mul p q hp hq => simp [PolyExpr.fromLegacy,legacyDegree,PolyExpr.variableDegree,hp,hq]

theorem legacy_sum_le {v b : ℕ} (d : Fin v → ℕ) (ps : List (PolynomialExpr v))
    (h : ∀ p ∈ ps, legacyDegree d p ≤ b) : legacyDegree d (PolynomialExpr.sum ps) ≤ b := by
  induction ps with
  | nil => exact Nat.zero_le _
  | cons p ps ih =>
    exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem legacy_product_eq_sum {v : ℕ} (d : Fin v → ℕ) (ps : List (PolynomialExpr v)) :
    legacyDegree d (Gen.ModelEncoding.Ordered.product ps) = (ps.map (legacyDegree d)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [Gen.ModelEncoding.Ordered.product,legacyDegree,ih]

theorem legacy_sumExpr_le {v b : ℕ} {I : Type*} (d : Fin v → ℕ) (E : Enumeration I)
    (p : I → PolynomialExpr v) (h : ∀ i, legacyDegree d (p i) ≤ b) :
    legacyDegree d (sumExpr E p) ≤ b := by
  apply legacy_sum_le
  intro q hq
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hq
  exact h i

theorem legacy_prodExpr_le {v : ℕ} {I : Type*} [Fintype I] (d : Fin v → ℕ)
    (E : Enumeration I) (p : I → PolynomialExpr v) (b : I → ℕ)
    (h : ∀ i, legacyDegree d (p i) ≤ b i) :
    legacyDegree d (prodExpr E p) ≤ ∑ i, b i := by
  rw [prodExpr,legacy_product_eq_sum,List.map_map]
  change (E.values.map (fun i => legacyDegree d (p i))).sum ≤ _
  rw [E.sum_map]
  exact Finset.sum_le_sum (fun i _ => h i)

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {Y : G → Type*} [∀ g, Fintype (Y g)] {r v : ℕ}

/-- An actual triple has exactly three kernel factors; the weight supplies the fourth. -/
theorem legacy_observation_degree_le_four (d : Fin v → ℕ) (E : ModelOrdering D Y r)
    (X : Gen.ModelEncoding.CoordinateExpressions D Y r (v := v))
    (hX : ∀ i, legacyDegree d (X i) ≤ 1) (e : D.Edge) (x : D.Outcome Y e) :
    legacyDegree d (Gen.ModelEncoding.Ordered.observation E X e x) ≤ 4 := by
  apply legacy_sumExpr_le
  intro z
  change legacyDegree d (X (.inl (D.component e,z))) +
    legacyDegree d (prodExpr (E.edgeGroups e) (fun g => X (.inr ⟨g.val,z,x g⟩))) ≤ 4
  have hp := legacy_prodExpr_le d (E.edgeGroups e)
    (fun g => X (.inr ⟨g.val,z,x g⟩)) (fun _ => 1) (fun g => hX (.inr ⟨g.val,z,x g⟩))
  have hc : Fintype.card (D.GroupAt e) = 3 := by
    rw [Fintype.card_coe,D.edge_card e.val e.property]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,hc] at hp
  have hw := hX (.inl (D.component e,z))
  omega

/-- Squared differences of quartic observations have variable degree at most eight. -/
theorem legacy_objective_degree_le_eight (d : Fin v → ℕ) (E : ModelOrdering D Y r)
    (X X' : Gen.ModelEncoding.CoordinateExpressions D Y r (v := v))
    (hX : ∀ i, legacyDegree d (X i) ≤ 1) (hX' : ∀ i, legacyDegree d (X' i) ≤ 1) :
    legacyDegree d (Gen.ModelEncoding.Ordered.H E X X') ≤ 8 := by
  apply legacy_sumExpr_le
  intro ex
  simp only [legacyDegree_square,legacyDegree_sub]
  have h1 := legacy_observation_degree_le_four d E X hX ex.1 ex.2
  have h2 := legacy_observation_degree_le_four d E X' hX' ex.1 ex.2
  omega
end Cover.Degree

namespace Cover.Compiler
open Gen.ModelEncoding.Ordered
variable {v a : ℕ}

theorem expandBlockExpr_degree_le_one {k : ℕ} (u : Fin k → PolyExpr v a)
    (hu : ∀ i, (u i).variableDegree ≤ 1) (i : Fin (k+1)) :
    (expandBlockExpr u i).variableDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [expandBlockExpr,Fin.lastCases_last,PolyExpr.variableDegree_sub,
      PolyExpr.variableDegree,Nat.zero_max]
    apply PolyExpr.variableDegree_sum_le
    intro p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    exact hu j
  · simpa only [expandBlockExpr,Fin.lastCases_castSucc] using hu j

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {n : G → ℕ} {k : ℕ}

theorem expandNormalizedExpr_degree_le_one
    (u : Normalization.ReducedCoordinate D n k → PolyExpr v a)
    (hu : ∀ i, (u i).variableDegree ≤ 1) (i : Gen.Geometry.Coordinate D (fun g => Fin (n g+1)) (k+1)) :
    (expandNormalizedExpr D n k u i).variableDegree ≤ 1 := by
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩
  · exact expandBlockExpr_degree_le_one _ (fun j => hu (.inl (c,j))) z
  · exact expandBlockExpr_degree_le_one _ (fun j => hu (.inr ⟨g,z,j⟩)) y

/-- Native shared grammar version of the actual observation-cell compiler. -/
def observationExpr (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := a))
    (e : D.Edge) (x : D.Outcome (fun g => Fin (n g+1)) e) : PolyExpr v a :=
  PolyExpr.fromLegacy (Gen.ModelEncoding.Ordered.observation E (fun i => (X i).toLegacy) e x)

theorem observationExpr_degree_le_four (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := a)) (hX : ∀ i, (X i).variableDegree ≤ 1)
    (e : D.Edge) (x : D.Outcome (fun g => Fin (n g+1)) e) :
    (observationExpr E X e x).variableDegree ≤ 4 := by
  simp only [observationExpr,Degree.fromLegacy_degree]
  exact Degree.legacy_observation_degree_le_four _ E _
    (fun i => by simpa only [Degree.toLegacy_degree] using hX i) e x

theorem objective_degree_le_eight (E : Order (D := D) (n := n) (k := k))
    (X X' : CoordinateExpr D n k (v := v) (a := a))
    (hX : ∀ i, (X i).variableDegree ≤ 1) (hX' : ∀ i, (X' i).variableDegree ≤ 1) :
    (objective E X X').variableDegree ≤ 8 := by
  simp only [objective,Degree.fromLegacy_degree]
  exact Degree.legacy_objective_degree_le_eight _ E _ _
    (fun i => by simpa only [Degree.toLegacy_degree] using hX i)
    (fun i => by simpa only [Degree.toLegacy_degree] using hX' i)
end Cover.Compiler

namespace Cover.ConcreteCompiler
open Cover.FiniteDesign
/-- The literal generated objective has degree at most eight for every valid finite input. -/
theorem objective_variableDegree_le_eight (I : Syntax) (h : Valid I) :
    (objective I h).variableDegree ≤ 8 := by
  apply Compiler.objective_degree_le_eight
  · apply Compiler.expandNormalizedExpr_degree_le_one
    intro i; exact le_rfl
  · apply Compiler.expandNormalizedExpr_degree_le_one
    intro i; exact le_rfl
end Cover.ConcreteCompiler
