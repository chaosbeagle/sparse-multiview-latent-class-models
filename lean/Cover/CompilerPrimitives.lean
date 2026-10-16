import Cover.Normalization
import Gen.ModelEncoding

open scoped BigOperators
namespace Cover.PolyExpr
variable {n a : ℕ}
def sum : List (PolyExpr n a) → PolyExpr n a
  | [] => .rat 0
  | p :: ps => .add p (sum ps)
def product : List (PolyExpr n a) → PolyExpr n a
  | [] => .rat 1
  | p :: ps => .mul p (product ps)
def sub (p q : PolyExpr n a) : PolyExpr n a := .add p (.neg q)
def square (p : PolyExpr n a) : PolyExpr n a := .mul p p
@[simp] theorem eval_sum (cs : Fin a → ℝ) (x : Fin n → ℝ) (ps : List (PolyExpr n a)) :
    (sum ps).eval cs x = (ps.map (eval cs x)).sum := by
  induction ps with
  | nil => simp [sum,eval]
  | cons p ps ih => simp [sum,eval,ih]
@[simp] theorem eval_product (cs : Fin a → ℝ) (x : Fin n → ℝ) (ps : List (PolyExpr n a)) :
    (product ps).eval cs x = (ps.map (eval cs x)).prod := by
  induction ps with
  | nil => simp [product,eval]
  | cons p ps ih => simp [product,eval,ih]
@[simp] theorem eval_sub (cs : Fin a → ℝ) (x : Fin n → ℝ) (p q : PolyExpr n a) :
    (sub p q).eval cs x = p.eval cs x - q.eval cs x := by simp [sub,eval,sub_eq_add_neg]
@[simp] theorem eval_square (cs : Fin a → ℝ) (x : Fin n → ℝ) (p : PolyExpr n a) :
    (square p).eval cs x = (p.eval cs x)^2 := by simp [square,eval,pow_two]

/-- A computable syntax translation, preserving repeated named scalar leaves. -/
def toLegacy : PolyExpr n a → Gen.QEEncoding.PolynomialExpr (n+a)
  | .rat q => .rational q
  | .scalar i => .var (Fin.natAdd n i)
  | .var i => .var (Fin.castAdd a i)
  | .add p q => .add (toLegacy p) (toLegacy q)
  | .neg p => .neg (toLegacy p)
  | .mul p q => .mul (toLegacy p) (toLegacy q)
@[simp] theorem toLegacy_eval (cs : Fin a → ℝ) (x : Fin n → ℝ) (p : PolyExpr n a) :
    p.toLegacy.eval (Fin.addCases x cs) = p.eval cs x := by
  induction p <;> simp_all [toLegacy,eval,Gen.QEEncoding.PolynomialExpr.eval]

/-- Restore separate variable and scalar namespaces after a legacy syntax operation. -/
def fromLegacy : Gen.QEEncoding.PolynomialExpr (n+a) → PolyExpr n a
  | .rational q => .rat q
  | .var i => Fin.addCases (fun j => .var j) (fun j => .scalar j) i
  | .add p q => .add (fromLegacy p) (fromLegacy q)
  | .neg p => .neg (fromLegacy p)
  | .mul p q => .mul (fromLegacy p) (fromLegacy q)
@[simp] theorem fromLegacy_eval (cs : Fin a → ℝ) (x : Fin n → ℝ)
    (p : Gen.QEEncoding.PolynomialExpr (n+a)) :
    (fromLegacy p).eval cs x = p.eval (Fin.addCases x cs) := by
  induction p with
  | rational q => rfl
  | var i =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [fromLegacy,eval,Gen.QEEncoding.PolynomialExpr.eval]
  | add p q hp hq => simp [fromLegacy,eval,Gen.QEEncoding.PolynomialExpr.eval,hp,hq]
  | neg p hp => simp [fromLegacy,eval,Gen.QEEncoding.PolynomialExpr.eval,hp]
  | mul p q hp hq => simp [fromLegacy,eval,Gen.QEEncoding.PolynomialExpr.eval,hp,hq]
end Cover.PolyExpr

namespace Cover.Compiler
open Gen.ModelEncoding.Ordered
variable {v a : ℕ}
def sumExpr {I : Type*} (E : Enumeration I) (p : I → PolyExpr v a) : PolyExpr v a :=
  PolyExpr.sum (E.values.map p)
def prodExpr {I : Type*} (E : Enumeration I) (p : I → PolyExpr v a) : PolyExpr v a :=
  PolyExpr.product (E.values.map p)
@[simp] theorem eval_sumExpr {I : Type*} [Fintype I] (E : Enumeration I)
    (p : I → PolyExpr v a) (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    (sumExpr E p).eval cs x = ∑ i, (p i).eval cs x := by
  simpa [sumExpr,List.map_map,Function.comp_def] using E.sum_map (fun i => (p i).eval cs x)
@[simp] theorem eval_prodExpr {I : Type*} [Fintype I] (E : Enumeration I)
    (p : I → PolyExpr v a) (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    (prodExpr E p).eval cs x = ∏ i, (p i).eval cs x := by
  simpa [prodExpr,List.map_map,Function.comp_def] using E.prod_map (fun i => (p i).eval cs x)

/-- Canonical natural index enumeration contains each finite index exactly once. -/
def finEnumeration (n : ℕ) : Enumeration (Fin n) :=
  ⟨List.finRange n, List.nodup_finRange n, fun i => List.mem_finRange i⟩

/-- Literal last-coordinate affine reconstruction at the syntax level. -/
def expandBlockExpr {k : ℕ} (u : Fin k → PolyExpr v a) : Fin (k+1) → PolyExpr v a :=
  Fin.lastCases ((PolyExpr.rat 1).sub (sumExpr (finEnumeration k) u)) u
@[simp] theorem expandBlockExpr_eval {k : ℕ} (u : Fin k → PolyExpr v a)
    (cs : Fin a → ℝ) (x : Fin v → ℝ) (i : Fin (k+1)) :
    (expandBlockExpr u i).eval cs x = Normalization.expandBlock (fun j => (u j).eval cs x) i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [expandBlockExpr,Normalization.expandBlock,PolyExpr.eval]

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (n : G → ℕ) (k : ℕ)
abbrev CoordinateExpr := Gen.Geometry.Coordinate D (fun g => Fin (n g+1)) (k+1) → PolyExpr v a

def expandNormalizedExpr (u : Normalization.ReducedCoordinate D n k → PolyExpr v a) :
    CoordinateExpr D n k (v := v) (a := a) := fun i => match i with
  | .inl (c,z) => expandBlockExpr (fun j => u (.inl (c,j))) z
  | .inr ⟨g,z,y⟩ => expandBlockExpr (fun j => u (.inr ⟨g,z,j⟩)) y
noncomputable def evalCoordinates (X : CoordinateExpr D n k (v := v) (a := a))
    (cs : Fin a → ℝ) (x : Fin v → ℝ) : Normalization.Full D n k :=
  WithLp.toLp 2 (fun i => (X i).eval cs x)
@[simp] theorem eval_expandNormalizedExpr
    (u : Normalization.ReducedCoordinate D n k → PolyExpr v a)
    (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    evalCoordinates D n k (expandNormalizedExpr D n k u) cs x =
      Normalization.expandNormalized D n k (fun i => (u i).eval cs x) := by
  ext i
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;> exact expandBlockExpr_eval _ cs x _

variable {D n k}
/-- Exact native-to-baseline denotation bridge. -/
@[simp] theorem eval_legacy_coordinates (X : CoordinateExpr D n k (v := v) (a := a))
    (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    Gen.ModelEncoding.evalCoordinates D (fun g => Fin (n g+1)) (k+1)
      (fun i => (X i).toLegacy) (Fin.addCases x cs) = evalCoordinates D n k X cs x := by
  ext i
  exact PolyExpr.toLegacy_eval cs x (X i)

/-- Full Euclidean Frobenius distance; every original coordinate appears once. -/
def distance (E : ModelOrdering D (fun g => Fin (n g+1)) (k+1))
    (q : Gen.W D (k+1)) (X X' : CoordinateExpr D n k (v := v) (a := a)) : PolyExpr v a :=
  PolyExpr.fromLegacy (Gen.ModelEncoding.Ordered.distance E q
    (fun i => (X i).toLegacy) (fun i => (X' i).toLegacy))
theorem distance_eval (E : ModelOrdering D (fun g => Fin (n g+1)) (k+1))
    (q : Gen.W D (k+1)) (X X' : CoordinateExpr D n k (v := v) (a := a))
    (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    (distance E q X X').eval cs x =
      ‖evalCoordinates D n k X cs x - q⁻¹ • evalCoordinates D n k X' cs x‖^2 := by
  simp [distance,Gen.ModelEncoding.Ordered.distance_eval]

/-- Exact stacked observation objective, preserving every observation cell. -/
def objective (E : ModelOrdering D (fun g => Fin (n g+1)) (k+1))
    (X X' : CoordinateExpr D n k (v := v) (a := a)) : PolyExpr v a :=
  PolyExpr.fromLegacy (Gen.ModelEncoding.Ordered.H E
    (fun i => (X i).toLegacy) (fun i => (X' i).toLegacy))
theorem coverObjective_eval (E : ModelOrdering D (fun g => Fin (n g+1)) (k+1))
    (X X' : CoordinateExpr D n k (v := v) (a := a))
    (cs : Fin a → ℝ) (x : Fin v → ℝ) :
    (objective E X X').eval cs x =
      ‖Gen.Geometry.observation D (fun g => Fin (n g+1)) (k+1) (evalCoordinates D n k X cs x) -
        Gen.Geometry.observation D (fun g => Fin (n g+1)) (k+1) (evalCoordinates D n k X' cs x)‖^2 := by
  simp [objective,Gen.ModelEncoding.Ordered.H_eval]
end Cover.Compiler
