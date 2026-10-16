import Cover.FiniteTasks
import Cover.CodedPermutations
import Cover.ConcreteCompiler
import Cover.FlatComponentCache

namespace Cover.CompilerAstTasks
open Cover.FinTask Gen.QEEncoding Gen.ModelEncoding.Ordered
variable {v a : ℕ}

/-- Syntax builders traverse the source enumeration without first building a whole expression. -/
def sumTask {I : Type} (f : I → FinTask (PolyExpr v a)) : List I → FinTask (PolyExpr v a)
  | [] => primitive (fun _ => .rat 0)
  | i::is => .step fun _ => do
      let p ← f i
      let q ← sumTask f is
      primitive (fun _ => .add p q)
@[simp] theorem sumTask_result {I : Type} (f : I → FinTask (PolyExpr v a)) (is : List I) :
    (sumTask f is).result = PolyExpr.sum (is.map (fun i => (f i).result)) := by
  induction is <;> simp_all [sumTask,PolyExpr.sum]

def legacySumTask {I : Type} (f : I → FinTask (PolynomialExpr v)) : List I → FinTask (PolynomialExpr v)
  | [] => primitive (fun _ => .rational 0)
  | i::is => .step fun _ => do
      let p ← f i
      let q ← legacySumTask f is
      primitive (fun _ => .add p q)
@[simp] theorem legacySumTask_result {I : Type} (f : I → FinTask (PolynomialExpr v)) (is : List I) :
    (legacySumTask f is).result = PolynomialExpr.sum (is.map (fun i => (f i).result)) := by
  induction is <;> simp_all [legacySumTask,PolynomialExpr.sum]

def legacyProdTask {I : Type} (f : I → FinTask (PolynomialExpr v)) : List I → FinTask (PolynomialExpr v)
  | [] => primitive (fun _ => .rational 1)
  | i::is => .step fun _ => do
      let p ← f i
      let q ← legacyProdTask f is
      primitive (fun _ => .mul p q)
@[simp] theorem legacyProdTask_result {I : Type} (f : I → FinTask (PolynomialExpr v)) (is : List I) :
    (legacyProdTask f is).result = Gen.ModelEncoding.Ordered.product (is.map (fun i => (f i).result)) := by
  induction is <;> simp_all [legacyProdTask,Gen.ModelEncoding.Ordered.product]

def toLegacyTask : PolyExpr v a → FinTask (PolynomialExpr (v+a))
  | .rat q => primitive (fun _ => .rational q)
  | .var i => primitive (fun _ => .var (Fin.castAdd a i))
  | .scalar i => primitive (fun _ => .var (Fin.natAdd v i))
  | .add p q => .step fun _ => do
      let p' ← toLegacyTask p
      let q' ← toLegacyTask q
      primitive (fun _ => .add p' q')
  | .mul p q => .step fun _ => do
      let p' ← toLegacyTask p
      let q' ← toLegacyTask q
      primitive (fun _ => .mul p' q')
  | .neg p => .step fun _ => do
      let p' ← toLegacyTask p
      primitive (fun _ => .neg p')
@[simp] theorem toLegacyTask_result (p : PolyExpr v a) : (toLegacyTask p).result = p.toLegacy := by
  induction p <;> simp_all [toLegacyTask,PolyExpr.toLegacy]

def fromLegacyTask : PolynomialExpr (v+a) → FinTask (PolyExpr v a)
  | .rational q => primitive (fun _ => .rat q)
  | .var i => primitive (fun _ => Fin.addCases (fun j => .var j) (fun j => .scalar j) i)
  | .add p q => .step fun _ => do
      let p' ← fromLegacyTask p
      let q' ← fromLegacyTask q
      primitive (fun _ => .add p' q')
  | .mul p q => .step fun _ => do
      let p' ← fromLegacyTask p
      let q' ← fromLegacyTask q
      primitive (fun _ => .mul p' q')
  | .neg p => .step fun _ => do
      let p' ← fromLegacyTask p
      primitive (fun _ => .neg p')
@[simp] theorem fromLegacyTask_result (p : PolynomialExpr (v+a)) :
    (fromLegacyTask p).result = PolyExpr.fromLegacy p := by
  induction p <;> simp_all [fromLegacyTask,PolyExpr.fromLegacy]

/-- Affine coordinates are generated node by node, including every omitted coordinate. -/
def expandBlockTask {k : ℕ} (u : Fin k → PolyExpr v a) (i : Fin (k+1)) : FinTask (PolyExpr v a) :=
  .step fun _ => Fin.lastCases
    (do let indices ← finRangeTask k
        let s ← sumTask (fun j => primitive (fun _ => u j)) indices
        let neg ← primitive (fun _ => PolyExpr.neg s)
        primitive (fun _ => PolyExpr.add (.rat 1) neg))
    (fun j => primitive (fun _ => u j)) i
@[simp] theorem expandBlockTask_result {k : ℕ} (u : Fin k → PolyExpr v a) (i : Fin (k+1)) :
    (expandBlockTask u i).result = Compiler.expandBlockExpr u i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [expandBlockTask,Compiler.expandBlockExpr,Compiler.sumExpr,Compiler.finEnumeration,PolyExpr.sub]

variable {G : Type} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {n : G → ℕ} {k : ℕ}

abbrev Coord := Gen.Geometry.Coordinate D (fun g => Fin (n g+1)) (k+1)
abbrev CoordTask := Coord (D := D) (n := n) (k := k) → FinTask (PolyExpr v a)

def coordinatesTask (u : Normalization.ReducedCoordinate D n k → PolyExpr v a) :
    CoordTask (D := D) (n := n) (k := k) (v := v) (a := a) := fun i =>
  match i with
  | .inl (c,z) => expandBlockTask (fun j => u (.inl (c,j))) z
  | .inr ⟨g,z,y⟩ => expandBlockTask (fun j => u (.inr ⟨g,z,j⟩)) y
@[simp] theorem coordinatesTask_result
    (u : Normalization.ReducedCoordinate D n k → PolyExpr v a) (i : Coord (D := D) (n := n) (k := k)) :
    (coordinatesTask u i).result = Compiler.expandNormalizedExpr D n k u i := by
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;> exact expandBlockTask_result _ _

def observationTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (X : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a))
    (e : D.Edge) (x : D.Outcome (fun g => Fin (n g+1)) e) : FinTask (PolynomialExpr (v+a)) :=
  legacySumTask (fun z => do
    let wn ← X (.inl (D.component e,z))
    let w ← toLegacyTask wn
    let product ← legacyProdTask (fun g : D.GroupAt e => do
      let pn ← X (.inr ⟨g.val,z,x g⟩)
      toLegacyTask pn) (E.edgeGroups e).values
    primitive (fun _ => .mul w product)) E.latent.values
@[simp] theorem observationTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (X : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a)) (e : D.Edge)
    (x : D.Outcome (fun g => Fin (n g+1)) e) :
    (observationTask E X e x).result = Gen.ModelEncoding.Ordered.observation E
      (fun i => (X i).result.toLegacy) e x := by
  simp [observationTask,Gen.ModelEncoding.Ordered.observation,sumExpr,prodExpr]

def objectiveTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a)) : FinTask (PolyExpr v a) := do
  let H ← legacySumTask (fun ex => do
    let p ← observationTask E X ex.1 ex.2
    let q ← observationTask E X' ex.1 ex.2
    let neg ← primitive (fun _ => PolynomialExpr.neg q)
    let diff ← primitive (fun _ => PolynomialExpr.add p neg)
    primitive (fun _ => PolynomialExpr.mul diff diff)) E.cells.values
  fromLegacyTask H
@[simp] theorem objectiveTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a)) :
    (objectiveTask E X X').result = Compiler.objective E (fun i => (X i).result) (fun i => (X' i).result) := by
  simp [objectiveTask,Compiler.objective,Gen.ModelEncoding.Ordered.H,sumExpr,
    PolynomialExpr.square,PolynomialExpr.sub]

def distanceTask (E : Compiler.Order (D := D) (n := n) (k := k)) (q : Gen.W D (k+1))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a)) : FinTask (PolyExpr v a) := do
  let F ← legacySumTask (fun i => do
    let pn ← X i
    let p ← toLegacyTask pn
    let qn ← X' (E.coordinatePullback q i)
    let qq ← toLegacyTask qn
    let neg ← primitive (fun _ => PolynomialExpr.neg qq)
    let diff ← primitive (fun _ => PolynomialExpr.add p neg)
    primitive (fun _ => PolynomialExpr.mul diff diff)) E.coordinates.values
  fromLegacyTask F
@[simp] theorem distanceTask_result (E : Compiler.Order (D := D) (n := n) (k := k)) (q : Gen.W D (k+1))
    (X X' : CoordTask (D := D) (n := n) (k := k) (v := v) (a := a)) :
    (distanceTask E q X X').result = Compiler.distance E q (fun i => (X i).result) (fun i => (X' i).result) := by
  simp [distanceTask,Compiler.distance,Gen.ModelEncoding.Ordered.distance,sumExpr,
    PolynomialExpr.square,PolynomialExpr.sub]

/-- A Gram matrix entry is compiled by an internally stepped output sum. -/
def gramTask (E : Compiler.Order (D := D) (n := n) (k := k))
    (X : CoordTask (D := D) (n := n) (k := k) (v := v) (a := 3))
    (g : G) (z z' : Fin (k+1)) : FinTask (PolyExpr v 3) := do
  let sum ← sumTask (fun y => do
    let p ← X (.inr ⟨g,z,y⟩)
    let q ← X (.inr ⟨g,z',y⟩)
    primitive (fun _ => PolyExpr.mul p q)) (E.outputs g).values
  let neg ← primitive (fun _ => PolyExpr.neg (if z = z' then .scalar 1 else .rat 0))
  primitive (fun _ => .add sum neg)
@[simp] theorem gramTask_result (E : Compiler.Order (D := D) (n := n) (k := k))
    (X : CoordTask (D := D) (n := n) (k := k) (v := v) (a := 3))
    (g : G) (z z' : Fin (k+1)) :
    (gramTask E X g z z').result = SquaredCompiler.gram E (fun i => (X i).result) g z z' := by
  simp [gramTask,SquaredCompiler.gram,Compiler.sumExpr,PolyExpr.sub]

variable {J : Type} [Fintype J] [DecidableEq J]
/-- The actual Leibniz determinant is generated term by term, then translated node by node. -/
def determinantTask (E : Enumeration J) (P : Enumeration (Equiv.Perm J))
    (A : J → J → FinTask (PolyExpr v a)) : FinTask (PolyExpr v a) := do
  let det ← legacySumTask (fun π => do
    let product ← legacyProdTask (fun i => do
      let p ← A (π i) i
      toLegacyTask p) E.values
    let sign ← FiniteEnumeration.signTask E π
    primitive (fun _ => PolynomialExpr.mul (.rational (sign : ℚ)) product)) P.values
  fromLegacyTask det
@[simp] theorem determinantTask_result (E : Enumeration J) (P : Enumeration (Equiv.Perm J))
    (A : J → J → FinTask (PolyExpr v a)) :
    (determinantTask E P A).result = Compiler.determinant E P (fun i j => (A i j).result) := by
  simp [determinantTask,FiniteEnumeration.signTask_result,Compiler.determinant,Gen.ModelEncoding.Ordered.determinant,sumExpr,prodExpr]

/-- Coded permutations expose every nested application and sign operation. -/
def determinantCodedTask (E : Enumeration J) (P : List (CodedPerm J))
    (A : J → J → FinTask (PolyExpr v a)) : FinTask (PolyExpr v a) := do
  let det ← legacySumTask (fun π => do
    let product ← legacyProdTask (fun i => do
      let row ← π.appTask i
      let p ← A row i
      toLegacyTask p) E.values
    let sign ← π.signTask
    primitive (fun _ => PolynomialExpr.mul (.rational (sign : ℚ)) product)) P
  fromLegacyTask det

@[simp] theorem determinantCodedTask_result (E : Enumeration J) (P : List (CodedPerm J))
    (legacy : Enumeration (Equiv.Perm J)) (hP : P.map CodedPerm.legacy=legacy.values)
    (A : J → J → FinTask (PolyExpr v a)) :
    (determinantCodedTask E P A).result = Compiler.determinant E legacy (fun i j => (A i j).result) := by
  simp only [determinantCodedTask,FinTask.result_bindM,legacySumTask_result,
    legacyProdTask_result,CodedPerm.appTask_result,CodedPerm.signTask_result,
    toLegacyTask_result,primitive_result,fromLegacyTask_result,
    Compiler.determinant,Gen.ModelEncoding.Ordered.determinant,sumExpr,prodExpr]
  rw [←hP,List.map_map]
  rfl

def principalTask (E : PrincipalOrdering J) (A : J → J → FinTask (PolyExpr v a)) :
    FinTask (List (PolyExpr v a)) := do
  let subsets ← filterTask (fun S => decide (S ≠ ∅)) E.subsets.values
  mapTask (fun S => determinantTask (E.indices S) (E.permutations S)
    (fun i j => A i.val j.val)) subsets
@[simp] theorem principalTask_result (E : PrincipalOrdering J) (A : J → J → FinTask (PolyExpr v a)) :
    (principalTask E A).result = Compiler.principalConstraints E (fun i j => (A i j).result) := by
  simp [principalTask,Compiler.principalConstraints,Matrix.submatrix]
  intro i hi; rfl

/-- The executable principal path uses directly computed entries, never a Finset-keyed
legacy family closure. The principal-subset order is retained exactly. -/
def canonicalPrincipal {r : ℕ} (E : PrincipalOrdering (Fin r)) : PrincipalOrdering (Fin r) where
  subsets := E.subsets
  indices := fun S => FiniteEnumeration.sorted
  permutations := fun S => FiniteEnumeration.permutations (FiniteEnumeration.sorted : Enumeration S)

def nonemptySubsetTask {I : Type} [DecidableEq I] (S : Finset I) : FinTask Bool := do
  let size ← finsetCardTask S
  primitive (fun _ => decide (size≠0))
@[simp] theorem nonemptySubsetTask_result {I : Type} [DecidableEq I] (S : Finset I) :
    (nonemptySubsetTask S).result = decide (S≠∅) := by
  simp [nonemptySubsetTask]

def principalSortedTask {r : ℕ} (E : PrincipalOrdering (Fin r))
    (A : Fin r → Fin r → FinTask (PolyExpr v a)) : FinTask (List (PolyExpr v a)) := do
  let base ← FiniteEnumeration.finEnumerationTask r
  let subsets ← filterByTask nonemptySubsetTask E.subsets.values
  mapTask (fun S => do
    let indices ← FiniteEnumeration.indicesTask base S
    let permutations ← FiniteEnumeration.codedPermutationsTask indices
    determinantCodedTask indices permutations (fun i j => A i.val j.val)) subsets

@[simp] theorem principalSortedTask_result {r : ℕ} (E : PrincipalOrdering (Fin r))
    (A : Fin r → Fin r → FinTask (PolyExpr v a)) :
    (principalSortedTask E A).result = Compiler.principalConstraints (canonicalPrincipal E)
      (fun i j => (A i j).result) := by
  simp only [principalSortedTask,FinTask.result_bindM,FiniteEnumeration.finEnumerationTask_result,
    FinTask.filterByTask_result,nonemptySubsetTask_result,FinTask.mapTask_result,FiniteEnumeration.indicesTask_result,
    Compiler.principalConstraints,canonicalPrincipal]
  congr 1
  funext S
  exact determinantCodedTask_result _ _ _ (FiniteEnumeration.codedPermutationsTask_legacy _) _

@[simp] theorem canonicalPrincipal_principal (r : ℕ) :
    canonicalPrincipal (FiniteEnumeration.principal r) = FiniteEnumeration.principal r := rfl

/-- Monadic retained coordinates expose index-search work before emitting variable nodes. -/
def expandBlockTaskM {t : ℕ} (u : Fin t → FinTask (PolyExpr v a)) (i : Fin (t+1)) :
    FinTask (PolyExpr v a) := .step fun _ => Fin.lastCases
  (do let indices ← finRangeTask t
      let s ← sumTask u indices
      let neg ← primitive (fun _ => PolyExpr.neg s)
      primitive (fun _ => PolyExpr.add (.rat 1) neg)) u i
@[simp] theorem expandBlockTaskM_result {t : ℕ} (u : Fin t → FinTask (PolyExpr v a))
    (i : Fin (t+1)) :
    (expandBlockTaskM u i).result = Compiler.expandBlockExpr (fun j => (u j).result) i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [expandBlockTaskM,Compiler.expandBlockExpr,Compiler.sumExpr,Compiler.finEnumeration,PolyExpr.sub]

def coordinatesTaskM (u : Normalization.ReducedCoordinate D n k → FinTask (PolyExpr v a)) :
    CoordTask (D := D) (n := n) (k := k) (v := v) (a := a) := fun i => match i with
  | .inl (c,z) => expandBlockTaskM (fun j => u (.inl (c,j))) z
  | .inr ⟨g,z,y⟩ => expandBlockTaskM (fun j => u (.inr ⟨g,z,j⟩)) y
@[simp] theorem coordinatesTaskM_result
    (u : Normalization.ReducedCoordinate D n k → FinTask (PolyExpr v a))
    (i : Coord (D := D) (n := n) (k := k)) :
    (coordinatesTaskM u i).result = Compiler.expandNormalizedExpr D n k (fun j => (u j).result) i := by
  rcases i with ⟨c,z⟩ | ⟨g,z,y⟩ <;> exact expandBlockTaskM_result _ _

end Cover.CompilerAstTasks
