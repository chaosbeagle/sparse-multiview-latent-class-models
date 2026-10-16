import Cover.ConcreteCompiler

open scoped BigOperators Classical
namespace Cover.ConstraintCounts
open Cover.Compiler Cover.FiniteEnumeration Gen.ModelEncoding.Ordered
variable {v a : ℕ}

theorem nonempty_principal_count {r : ℕ} (E : PrincipalOrdering (Fin r)) :
    (E.subsets.values.filter (fun S => S ≠ ∅)).length = 2^r - 1 := by
  rw [← List.toFinset_card_of_nodup (E.subsets.nodup.filter _)]
  have hs : (E.subsets.values.filter (fun S => S ≠ ∅)).toFinset =
      (Finset.univ : Finset (Finset (Fin r))).erase ∅ := by
    ext S; simp [E.subsets.complete S,ne_comm]
  rw [hs,Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

@[simp] theorem principalConstraints_length {r : ℕ} (E : PrincipalOrdering (Fin r))
    (A : Matrix (Fin r) (Fin r) (PolyExpr v a)) :
    (principalConstraints E A).length = 2^r - 1 := by
  simpa only [principalConstraints,List.length_map] using nonempty_principal_count E

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {n : G → ℕ} {k : ℕ}

@[simp] theorem weights_length (E : Order (D := D) (n := n) (k := k)) (w : PolyExpr v a)
    (X : CoordinateExpr D n k (v := v) (a := a)) :
    (weightConstraints E w X).length = Fintype.card D.Component * (k+1) := by
  simp [weightConstraints,List.length_flatMap,FiniteEnumeration.length_eq_card]

@[simp] theorem kernels_length (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := a)) :
    (kernelConstraints E X).length = (k+1) * ∑ g, (n g+1) := by
  simp [kernelConstraints,List.length_flatMap,FiniteEnumeration.length_eq_card,
    E.groups.sum_map,Finset.mul_sum]

@[simp] theorem grams_length (E : Order (D := D) (n := n) (k := k))
    (X : CoordinateExpr D n k (v := v) (a := 3)) :
    (SquaredCompiler.gramConstraints E X).length = Fintype.card G * (2^(k+1)-1) := by
  simp [SquaredCompiler.gramConstraints,List.length_flatMap,FiniteEnumeration.length_eq_card]

@[simp] theorem far_length (E : Order (D := D) (n := n) (k := k))
    (X X' : CoordinateExpr D n k (v := v) (a := 3)) :
    (SquaredCompiler.farConstraints E X X').length = ((k+1).factorial)^Fintype.card D.Component := by
  simp [SquaredCompiler.farConstraints,FiniteEnumeration.length_eq_card,
    Gen.W,Fintype.card_pi,Fintype.card_perm]

/-- Exact four family sizes: two copies of weight/kernel/Gram tests and every gauge test. -/
theorem constraints_length (E : Order (D := D) (n := n) (k := k))
    (u u' : Normalization.ReducedCoordinate D n k → PolyExpr v 3) :
    (SquaredCompiler.constraints E u u').length =
      2 * (k+1) * Fintype.card D.Component +
      2 * (k+1) * (∑ g, (n g+1)) +
      2 * Fintype.card G * (2^(k+1)-1) +
      ((k+1).factorial)^Fintype.card D.Component := by
  simp only [SquaredCompiler.constraints,SquaredCompiler.modelConstraints,List.length_append,
    weights_length,kernels_length,grams_length,far_length]
  ring
end Cover.ConstraintCounts
