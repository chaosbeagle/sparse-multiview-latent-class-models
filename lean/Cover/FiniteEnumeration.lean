import Cover.CompilerPrimitives
import Mathlib.Data.List.Pi

open scoped BigOperators
namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

def sorted {I : Type*} [Fintype I] [LinearOrder I] : Enumeration I where
  values := Finset.univ.sort (· ≤ ·)
  nodup := Finset.sort_nodup _ _
  complete i := by simp

/-- Canonical lexicographic order on finite sets, via their increasing element lists. -/
@[reducible] def finsetOrder {I : Type*} [LinearOrder I] : LinearOrder (Finset I) :=
  LinearOrder.lift' (fun s => s.sort (· ≤ ·)) (by
    intro s t h
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset h)

/-- Ordered enumeration is built from finite data and removes duplicate representations. -/
def ofCover {I : Type*} [DecidableEq I] (xs : List I) (h : ∀ i, i ∈ xs) : Enumeration I :=
  ⟨xs.dedup, List.nodup_dedup xs, fun i => List.mem_dedup.mpr (h i)⟩

def map {I J : Type*} [DecidableEq J] (E : Enumeration I) (f : I → J)
    (hf : Function.Surjective f) : Enumeration J :=
  ofCover (E.values.map f) (by
    intro j; obtain ⟨i,rfl⟩ := hf j; exact List.mem_map.mpr ⟨i,E.complete i,rfl⟩)

/-- Explicit dependent-product enumeration, including every cell and every gauge. -/
def pi {I : Type*} [Fintype I] [DecidableEq I] {J : I → Type*} [∀ i, DecidableEq (J i)]
    (E : Enumeration I) (F : ∀ i, Enumeration (J i)) : Enumeration (∀ i, J i) :=
  ofCover ((List.pi E.values (fun i => (F i).values)).map (fun f i => f i (E.complete i))) (by
    intro f
    refine List.mem_map.mpr ⟨fun i _ => f i, ?_, rfl⟩
    exact (List.mem_pi _ _).mpr (fun i _ => (F i).complete (f i)))

/-- Complete finite product without opaque choices. -/
def prod {I J : Type*} [DecidableEq I] [DecidableEq J]
    (E : Enumeration I) (F : Enumeration J) : Enumeration (I × J) :=
  ofCover (E.values.flatMap (fun i => F.values.map (fun j => (i,j)))) (by
    rintro ⟨i,j⟩
    exact List.mem_flatMap.mpr ⟨i,E.complete i,List.mem_map.mpr ⟨j,F.complete j,rfl⟩⟩)

def sigma {I : Type*} [DecidableEq I] {J : I → Type*} [∀ i, DecidableEq (J i)]
    (E : Enumeration I) (F : ∀ i, Enumeration (J i)) : Enumeration (Sigma J) :=
  ofCover (E.values.flatMap (fun i => (F i).values.map (fun j => Sigma.mk i j))) (by
    rintro ⟨i,j⟩
    exact List.mem_flatMap.mpr ⟨i,E.complete i,List.mem_map.mpr ⟨j,(F i).complete j,rfl⟩⟩)

def sum {I J : Type*} [DecidableEq I] [DecidableEq J]
    (E : Enumeration I) (F : Enumeration J) : Enumeration (I ⊕ J) :=
  ofCover (E.values.map Sum.inl ++ F.values.map Sum.inr) (by
    intro ij; cases ij <;> simp [E.complete,F.complete])

/-- Generate all permutations, then sort their literal value sequences lexicographically. -/
def permutations {I : Type*} [LinearOrder I] (E : Enumeration I) : Enumeration (Equiv.Perm I) where
  values := (permsOfList E.values).mergeSort
    (fun p q => decide (E.values.map p ≤ E.values.map q))
  nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (nodup_permsOfList E.nodup)
  complete p := (List.mergeSort_perm _ _).mem_iff.mpr
    (mem_permsOfList_of_mem (fun i _ => E.complete i))

theorem permutations_lexicographic {I : Type*} [LinearOrder I] (E : Enumeration I) :
    (permutations E).values.Pairwise (fun p q : Equiv.Perm I => E.values.map p ≤ E.values.map q) := by
  have h := List.pairwise_mergeSort
    (le := fun p q : Equiv.Perm I => decide (E.values.map p ≤ E.values.map q))
    (fun p q r hp hq => by simp only [decide_eq_true_eq] at *; exact hp.trans hq)
    (fun p q => by simp only [Bool.or_eq_true,decide_eq_true_eq]; exact le_total _ _)
    (permsOfList E.values)
  simpa only [permutations,decide_eq_true_eq] using h

theorem permutations_length {I : Type*} [LinearOrder I] (E : Enumeration I) :
    (permutations E).values.length = E.values.length.factorial := by
  simp [permutations,length_permsOfList]

/-- All principal subsets, each index list, and each determinant permutation are generated. -/
def principal (r : ℕ) : PrincipalOrdering (Fin r) := by
  letI := finsetOrder (I := Fin r)
  exact { subsets := sorted
          indices := fun S => sorted
          permutations := fun S => permutations (sorted : Enumeration S) }

/-- A literal enumeration induces its computable index bijection. -/
def indexEquiv {I : Type*} [DecidableEq I] (E : Enumeration I) : Fin E.values.length ≃ I :=
  (List.Nodup.getEquiv E.values E.nodup).trans (Equiv.subtypeUnivEquiv E.complete)

theorem length_eq_card {I : Type*} [Fintype I] (E : Enumeration I) : E.values.length = Fintype.card I := by
  classical
  exact (Fintype.card_fin _).symm.trans (Fintype.card_congr (indexEquiv E))
end Cover.FiniteEnumeration
