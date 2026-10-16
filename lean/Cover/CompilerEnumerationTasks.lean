import Cover.CodedPermutations

namespace Cover.CompilerEnumerationTasks
open Cover.FinTask Cover.FiniteEnumeration Gen.ModelEncoding.Ordered

/-- The code list, all legacy closure nodes and list traversal are constructed in tasks. -/
def permutationEnumerationTask {I : Type} [LinearOrder I] (E : Enumeration I) :
    FinTask (Enumeration (Equiv.Perm I)) := do
  let codes ← certify (codedPermutationsTask E)
  let values ← certify (mapTask (fun p : CodedPerm I => primitive (fun _ => p.legacy)) codes.val)
  have hv : values.val = (permutations E).values := by
    rw [values.property,mapTask_result]
    simp only [primitive_result]
    rw [codes.property,codedPermutationsTask_legacy]
  .step fun _ => .done ⟨values.val,hv.symm ▸ (permutations E).nodup,
    fun p => hv.symm ▸ (permutations E).complete p⟩
@[simp] theorem permutationEnumerationTask_result {I : Type} [LinearOrder I] (E : Enumeration I) :
    (permutationEnumerationTask E).result = permutations E := by
  apply enumeration_ext
  simp [permutationEnumerationTask]

def principalEntryCodedTask {I : Type} [Fintype I] [LinearOrder I]
    (E : Enumeration I) (S : Finset I) :
    FinTask (Enumeration S × Enumeration (Equiv.Perm S)) := do
  let indices ← indicesTask E S
  let perms ← permutationEnumerationTask indices
  .done (indices,perms)
@[simp] theorem principalEntryCodedTask_result {I : Type} [Fintype I] [LinearOrder I]
    (E : Enumeration I) (S : Finset I) :
    (principalEntryCodedTask E S).result =
      (sorted,permutations (sorted : Enumeration S)) := by simp [principalEntryCodedTask]

def principalOrderingTask (r : ℕ) : FinTask (PrincipalOrdering (Fin r)) := do
  let base ← finEnumerationTask r
  let subs ← subsetsTask base
  let entries ← dependentTask subs (principalEntryCodedTask base)
  .step fun _ => .done {
    subsets := subs
    indices := fun S => (entries S).1
    permutations := fun S => (entries S).2 }
@[simp] theorem principalOrderingTask_result (r : ℕ) :
    (principalOrderingTask r).result = principal r := by simp [principalOrderingTask,principal]

private theorem fullRawNodup {I : Type} [Fintype I] [DecidableEq I]
    (xs : List I) (hc : ∀ i,i∈xs) (hl : xs.length=Fintype.card I) : xs.Nodup := by
  have hu : xs.toFinset=Finset.univ := by ext i; simp [hc i]
  apply List.dedup_eq_self.mp
  apply (List.dedup_sublist xs).eq_of_length
  rw [←List.card_toFinset,hu,Finset.card_univ,hl]

private theorem sigmaRawNodup {I : Type} [DecidableEq I] {J : I → Type} [∀ i,DecidableEq (J i)]
    (E : Enumeration I) (F : ∀ i,Enumeration (J i)) :
    (E.values.flatMap (fun i => (F i).values.map (fun j => Sigma.mk i j))).Nodup := by
  classical
  letI : Fintype I := Fintype.ofList E.values E.complete
  letI : ∀ i,Fintype (J i) := fun i => Fintype.ofList (F i).values (F i).complete
  apply fullRawNodup _
    (by rintro ⟨i,j⟩; exact List.mem_flatMap.mpr ⟨i,E.complete i,List.mem_map.mpr ⟨j,(F i).complete j,rfl⟩⟩)
  simp [List.length_flatMap,List.length_map,E.sum_map,Fintype.card_sigma,length_eq_card]

/-- Task-valued families avoid applying a cached key-search closure during products. -/
def sigmaWithTask {I : Type} [DecidableEq I] {J : I → Type} [∀ i,DecidableEq (J i)]
    (E : Enumeration I) (F : (i : I) → FinTask (Enumeration (J i))) : FinTask (Enumeration (Sigma J)) := do
  let xs ← certify (flatMapTask (fun i => do
    let row ← F i
    mapTask (fun j => primitive (fun _ => Sigma.mk i j)) row.values) E.values)
  have hx : xs.val = E.values.flatMap (fun i => (F i).result.values.map (Sigma.mk i)) := by
    rw [xs.property]
    simp
  .step fun _ => .done ⟨xs.val, hx.symm ▸ sigmaRawNodup E (fun i => (F i).result), by
    rintro ⟨i,j⟩
    rw [hx]
    exact List.mem_flatMap.mpr ⟨i,E.complete i,List.mem_map.mpr ⟨j,(F i).result.complete j,rfl⟩⟩⟩
@[simp] theorem sigmaWithTask_result {I : Type} [DecidableEq I] {J : I → Type} [∀ i,DecidableEq (J i)]
    (E : Enumeration I) (F : (i : I) → FinTask (Enumeration (J i))) :
    (sigmaWithTask E F).result = sigma E (fun i => (F i).result) := by
  apply enumeration_ext
  simp [sigmaWithTask,sigma,ofCover,List.dedup_eq_self.mpr (sigmaRawNodup E (fun i => (F i).result))]

end Cover.CompilerEnumerationTasks
