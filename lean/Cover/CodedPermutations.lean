import Cover.EnumerationTasks

namespace Cover

/-- Finite permutation syntax; composition has the same left/right convention as
Equiv.Perm multiplication: compose p q applies q first, then p. -/
inductive PermCode (I : Type) where
  | identity : PermCode I
  | swap : I → I → PermCode I
  | compose : PermCode I → PermCode I → PermCode I
  deriving DecidableEq, Repr

namespace PermCode

def eval {I : Type} [DecidableEq I] : PermCode I → Equiv.Perm I
  | .identity => 1
  | .swap i j => Equiv.swap i j
  | .compose p q => p.eval * q.eval

/-- Every nested composition and swap lookup is interpreted by explicit steps. -/
def appTask {I : Type} [DecidableEq I] : PermCode I → I → FinTask I
  | .identity,i => .step fun _ => .done i
  | .swap a b,i => .step fun _ => if i=a then .done b else
      .step fun _ => .done (if i=b then a else i)
  | .compose p q,i => .step fun _ => do
      let j ← appTask q i
      appTask p j

@[simp] theorem appTask_result {I : Type} [DecidableEq I] (p : PermCode I) (i : I) :
    (p.appTask i).result = p.eval i := by
  induction p generalizing i with
  | identity => rfl
  | swap a b =>
      simp only [appTask,FinTask.result_step,eval,Equiv.swap_apply_def]
      split_ifs <;> rfl
  | compose p q hp hq => simp [appTask,hp,hq,eval,Equiv.Perm.mul_apply]

/-- Sign follows the finite syntax, not an opaque application of Equiv.Perm.sign. -/
def signTask {I : Type} [DecidableEq I] : PermCode I → FinTask ℤ
  | .identity => .step fun _ => .done 1
  | .swap a b => .step fun _ => .done (if a=b then 1 else -1)
  | .compose p q => .step fun _ => do
      let a ← signTask p
      let b ← signTask q
      FinTask.primitive (fun _ => a*b)

@[simp] theorem signTask_result {I : Type} [DecidableEq I] [Fintype I] (p : PermCode I) :
    p.signTask.result = (Equiv.Perm.sign p.eval : ℤ) := by
  induction p with
  | identity => simp [signTask,eval]
  | swap a b =>
      by_cases h : a=b <;> simp [signTask,eval,Equiv.Perm.sign_swap',h]
  | compose p q hp hq => simp [signTask,eval,hp,hq]

/-- Cached legacy permutation values are also constructed node-by-node. Building
these closures never evaluates a nested permutation application. -/
def evalTask {I : Type} [DecidableEq I] : PermCode I → FinTask (Equiv.Perm I)
  | .identity => .step fun _ => .done 1
  | .swap a b => .step fun _ => .done (Equiv.swap a b)
  | .compose p q => .step fun _ => do
      let a ← evalTask p
      let b ← evalTask q
      FinTask.primitive (fun _ => a*b)

@[simp] theorem evalTask_result {I : Type} [DecidableEq I] (p : PermCode I) : p.evalTask.result=p.eval := by
  induction p <;> simp_all [evalTask,eval]

theorem appTask_zero_unknown {I : Type} [DecidableEq I] (p : PermCode I) (i : I) :
    FinTask.run 0 (p.appTask i) = none := by cases p <;> rfl

theorem signTask_zero_unknown {I : Type} [DecidableEq I] (p : PermCode I) :
    FinTask.run 0 p.signTask = none := by cases p <;> rfl

end PermCode

/-- Ordinary finite code with a cached legacy value and an erased exact bridge.
The executable consumers below use code, never the cached function application. -/
structure CodedPerm (I : Type) [DecidableEq I] where
  legacy : Equiv.Perm I
  code : PermCode I
  correct : legacy=code.eval

namespace CodedPerm

def ofCodeTask {I : Type} [DecidableEq I] (p : PermCode I) : FinTask (CodedPerm I) := do
  let value ← p.evalTask.attach
  .step fun _ => .done ⟨value.val,p,value.property.trans (PermCode.evalTask_result p)⟩

@[simp] theorem ofCodeTask_result_legacy {I : Type} [DecidableEq I] (p : PermCode I) :
    (ofCodeTask p).result.legacy = p.eval := by
  simp [ofCodeTask]
@[simp] theorem ofCodeTask_result_code {I : Type} [DecidableEq I] (p : PermCode I) :
    (ofCodeTask p).result.code = p := by
  simp [ofCodeTask]

def appTask {I : Type} [DecidableEq I] (p : CodedPerm I) (i : I) : FinTask I := p.code.appTask i
@[simp] theorem appTask_result {I : Type} [DecidableEq I] (p : CodedPerm I) (i : I) :
    (p.appTask i).result=p.legacy i := by rw [appTask,PermCode.appTask_result,←p.correct]

def signTask {I : Type} [DecidableEq I] (p : CodedPerm I) : FinTask ℤ := p.code.signTask
@[simp] theorem signTask_result {I : Type} [DecidableEq I] [Fintype I] (p : CodedPerm I) :
    p.signTask.result=(Equiv.Perm.sign p.legacy : ℤ) := by rw [signTask,PermCode.signTask_result,←p.correct]

end CodedPerm
end Cover

namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

/-- Ordinary finite syntax list matching the exact permsOfList insertion order.
It is a specification of the stepped generator below, not a task precomputation. -/
def permutationCodesOfList {I : Type} : List I → List (PermCode I)
  | [] => [.identity]
  | a::as => permutationCodesOfList as ++ as.flatMap (fun b =>
      (permutationCodesOfList as).map (fun p => .compose (.swap a b) p))

def permutationCodesOfListTask {I : Type} : List I → FinTask (List (PermCode I))
  | [] => .step fun _ => .done [.identity]
  | a::as => .step fun _ => do
      let tail ← permutationCodesOfListTask as
      let rest ← FinTask.flatMapTask (fun b => do
        let swap ← FinTask.primitive (fun _ => PermCode.swap a b)
        FinTask.mapTask (fun p => FinTask.primitive (fun _ => PermCode.compose swap p)) tail) as
      FinTask.appendTask tail rest

@[simp] theorem permutationCodesOfListTask_result {I : Type} (xs : List I) :
    (permutationCodesOfListTask xs).result = permutationCodesOfList xs := by
  induction xs <;> simp_all [permutationCodesOfListTask,permutationCodesOfList]

theorem permutationCodesOfList_eval {I : Type} [DecidableEq I] (xs : List I) :
    (permutationCodesOfList xs).map PermCode.eval = permsOfList xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp only [permutationCodesOfList,List.map_append,List.map_flatMap,List.map_map,PermCode.eval,
        permsOfList.eq_2,ih]
      congr 1
      apply congrArg (List.flatMap · as)
      funext b
      rw [←ih]
      simp only [List.map_map,Function.comp_def,PermCode.eval]

/-- Lexicographic ordering evaluates each code through appTask. No cached legacy
permutation is applied, including during mergeSort comparison. -/
def permutationCodeLETask {I : Type} [LinearOrder I] (E : Enumeration I)
    (p q : PermCode I) : FinTask Bool := do
  let ps ← FinTask.mapTask (fun i => p.appTask i) E.values
  let qs ← FinTask.mapTask (fun i => q.appTask i) E.values
  FinTask.lexLETask ps qs

@[simp] theorem permutationCodeLETask_result {I : Type} [LinearOrder I] (E : Enumeration I)
    (p q : PermCode I) : (permutationCodeLETask E p q).result =
      decide (E.values.map p.eval ≤ E.values.map q.eval) := by
  simp [permutationCodeLETask]

def permutationCodesTask {I : Type} [LinearOrder I] (E : Enumeration I) : FinTask (List (PermCode I)) := do
  let codes ← permutationCodesOfListTask E.values
  FinTask.mergeSortTask (permutationCodeLETask E) codes

theorem permutationCodesTask_eval {I : Type} [LinearOrder I] (E : Enumeration I) :
    (permutationCodesTask E).result.map PermCode.eval = (permutations E).values := by
  simp only [permutationCodesTask,FinTask.result_bindM,permutationCodesOfListTask_result,
    FinTask.mergeSortTask_result]
  rw [List.map_mergeSort (f := PermCode.eval)
    (s := fun p q : Equiv.Perm I => decide (E.values.map p ≤ E.values.map q))
    (fun p _ q _ => permutationCodeLETask_result E p q)]
  rw [permutationCodesOfList_eval]
  rfl

/-- Entries carry code and an already stepped cached legacy value, in exactly the
existing permutation enumeration's order. Runtime application/sign use only code. -/
def codedPermutationsTask {I : Type} [LinearOrder I] (E : Enumeration I) : FinTask (List (CodedPerm I)) := do
  let codes ← permutationCodesTask E
  FinTask.mapTask CodedPerm.ofCodeTask codes

@[simp] theorem codedPermutationsTask_legacy {I : Type} [LinearOrder I] (E : Enumeration I) :
    (codedPermutationsTask E).result.map CodedPerm.legacy = (permutations E).values := by
  simp only [codedPermutationsTask,FinTask.result_bindM,FinTask.mapTask_result,List.map_map,
    Function.comp_def,CodedPerm.ofCodeTask_result_legacy]
  exact permutationCodesTask_eval E

theorem codedPermutationsTask_complete {I : Type} [LinearOrder I]
    (E : Enumeration I) (π : Equiv.Perm I) :
    ∃ p ∈ (codedPermutationsTask E).result,p.legacy=π := by
  apply List.mem_map.mp
  rw [codedPermutationsTask_legacy]
  exact (permutations E).complete π

theorem codedPermutationsTask_nodup {I : Type} [LinearOrder I] (E : Enumeration I) :
    (codedPermutationsTask E).result.Nodup := by
  apply List.Nodup.of_map CodedPerm.legacy
  rw [codedPermutationsTask_legacy]
  exact (permutations E).nodup

theorem codedPermutationsTask_run_legacy {I : Type} [LinearOrder I]
    (E : Enumeration I) (fuel : ℕ) (ps : List (CodedPerm I))
    (hr : FinTask.run fuel (codedPermutationsTask E) = some ps) :
    ps.map CodedPerm.legacy = (permutations E).values := by
  have h := FinTask.run_sound fuel _ _ hr
  rw [←h,codedPermutationsTask_legacy]

end Cover.FiniteEnumeration

namespace Cover.CodedPerm

theorem appTask_run_correct {I : Type} [DecidableEq I] (p : CodedPerm I)
    (i j : I) (fuel : ℕ) (hr : FinTask.run fuel (p.appTask i) = some j) : j=p.legacy i := by
  have h := FinTask.run_sound fuel _ _ hr
  rw [appTask_result] at h
  exact h.symm

theorem signTask_run_correct {I : Type} [DecidableEq I] [Fintype I] (p : CodedPerm I)
    (z : ℤ) (fuel : ℕ) (hr : FinTask.run fuel p.signTask = some z) : z=(Equiv.Perm.sign p.legacy : ℤ) := by
  have h := FinTask.run_sound fuel _ _ hr
  rw [signTask_result] at h
  exact h.symm

end Cover.CodedPerm
