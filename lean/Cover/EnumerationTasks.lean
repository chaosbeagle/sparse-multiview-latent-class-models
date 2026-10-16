import Cover.FiniteEnumeration
import Cover.FiniteTasks
import Cover.AlgebraicPrimitiveTasks

namespace Cover.FinTask

theorem steps_bind {α β : Type} (p : FinTask α) (f : α → FinTask β) :
    (p >>= f).steps = p.steps + (f p.result).steps := by
  change (FinTask.bind p f).steps = _
  induction p with
  | done a => simp [FinTask.bind,steps,result]
  | step next ih => simp only [FinTask.bind,steps,result,ih];omega

@[simp] theorem primitive_steps {α : Type} (f : Unit → α) : (primitive f).steps = 1 := rfl

/-- Unary finite tasks are determined by their finite transition count and result. -/
theorem eq_of_steps_result {α : Type} (p q : FinTask α)
    (hs : p.steps=q.steps) (hr : p.result=q.result) : p=q := by
  induction p generalizing q with
  | done a =>
      cases q with
      | done b => cases hr;rfl
      | step next => simp only [steps] at hs;omega
  | step next ih =>
      cases q with
      | done b => simp only [steps] at hs;omega
      | step next' =>
          congr 1
          funext u
          cases u
          apply ih ()
          · simpa only [steps,Nat.add_right_cancel_iff] using hs
          · exact hr

/-- Scan every list cell, so result and cost are invariant under permutation. -/
def memListTask {α : Type} [DecidableEq α] (a : α) : List α → FinTask Bool
  | [] => .step fun _ => .done false
  | b::bs => .step fun _ => do
      let seen ← memListTask a bs
      primitive (fun _ => decide (a=b) || seen)
@[simp] theorem memListTask_result {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    (memListTask a xs).result = decide (a∈xs) := by
  induction xs <;> simp_all [memListTask]
@[simp] theorem memListTask_steps {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    (memListTask a xs).steps = 2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp only [memListTask,steps,steps_bind,primitive_steps,ih,List.length_cons]
      omega

/-- Computable quotient lifting is justified by exact task equality, including
step count. No representative is chosen or extracted. -/
def multisetMemTask {α : Type} [DecidableEq α] (a : α) (s : Multiset α) : FinTask Bool :=
  Quotient.liftOn s (memListTask a) (by
    intro xs ys h
    apply eq_of_steps_result
    · simp only [memListTask_steps,h.length_eq]
    · simp only [memListTask_result]
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (h.mem_iff (a := a)))
@[simp] theorem multisetMemTask_result {α : Type} [DecidableEq α] (a : α) (s : Multiset α) :
    (multisetMemTask a s).result = decide (a∈s) := by
  induction s using Quotient.inductionOn with
  | h xs => exact memListTask_result a xs

def finsetMemTask {α : Type} [DecidableEq α] (a : α) (s : Finset α) : FinTask Bool :=
  multisetMemTask a s.val
@[simp] theorem finsetMemTask_result {α : Type} [DecidableEq α] (a : α) (s : Finset α) :
    (finsetMemTask a s).result = decide (a∈s) := multisetMemTask_result a s.val

def finsetInsertTask {α : Type} [DecidableEq α] (a : α) (s : Finset α) : FinTask (Finset α) := do
  let seen ← (finsetMemTask a s).attach
  .step fun _ => if h : seen.val=true then .done s else
    have hn : a∉s := by
      have he := seen.property.trans (finsetMemTask_result a s)
      intro hm
      exact h (he.trans (decide_eq_true hm))
    primitive (fun _ => Finset.cons a s hn)
@[simp] theorem finsetInsertTask_result {α : Type} [DecidableEq α] (a : α) (s : Finset α) :
    (finsetInsertTask a s).result = insert a s := by
  simp only [finsetInsertTask,result_bindM,attach_result,finsetMemTask_result,result_step]
  by_cases h : a∈s
  · simp [h,Finset.insert_eq_of_mem h]
  · simp [h,Finset.cons_eq_insert]

def filterByTask {α : Type} (test : α → FinTask Bool) : List α → FinTask (List α)
  | [] => .step fun _ => .done []
  | a::as => .step fun _ => do
      let rest ← filterByTask test as
      let keep ← test a
      .step fun _ => .done (if keep then a::rest else rest)
@[simp] theorem filterByTask_result {α : Type} (test : α → FinTask Bool) (xs : List α) :
    (filterByTask test xs).result = xs.filter (fun a => (test a).result) := by
  induction xs <;> simp_all [filterByTask,List.filter_cons]

def dedupTask {α : Type} [DecidableEq α] : List α → FinTask (List α)
  | [] => .step fun _ => .done []
  | a::as => .step fun _ => do
      let bs ← dedupTask as
      let seen ← anyTask (fun b => primitive (fun _ => decide (a=b))) as
      .step fun _ => .done (if seen then bs else a::bs)

@[simp] theorem dedupTask_result {α : Type} [DecidableEq α] (as : List α) :
    (dedupTask as).result = as.dedup := by
  induction as with
  | nil => simp [dedupTask]
  | cons a as ih =>
      by_cases ha : a ∈ as <;> simp [dedupTask,ih,List.dedup_cons,ha]

def dependentListTask {I : Type} [DecidableEq I] {J : I → Type}
    (f : ∀ i, FinTask (J i)) : (xs : List I) → FinTask (∀ i, i ∈ xs → J i)
  | [] => .step fun _ => .done (List.Pi.nil J)
  | i::is => .step fun _ => do
      let a ← f i
      let as ← dependentListTask f is
      .step fun _ => .done (List.Pi.cons i is a as)

theorem dependentListTask_result {I : Type} [DecidableEq I] {J : I → Type}
    (f : ∀ i, FinTask (J i)) (xs : List I) (i : I) (hi : i ∈ xs) :
    (dependentListTask f xs).result i hi = (f i).result := by
  induction xs with
  | nil => simp at hi
  | cons k ks ih =>
      simp only [dependentListTask,result_step,result_bindM,result_done,List.Pi.cons_def]
      split_ifs with h
      · subst i; rfl
      · exact ih ((List.mem_cons.mp hi).resolve_left h)

end Cover.FinTask

namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

theorem enumeration_ext {I : Type} {E F : Enumeration I} (h : E.values = F.values) : E = F := by
  cases E
  cases F
  cases h
  rfl

def ofCoverTask {I : Type} [DecidableEq I] (xs : List I) (h : ∀ i, i ∈ xs) : FinTask (Enumeration I) := do
  let ys ← (FinTask.dedupTask xs).attach
  .step fun _ => .done ⟨ys.val,
    by rw [ys.property,FinTask.dedupTask_result]; exact List.nodup_dedup xs,
    by intro i; rw [ys.property,FinTask.dedupTask_result]; exact List.mem_dedup.mpr (h i)⟩

@[simp] theorem ofCoverTask_result {I : Type} [DecidableEq I] (xs : List I) (h : ∀ i, i ∈ xs) :
    (ofCoverTask xs h).result = ofCover xs h := by
  apply enumeration_ext
  simp [ofCoverTask,ofCover]

def dependentTask {I : Type} [DecidableEq I] {J : I → Type}
    (E : Enumeration I) (f : ∀ i, FinTask (J i)) : FinTask (∀ i,J i) := do
  let vals ← FinTask.dependentListTask f E.values
  .step fun _ => .done (fun i => vals i (E.complete i))

@[simp] theorem dependentTask_result {I : Type} [DecidableEq I] {J : I → Type}
    (E : Enumeration I) (f : ∀ i, FinTask (J i)) :
    (dependentTask E f).result = fun i => (f i).result := by
  simp only [dependentTask,FinTask.result_bindM,FinTask.result_step,FinTask.result_done]
  funext i
  exact FinTask.dependentListTask_result f E.values i (E.complete i)

/-- Complete raw lists of the exact finite cardinality cannot contain duplicates. -/
private theorem raw_nodup_of_complete_length {I : Type} [Fintype I] [DecidableEq I]
    (xs : List I) (hc : ∀ i,i∈xs) (hl : xs.length=Fintype.card I) : xs.Nodup := by
  have hu : xs.toFinset=Finset.univ := by ext i; simp [hc i]
  apply List.dedup_eq_self.mp
  apply (List.dedup_sublist xs).eq_of_length
  rw [← List.card_toFinset,hu,Finset.card_univ,hl]

/-- No equality test is executed when the raw generator already proves nodup. -/
def ofNodupTask {I : Type} [DecidableEq I] (xs : List I) (hn : xs.Nodup)
    (hc : ∀ i,i∈xs) : FinTask (Enumeration I) := .step fun _ => .done ⟨xs,hn,hc⟩
@[simp] theorem ofNodupTask_result {I : Type} [DecidableEq I] (xs : List I) (hn : xs.Nodup)
    (hc : ∀ i,i∈xs) : (ofNodupTask xs hn hc).result = ofCover xs hc := by
  apply enumeration_ext
  simp [ofNodupTask,ofCover,List.dedup_eq_self.mpr hn]

private theorem prodRaw_nodup {I J : Type} [DecidableEq I] [DecidableEq J]
    (E : Enumeration I) (F : Enumeration J) :
    (E.values.flatMap (fun i => F.values.map (fun j => (i,j)))).Nodup := by
  classical
  letI : Fintype I := Fintype.ofList E.values E.complete
  letI : Fintype J := Fintype.ofList F.values F.complete
  apply raw_nodup_of_complete_length _
    (by rintro ⟨i,j⟩; exact List.mem_flatMap.mpr ⟨i,E.complete i,List.mem_map.mpr ⟨j,F.complete j,rfl⟩⟩)
  simp [List.length_flatMap,List.length_map,E.sum_map,Fintype.card_prod,length_eq_card]

private theorem sigmaRaw_nodup {I : Type} [DecidableEq I] {J : I → Type} [∀ i,DecidableEq (J i)]
    (E : Enumeration I) (F : ∀ i,Enumeration (J i)) :
    (E.values.flatMap (fun i => (F i).values.map (fun j => Sigma.mk i j))).Nodup := by
  classical
  letI : Fintype I := Fintype.ofList E.values E.complete
  letI : ∀ i,Fintype (J i) := fun i => Fintype.ofList (F i).values (F i).complete
  apply raw_nodup_of_complete_length _
    (by rintro ⟨i,j⟩; exact List.mem_flatMap.mpr ⟨i,E.complete i,List.mem_map.mpr ⟨j,(F i).complete j,rfl⟩⟩)
  simp [List.length_flatMap,List.length_map,E.sum_map,Fintype.card_sigma,length_eq_card]

private theorem sumRaw_nodup {I J : Type} [DecidableEq I] [DecidableEq J]
    (E : Enumeration I) (F : Enumeration J) :
    (E.values.map Sum.inl ++ F.values.map Sum.inr : List (I⊕J)).Nodup := by
  classical
  letI : Fintype I := Fintype.ofList E.values E.complete
  letI : Fintype J := Fintype.ofList F.values F.complete
  apply raw_nodup_of_complete_length _ (by intro i;cases i <;> simp [E.complete,F.complete])
  simp [Fintype.card_sum,length_eq_card]

private theorem length_piList {I : Type} [DecidableEq I] {J : I → Type}
    (xs : List I) (F : ∀ i,List (J i)) :
    (List.pi xs F).length=(xs.map (fun i => (F i).length)).prod := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp [List.pi_cons,List.length_flatMap,ih]

private theorem piRaw_nodup {I : Type} [Fintype I] [DecidableEq I]
    {J : I → Type} [∀ i,DecidableEq (J i)] (E : Enumeration I) (F : ∀ i,Enumeration (J i)) :
    ((List.pi E.values (fun i => (F i).values)).map (fun f i => f i (E.complete i))).Nodup := by
  classical
  letI : ∀ i,Fintype (J i) := fun i => Fintype.ofList (F i).values (F i).complete
  apply raw_nodup_of_complete_length _
    (by intro f;refine List.mem_map.mpr ⟨fun i _ => f i,?_,rfl⟩
        exact (List.mem_pi _ _).mpr (fun i _ => (F i).complete (f i)))
  simp only [List.length_map,length_piList,E.prod_map,Fintype.card_pi]
  exact Finset.prod_congr rfl (fun i _ => length_eq_card (F i))

def prodTask {I J : Type} [DecidableEq I] [DecidableEq J]
    (E : Enumeration I) (F : Enumeration J) : FinTask (Enumeration (I×J)) := do
  let xs ← (FinTask.flatMapTask (fun i => FinTask.mapTask (fun j => FinTask.primitive (fun _ => (i,j))) F.values) E.values).attach
  ofNodupTask xs.val (by
    rw [xs.property,FinTask.flatMapTask_result]
    simp only [FinTask.mapTask_result,FinTask.primitive_result]
    exact prodRaw_nodup E F) (by
    intro ⟨i,j⟩
    rw [xs.property,FinTask.flatMapTask_result]
    simp only [FinTask.mapTask_result,FinTask.primitive_result]
    exact List.mem_flatMap.mpr ⟨i,E.complete i,List.mem_map.mpr ⟨j,F.complete j,rfl⟩⟩)

@[simp] theorem prodTask_result {I J : Type} [DecidableEq I] [DecidableEq J]
    (E : Enumeration I) (F : Enumeration J) : (prodTask E F).result = prod E F := by
  apply enumeration_ext
  simp [prodTask,prod,ofCover]

def sigmaTask {I : Type} [DecidableEq I] {J : I → Type} [∀ i, DecidableEq (J i)]
    (E : Enumeration I) (F : ∀ i, Enumeration (J i)) : FinTask (Enumeration (Sigma J)) := do
  let xs ← (FinTask.flatMapTask (fun i => FinTask.mapTask
    (fun j => FinTask.primitive (fun _ => Sigma.mk i j)) (F i).values) E.values).attach
  ofNodupTask xs.val (by
    rw [xs.property,FinTask.flatMapTask_result]
    simp only [FinTask.mapTask_result,FinTask.primitive_result]
    exact sigmaRaw_nodup E F) (by
    intro ⟨i,j⟩
    rw [xs.property,FinTask.flatMapTask_result]
    simp only [FinTask.mapTask_result,FinTask.primitive_result]
    exact List.mem_flatMap.mpr ⟨i,E.complete i,List.mem_map.mpr ⟨j,(F i).complete j,rfl⟩⟩)

@[simp] theorem sigmaTask_result {I : Type} [DecidableEq I] {J : I → Type} [∀ i, DecidableEq (J i)]
    (E : Enumeration I) (F : ∀ i, Enumeration (J i)) : (sigmaTask E F).result = sigma E F := by
  apply enumeration_ext
  simp [sigmaTask,sigma,ofCover]

def sumValuesTask {I J : Type} (E : Enumeration I) (F : Enumeration J) : FinTask (List (I⊕J)) := do
  let ls ← FinTask.mapTask (fun i => FinTask.primitive (fun _ => Sum.inl i)) E.values
  let rs ← FinTask.mapTask (fun j => FinTask.primitive (fun _ => Sum.inr j)) F.values
  FinTask.appendTask ls rs

@[simp] theorem sumValuesTask_result {I J : Type} (E : Enumeration I) (F : Enumeration J) :
    (sumValuesTask E F).result = E.values.map Sum.inl ++ F.values.map Sum.inr := by
  simp [sumValuesTask]

def sumTask {I J : Type} [DecidableEq I] [DecidableEq J]
    (E : Enumeration I) (F : Enumeration J) : FinTask (Enumeration (I⊕J)) := do
  let xs ← (sumValuesTask E F).attach
  ofNodupTask xs.val (by
    rw [xs.property,sumValuesTask_result]
    exact sumRaw_nodup E F) (by
    intro ij
    rw [xs.property,sumValuesTask_result]
    cases ij <;> simp [E.complete,F.complete])

@[simp] theorem sumTask_result {I J : Type} [DecidableEq I] [DecidableEq J]
    (E : Enumeration I) (F : Enumeration J) : (sumTask E F).result = sum E F := by
  apply enumeration_ext
  simp [sumTask,sum,ofCover]

def piListTask {I : Type} [DecidableEq I] {J : I → Type}
    (F : ∀ i, List (J i)) : (xs : List I) → FinTask (List (∀ i, i ∈ xs → J i))
  | [] => .step fun _ => .done [List.Pi.nil J]
  | i::is => .step fun _ => do
      let tails ← piListTask F is
      FinTask.flatMapTask (fun b => FinTask.mapTask
        (fun f => FinTask.primitive (fun _ => List.Pi.cons i is b f)) tails) (F i)

@[simp] theorem piListTask_result {I : Type} [DecidableEq I] {J : I → Type}
    (F : ∀ i, List (J i)) (xs : List I) : (piListTask F xs).result = List.pi xs F := by
  induction xs with
  | nil => rfl
  | cons i is ih => simp [piListTask,ih,List.pi_cons]

def piValuesTask {I : Type} [DecidableEq I] {J : I → Type}
    (E : Enumeration I) (F : ∀ i, Enumeration (J i)) : FinTask (List (∀ i,J i)) := do
  let xs ← piListTask (fun i => (F i).values) E.values
  FinTask.mapTask (fun f => FinTask.primitive (fun _ i => f i (E.complete i))) xs

@[simp] theorem piValuesTask_result {I : Type} [DecidableEq I] {J : I → Type}
    (E : Enumeration I) (F : ∀ i, Enumeration (J i)) :
    (piValuesTask E F).result = (List.pi E.values (fun i => (F i).values)).map
      (fun f i => f i (E.complete i)) := by
  simp [piValuesTask]

def piTask {I : Type} [Fintype I] [DecidableEq I] {J : I → Type} [∀ i, DecidableEq (J i)]
    (E : Enumeration I) (F : ∀ i, Enumeration (J i)) : FinTask (Enumeration (∀ i,J i)) := do
  let xs ← (piValuesTask E F).attach
  ofNodupTask xs.val (by
    rw [xs.property,piValuesTask_result]
    exact piRaw_nodup E F) (by
    intro f
    rw [xs.property,piValuesTask_result]
    refine List.mem_map.mpr ⟨fun i _ => f i,?_,rfl⟩
    exact (List.mem_pi _ _).mpr (fun i _ => (F i).complete (f i)))

@[simp] theorem piTask_result {I : Type} [Fintype I] [DecidableEq I] {J : I → Type} [∀ i, DecidableEq (J i)]
    (E : Enumeration I) (F : ∀ i, Enumeration (J i)) : (piTask E F).result = pi E F := by
  apply enumeration_ext
  simp [piTask,pi,ofCover]

end Cover.FiniteEnumeration

namespace Cover.FinTask

def listLengthTask {α : Type} : List α → FinTask ℕ
  | [] => .step fun _ => .done 0
  | _::xs => .step fun _ => do
      let n ← listLengthTask xs
      .step fun _ => .done (n+1)
@[simp] theorem listLengthTask_result {α : Type} (xs : List α) :
    (listLengthTask xs).result = xs.length := by
  induction xs <;> simp_all [listLengthTask]

def splitAtTask {α : Type} : ℕ → List α → FinTask (List α × List α)
  | 0,xs => .step fun _ => .done ([],xs)
  | _+1,[] => .step fun _ => .done ([],[])
  | n+1,x::xs => .step fun _ => do
      let p ← splitAtTask n xs
      .step fun _ => .done (x::p.1,p.2)
@[simp] theorem splitAtTask_result {α : Type} (n : ℕ) (xs : List α) :
    (splitAtTask n xs).result = (xs.take n,xs.drop n) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp [splitAtTask,ih]

def mergeTask {α : Type} (cmp : α → α → FinTask Bool) : List α → List α → FinTask (List α)
  | [],ys => .step fun _ => .done ys
  | xs,[] => .step fun _ => .done xs
  | x::xs,y::ys => .step fun _ => do
      let b ← cmp x y
      if b then do
        let zs ← mergeTask cmp xs (y::ys)
        .step fun _ => .done (x::zs)
      else do
        let zs ← mergeTask cmp (x::xs) ys
        .step fun _ => .done (y::zs)
termination_by xs ys => xs.length+ys.length

@[simp] theorem mergeTask_result {α : Type} (cmp : α → α → FinTask Bool) (xs ys : List α) :
    (mergeTask cmp xs ys).result = xs.merge ys (fun x y => (cmp x y).result) := by
  induction xs generalizing ys with
  | nil => simp [mergeTask]
  | cons x xs ihx =>
      induction ys with
      | nil => simp [mergeTask]
      | cons y ys ihy =>
          simp only [mergeTask,result_step,result_bindM,List.merge.eq_3]
          split <;> simp_all

/-- Structural recursion uses a computed list-length upper bound. Contiguous splitting
matches List.mergeSort exactly, and both splitting and merging expose internal steps. -/
def mergeSortFuelTask {α : Type} (cmp : α → α → FinTask Bool) : ℕ → List α → FinTask (List α)
  | 0,xs => .step fun _ => .done xs
  | _+1,[] => .step fun _ => .done []
  | _+1,[a] => .step fun _ => .done [a]
  | n+1,a::b::xs => .step fun _ => do
      let len ← listLengthTask (a::b::xs)
      let half ← primitive (fun _ => (len+1)/2)
      let p ← splitAtTask half (a::b::xs)
      let ls ← mergeSortFuelTask cmp n p.1
      let rs ← mergeSortFuelTask cmp n p.2
      mergeTask cmp ls rs

theorem mergeSortFuelTask_result {α : Type} (cmp : α → α → FinTask Bool) (n : ℕ)
    (xs : List α) (hn : xs.length ≤ n) :
    (mergeSortFuelTask cmp n xs).result = xs.mergeSort (fun x y => (cmp x y).result) := by
  induction n generalizing xs with
  | zero =>
      cases xs with
      | nil => simp [mergeSortFuelTask]
      | cons a xs => simp at hn
  | succ n ih =>
      cases xs with
      | nil => simp [mergeSortFuelTask]
      | cons a xs =>
          cases xs with
          | nil => simp [mergeSortFuelTask]
          | cons b xs =>
              have hl : ((a::b::xs).take (((a::b::xs).length+1)/2)).length ≤ n := by
                simp only [List.length_take,List.length_cons] at *
                omega
              have hr : ((a::b::xs).drop (((a::b::xs).length+1)/2)).length ≤ n := by
                simp only [List.length_drop,List.length_cons] at *
                omega
              simp only [mergeSortFuelTask,result_step,result_bindM,listLengthTask_result,
                primitive_result,splitAtTask_result,ih _ hl,ih _ hr,mergeTask_result]
              rw [List.mergeSort.eq_3]
              simp only [List.MergeSort.Internal.splitInTwo_fst,List.MergeSort.Internal.splitInTwo_snd]

def mergeSortTask {α : Type} (cmp : α → α → FinTask Bool) (xs : List α) : FinTask (List α) := do
  let n ← listLengthTask xs
  mergeSortFuelTask cmp n xs

@[simp] theorem mergeSortTask_result {α : Type} (cmp : α → α → FinTask Bool) (xs : List α) :
    (mergeSortTask cmp xs).result = xs.mergeSort (fun x y => (cmp x y).result) := by
  simp only [mergeSortTask,result_bindM,listLengthTask_result]
  exact mergeSortFuelTask_result cmp xs.length xs (le_refl _)

def lexLtTask {α : Type} [LinearOrder α] : List α → List α → FinTask Bool
  | [],[] => .step fun _ => .done false
  | [],_::_ => .step fun _ => .done true
  | _::_,[] => .step fun _ => .done false
  | a::as,b::bs => .step fun _ => if a<b then .done true else
      .step fun _ => if a=b then lexLtTask as bs else .done false

@[simp] theorem lexLtTask_result {α : Type} [LinearOrder α] (as bs : List α) :
    (lexLtTask as bs).result = decide (as<bs) := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [lexLtTask,List.lt]
  | cons a as ih =>
      cases bs with
      | nil => simp [lexLtTask,List.lt]
      | cons b bs =>
          by_cases hab : a<b
          · have hl : a::as < b::bs := List.Lex.rel hab
            simp [lexLtTask,hab,hl]
          · by_cases he : a=b
            · subst b; simp [lexLtTask,ih,List.lt,List.cons_lex_cons_iff]
            · have hba : b<a := lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm he)
              have hl : b::bs < a::as := List.Lex.rel hba
              simp [lexLtTask,hab,he,not_lt_of_ge hl.le]

def lexLETask {α : Type} [LinearOrder α] (as bs : List α) : FinTask Bool := do
  let b ← lexLtTask bs as
  .step fun _ => .done (!b)
@[simp] theorem lexLETask_result {α : Type} [LinearOrder α] (as bs : List α) :
    (lexLETask as bs).result = decide (as≤bs) := by
  by_cases h : as≤bs
  · have hn : ¬bs<as := not_lt_of_ge h
    simp [lexLETask,h,hn]
  · have hl : bs<as := lt_of_not_ge h
    simp [lexLETask,h,hl]

end Cover.FinTask

namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

def permsOfListTask {I : Type} [DecidableEq I] : List I → FinTask (List (Equiv.Perm I))
  | [] => .step fun _ => .done [1]
  | a::as => .step fun _ => do
      let ps ← permsOfListTask as
      let qs ← FinTask.flatMapTask (fun b => FinTask.mapTask
        (fun f => FinTask.primitive (fun _ => Equiv.swap a b * f)) ps) as
      FinTask.appendTask ps qs

@[simp] theorem permsOfListTask_result {I : Type} [DecidableEq I] (as : List I) :
    (permsOfListTask as).result = permsOfList as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [permsOfListTask,ih,permsOfList.eq_2]

def permutationLETask {I : Type} [LinearOrder I] (E : Enumeration I) (p q : Equiv.Perm I) : FinTask Bool := do
  let ps ← FinTask.mapTask (fun i => FinTask.primitive (fun _ => p i)) E.values
  let qs ← FinTask.mapTask (fun i => FinTask.primitive (fun _ => q i)) E.values
  FinTask.lexLETask ps qs
@[simp] theorem permutationLETask_result {I : Type} [LinearOrder I] (E : Enumeration I) (p q : Equiv.Perm I) :
    (permutationLETask E p q).result = decide (E.values.map p ≤ E.values.map q) := by
  simp [permutationLETask]

def permutationValuesTask {I : Type} [LinearOrder I] (E : Enumeration I) : FinTask (List (Equiv.Perm I)) := do
  let ps ← permsOfListTask E.values
  FinTask.mergeSortTask (permutationLETask E) ps

@[simp] theorem permutationValuesTask_result {I : Type} [LinearOrder I] (E : Enumeration I) :
    (permutationValuesTask E).result = (permutations E).values := by
  simp [permutationValuesTask,permutations]

def permutationsTask {I : Type} [LinearOrder I] (E : Enumeration I) : FinTask (Enumeration (Equiv.Perm I)) := do
  let ps ← (permutationValuesTask E).attach
  .step fun _ => .done ⟨ps.val,
    by rw [ps.property,permutationValuesTask_result]; exact (permutations E).nodup,
    by intro p; rw [ps.property,permutationValuesTask_result]; exact (permutations E).complete p⟩

@[simp] theorem permutationsTask_result {I : Type} [LinearOrder I] (E : Enumeration I) :
    (permutationsTask E).result = permutations E := by
  apply enumeration_ext
  simp [permutationsTask]

end Cover.FiniteEnumeration

namespace Cover.FinTask


def sublistsTask {α : Type} : List α → FinTask (List (List α))
  | [] => .step fun _ => .done [[]]
  | a::as => .step fun _ => do
      let tails ← sublistsTask as
      flatMapTask (fun xs => primitive (fun _ => [xs,a::xs])) tails
@[simp] theorem sublistsTask_result {α : Type} (xs : List α) :
    (sublistsTask xs).result = xs.sublists := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [sublistsTask,ih,List.sublists_cons]

def toFinsetTask {α : Type} [DecidableEq α] : List α → FinTask (Finset α)
  | [] => .step fun _ => .done ∅
  | a::as => .step fun _ => do
      let s ← toFinsetTask as
      finsetInsertTask a s
@[simp] theorem toFinsetTask_result {α : Type} [DecidableEq α] (xs : List α) :
    (toFinsetTask xs).result = xs.toFinset := by
  induction xs <;> simp_all [toFinsetTask]

def attachWithTask {α : Type} (P : α → Prop) : (xs : List α) →
    (∀ x ∈ xs,P x) → FinTask (List {x // P x})
  | [],_ => .step fun _ => .done []
  | x::xs,h => .step fun _ => do
      let ys ← attachWithTask P xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
      .step fun _ => .done (⟨x,h x (List.mem_cons_self)⟩::ys)
@[simp] theorem attachWithTask_result {α : Type} (P : α → Prop)
    (xs : List α) (h : ∀ x ∈ xs,P x) : (attachWithTask P xs h).result = xs.attachWith P h := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [attachWithTask,ih,List.attachWith,List.pmap]

end Cover.FinTask

namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

def finEnumerationTask (n : ℕ) : FinTask (Enumeration (Fin n)) := do
  let xs ← (FinTask.finRangeTask n).attach
  .step fun _ => .done ⟨xs.val,
    by rw [xs.property,FinTask.finRangeTask_result]; exact List.nodup_finRange n,
    by intro i; rw [xs.property,FinTask.finRangeTask_result]; exact List.mem_finRange i⟩
@[simp] theorem finEnumerationTask_result (n : ℕ) : (finEnumerationTask n).result = Compiler.finEnumeration n := by
  apply enumeration_ext
  simp [finEnumerationTask,Compiler.finEnumeration]

theorem mergeSort_enumeration_eq_sorted {I : Type} [Fintype I] [LinearOrder I] (E : Enumeration I) :
    E.values.mergeSort (fun x y => decide (x≤y)) = (sorted : Enumeration I).values := by
  have hs : (E.values.mergeSort (fun x y => decide (x≤y))).Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
      (le := fun x y : I => decide (x≤y))
      (fun x y z hxy hyz => by simpa using (of_decide_eq_true hxy).trans (of_decide_eq_true hyz))
      (fun x y => by simp only [Bool.or_eq_true,decide_eq_true_eq]; exact le_total x y) E.values
  have ht : (sorted : Enumeration I).values.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba) hs ht
  apply (List.perm_ext_iff_of_nodup (List.nodup_mergeSort.mpr E.nodup) (sorted : Enumeration I).nodup).mpr
  intro i
  simp [sorted,E.complete i]

def sortedByTask {I : Type} [Fintype I] [LinearOrder I] (E : Enumeration I)
    (cmp : I → I → FinTask Bool) (hcmp : ∀ x y, (cmp x y).result = decide (x≤y)) : FinTask (Enumeration I) := do
  let xs ← (FinTask.mergeSortTask cmp E.values).attach
  have he : xs.val = (sorted : Enumeration I).values := by
    rw [xs.property,FinTask.mergeSortTask_result]
    simp only [hcmp]
    exact mergeSort_enumeration_eq_sorted E
  .step fun _ => .done ⟨xs.val,he.symm ▸ (sorted : Enumeration I).nodup,
    fun i => he.symm ▸ (sorted : Enumeration I).complete i⟩
@[simp] theorem sortedByTask_result {I : Type} [Fintype I] [LinearOrder I] (E : Enumeration I)
    (cmp : I → I → FinTask Bool) (hcmp : ∀ x y, (cmp x y).result = decide (x≤y)) :
    (sortedByTask E cmp hcmp).result = (sorted : Enumeration I) := by
  apply enumeration_ext
  simp only [sortedByTask,FinTask.result_bindM,FinTask.attach_result,FinTask.result_step,FinTask.result_done,
    FinTask.mergeSortTask_result,hcmp]
  exact mergeSort_enumeration_eq_sorted E

def sortedTask {I : Type} [Fintype I] [LinearOrder I] (E : Enumeration I) : FinTask (Enumeration I) :=
  sortedByTask E (fun x y => FinTask.primitive (fun _ => decide (x≤y))) (fun _ _ => rfl)
@[simp] theorem sortedTask_result {I : Type} [Fintype I] [LinearOrder I] (E : Enumeration I) :
    (sortedTask E).result = (sorted : Enumeration I) := sortedByTask_result _ _ _

def subtypeValuesTask {I : Type} [DecidableEq I] (E : Enumeration I) (P : I → Prop) [DecidablePred P] :
    FinTask (List {i // P i}) := do
  let xs ← (FinTask.filterTask (fun i => decide (P i)) E.values).attach
  FinTask.attachWithTask P xs.val (by
    intro i hi
    rw [xs.property,FinTask.filterTask_result] at hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2)

@[simp] theorem subtypeValuesTask_result {I : Type} [DecidableEq I]
    (E : Enumeration I) (P : I → Prop) [DecidablePred P] :
    (subtypeValuesTask E P).result = (E.values.filter (fun i => decide (P i))).attachWith P
      (fun i hi => of_decide_eq_true (List.mem_filter.mp hi).2) := by
  simp [subtypeValuesTask]

def subtypeTask {I : Type} [DecidableEq I] (E : Enumeration I) (P : I → Prop) [DecidablePred P] :
    FinTask (Enumeration {i // P i}) := do
  let xs ← (subtypeValuesTask E P).attach
  ofNodupTask xs.val (by
    rw [xs.property,subtypeValuesTask_result]
    apply List.Nodup.of_map Subtype.val
    simpa using E.nodup.filter (fun i => decide (P i))) (by
    intro i
    rw [xs.property,subtypeValuesTask_result]
    simp [E.complete i.val,i.property])

def subsetsValuesTask {I : Type} [DecidableEq I] (E : Enumeration I) : FinTask (List (Finset I)) := do
  let xs ← FinTask.sublistsTask E.values
  FinTask.mapTask FinTask.toFinsetTask xs
@[simp] theorem subsetsValuesTask_result {I : Type} [DecidableEq I] (E : Enumeration I) :
    (subsetsValuesTask E).result = E.values.sublists.map List.toFinset := by
  simp [subsetsValuesTask]

def subsetsUnsortedTask {I : Type} [DecidableEq I] (E : Enumeration I) : FinTask (Enumeration (Finset I)) := do
  let xs ← (subsetsValuesTask E).attach
  ofNodupTask xs.val (by
    classical
    letI : Fintype I := Fintype.ofList E.values E.complete
    rw [xs.property,subsetsValuesTask_result]
    apply raw_nodup_of_complete_length _
      (by intro S
          refine List.mem_map.mpr ⟨E.values.filter (fun i => decide (i∈S)),List.mem_sublists.mpr List.filter_sublist,?_⟩
          ext i;simp [E.complete i])
    simp [Fintype.card_finset,length_eq_card]) (by
    intro S
    rw [xs.property,subsetsValuesTask_result]
    refine List.mem_map.mpr ⟨E.values.filter (fun i => decide (i∈S)),List.mem_sublists.mpr List.filter_sublist,?_⟩
    ext i
    simp [E.complete i])

end Cover.FiniteEnumeration

namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

private theorem mergeSort_filter_eq_sort {I : Type} [LinearOrder I]
    (E : Enumeration I) (S : Finset I) :
    (E.values.filter (fun i => decide (i∈S))).mergeSort (fun x y => decide (x≤y)) = S.sort (· ≤ ·) := by
  have hs : ((E.values.filter (fun i => decide (i∈S))).mergeSort
      (fun x y => decide (x≤y))).Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
      (le := fun x y : I => decide (x≤y))
      (fun x y z hxy hyz => by simpa using (of_decide_eq_true hxy).trans (of_decide_eq_true hyz))
      (fun x y => by simp only [Bool.or_eq_true,decide_eq_true_eq]; exact le_total x y) _
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba) hs (Finset.pairwise_sort _ _)
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_mergeSort.mpr (E.nodup.filter _)) (Finset.sort_nodup _ _)).mpr
  intro i
  simp [E.complete i]

def sortSubsetValuesTask {I : Type} [LinearOrder I] (E : Enumeration I) (S : Finset I) : FinTask (List I) := do
  let xs ← FinTask.filterByTask (fun i => FinTask.finsetMemTask i S) E.values
  FinTask.mergeSortTask (fun x y => FinTask.primitive (fun _ => decide (x≤y))) xs
@[simp] theorem sortSubsetValuesTask_result {I : Type} [LinearOrder I] (E : Enumeration I) (S : Finset I) :
    (sortSubsetValuesTask E S).result = S.sort (· ≤ ·) := by
  simp only [sortSubsetValuesTask,FinTask.result_bindM,FinTask.filterByTask_result,FinTask.finsetMemTask_result,
    FinTask.mergeSortTask_result,FinTask.primitive_result]
  exact mergeSort_filter_eq_sort E S

section FinsetOrdering
variable {I : Type} [Fintype I] [LinearOrder I]
local instance : LinearOrder (Finset I) := finsetOrder

/-- Comparing principal subsets does not hide their canonical sorting or list comparison. -/
def finsetLETask (E : Enumeration I) (S T : Finset I) : FinTask Bool := do
  let xs ← sortSubsetValuesTask E S
  let ys ← sortSubsetValuesTask E T
  FinTask.lexLETask xs ys
@[simp] theorem finsetLETask_result (E : Enumeration I) (S T : Finset I) :
    (finsetLETask E S T).result = decide (S.sort (· ≤ ·) ≤ T.sort (· ≤ ·)) := by
  simp only [finsetLETask,FinTask.result_bindM,sortSubsetValuesTask_result,FinTask.lexLETask_result]

/-- All subsets are constructed by a stepped powerset traversal and then sorted
with the exact existing lexicographic finset order. No Fintype universal-set data
is eagerly constructed to produce the executable list. -/
def subsetsTask (E : Enumeration I) : FinTask (Enumeration (Finset I)) := do
  let raw ← subsetsUnsortedTask E
  sortedByTask raw (finsetLETask E) (by
    intro S T
    exact finsetLETask_result E S T)
@[simp] theorem subsetsTask_result (E : Enumeration I) :
    (subsetsTask E).result = (sorted : Enumeration (Finset I)) := by
  simp [subsetsTask]

end FinsetOrdering

def subtypeValuesByTask {I : Type} [DecidableEq I] (E : Enumeration I)
    (P : I → Prop) [DecidablePred P] (test : I → FinTask Bool)
    (htest : ∀ i,(test i).result=decide (P i)) : FinTask (List {i // P i}) := do
  let xs ← (FinTask.filterByTask test E.values).attach
  FinTask.attachWithTask P xs.val (by
    intro i hi
    rw [xs.property,FinTask.filterByTask_result] at hi
    have h := (List.mem_filter.mp hi).2
    rw [htest] at h
    exact of_decide_eq_true h)
@[simp] theorem subtypeValuesByTask_result {I : Type} [DecidableEq I] (E : Enumeration I)
    (P : I → Prop) [DecidablePred P] (test : I → FinTask Bool)
    (htest : ∀ i,(test i).result=decide (P i)) :
    (subtypeValuesByTask E P test htest).result = (subtypeValuesTask E P).result := by
  simp [subtypeValuesByTask,htest]

def subtypeByTask {I : Type} [DecidableEq I] (E : Enumeration I)
    (P : I → Prop) [DecidablePred P] (test : I → FinTask Bool)
    (htest : ∀ i,(test i).result=decide (P i)) : FinTask (Enumeration {i // P i}) := do
  let xs ← (subtypeValuesByTask E P test htest).attach
  ofNodupTask xs.val (by
    rw [xs.property,subtypeValuesByTask_result,subtypeValuesTask_result]
    apply List.Nodup.of_map Subtype.val
    simpa using E.nodup.filter (fun i => decide (P i))) (by
    intro i
    rw [xs.property,subtypeValuesByTask_result,subtypeValuesTask_result]
    simp [E.complete i.val,i.property])

def indicesTask {I : Type} [Fintype I] [LinearOrder I] (E : Enumeration I) (S : Finset I) :
    FinTask (Enumeration S) := do
  let raw ← subtypeByTask E (fun i => i∈S) (fun i => FinTask.finsetMemTask i S)
    (fun i => FinTask.finsetMemTask_result i S)
  sortedTask raw
@[simp] theorem indicesTask_result {I : Type} [Fintype I] [LinearOrder I] (E : Enumeration I) (S : Finset I) :
    (indicesTask E S).result = (sorted : Enumeration S) := by
  simp [indicesTask]

/-- Compute both parts of one principal entry without a dependent-map lookup. -/
def principalEntryTask {I : Type} [Fintype I] [LinearOrder I]
    (E : Enumeration I) (S : Finset I) :
    FinTask (Enumeration S × Enumeration (Equiv.Perm S)) := do
  let indices ← indicesTask E S
  let perms ← permutationsTask indices
  .step fun _ => .done (indices,perms)
@[simp] theorem principalEntryTask_result {I : Type} [Fintype I] [LinearOrder I]
    (E : Enumeration I) (S : Finset I) :
    (principalEntryTask E S).result = ((sorted : Enumeration S),permutations (sorted : Enumeration S)) := by
  simp [principalEntryTask]

/-- The complete principal ordering is built before return: every subset, every
subtype index list, and every determinant permutation enumeration is stepped. -/
def principalTask (r : ℕ) : FinTask (PrincipalOrdering (Fin r)) := .step fun _ => do
  let base ← finEnumerationTask r
  let subs ← subsetsTask base
  let entries ← dependentTask subs (principalEntryTask base)
  .step fun _ => .done {
    subsets := subs
    indices := fun S => (entries S).1
    permutations := fun S => (entries S).2 }

@[simp] theorem principalTask_result (r : ℕ) : (principalTask r).result = principal r := by
  simp [principalTask,principal]

theorem principalTask_zero_unknown (r : ℕ) : FinTask.run 0 (principalTask r) = none := rfl

theorem principalTask_run_sound (r fuel : ℕ) (P : PrincipalOrdering (Fin r))
    (hr : FinTask.run fuel (principalTask r) = some P) : P = principal r := by
  have h := FinTask.run_sound fuel _ _ hr
  rw [principalTask_result] at h
  exact h.symm

theorem principalTask_has_fuel (r : ℕ) :
    ∃ fuel, FinTask.run fuel (principalTask r) = some (principal r) := by
  refine ⟨(principalTask r).steps,?_⟩
  simpa only [principalTask_result] using FinTask.run_sufficient (principalTask r) _ (le_refl _)

end Cover.FiniteEnumeration


namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

/-- Sort a complete explicitly supplied candidate list; no opaque Fintype list is
extracted or constructed. Deduplication and stable sorting are both stepped. -/
def sortedCandidatesTask {I : Type} [Fintype I] [LinearOrder I]
    (xs : List I) (complete : ∀ i,i∈xs) : FinTask (Enumeration I) := do
  let raw ← ofCoverTask xs complete
  sortedTask raw
@[simp] theorem sortedCandidatesTask_result {I : Type} [Fintype I] [LinearOrder I]
    (xs : List I) (complete : ∀ i,i∈xs) :
    (sortedCandidatesTask xs complete).result = (sorted : Enumeration I) := by
  simp [sortedCandidatesTask]

/-- Generic predicate-restricted sorting from a previously executed finite enumeration. -/
def sortedSubtypeTask {I : Type} [Fintype I] [LinearOrder I]
    (E : Enumeration I) (P : I → Prop) [DecidablePred P] : FinTask (Enumeration {i // P i}) := do
  let raw ← subtypeTask E P
  sortedTask raw
@[simp] theorem sortedSubtypeTask_result {I : Type} [Fintype I] [LinearOrder I]
    (E : Enumeration I) (P : I → Prop) [DecidablePred P] :
    (sortedSubtypeTask E P).result = (sorted : Enumeration {i // P i}) := by
  simp [sortedSubtypeTask]

end Cover.FiniteEnumeration

namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

/-- Mirror the pinned signAux2 recursion. Each visited index, permutation application,
fixed-point check, transposition construction and integer negation is stepped. -/
def signAuxTask {I : Type} [DecidableEq I] : List I → Equiv.Perm I → FinTask ℤ
  | [],_ => .step fun _ => .done 1
  | i::is,π => .step fun _ => do
      let j ← FinTask.primitive (fun _ => π i)
      let fixed ← FinTask.primitive (fun _ => decide (i=j))
      if fixed then signAuxTask is π else do
        let next ← FinTask.primitive (fun _ => Equiv.swap i j * π)
        let z ← signAuxTask is next
        FinTask.primitive (fun _ => -z)

@[simp] theorem signAuxTask_result {I : Type} [DecidableEq I]
    (is : List I) (π : Equiv.Perm I) :
    (signAuxTask is π).result = (Equiv.Perm.signAux2 is π : ℤ) := by
  induction is generalizing π with
  | nil => simp [signAuxTask,Equiv.Perm.signAux2]
  | cons i is ih =>
      simp only [signAuxTask,FinTask.result_step,FinTask.result_bindM,FinTask.primitive_result,
        decide_eq_true_eq,Equiv.Perm.signAux2.eq_2]
      split_ifs
      · exact ih π
      · simp only [FinTask.result_bindM,FinTask.primitive_result,ih,Units.val_neg]

/-- The supplied list need only cover the nonfixed points; no list chosen from an
opaque finite-type instance occurs in the executable computation. -/
theorem signAux2_eq_sign_of_cover {I : Type} [DecidableEq I] [Fintype I]
    (is : List I) (π : Equiv.Perm I) (hcover : ∀ i, π i ≠ i → i∈is) :
    Equiv.Perm.signAux2 is π = Equiv.Perm.sign π := by
  induction is generalizing π with
  | nil =>
      have he : π=1 := by
        apply Equiv.ext
        intro i
        by_contra hn
        exact List.not_mem_nil (hcover i hn)
      subst π
      simp [Equiv.Perm.signAux2]
  | cons i is ih =>
      rw [Equiv.Perm.signAux2]
      by_cases hi : i=π i
      · rw [if_pos hi]
        apply ih
        intro j hj
        have hji : j≠i := by intro he; subst j; exact hj hi.symm
        exact (List.mem_cons.mp (hcover j hj)).resolve_left hji
      · rw [if_neg hi]
        have hnext : ∀ j, (Equiv.swap i (π i)*π) j ≠ j → j∈is := by
          intro j hj
          have hn := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hj
          exact (List.mem_cons.mp (hcover j hn.1)).resolve_left hn.2
        rw [ih _ hnext,Equiv.Perm.sign_mul,Equiv.Perm.sign_swap hi]
        simp

/-- Exact determinant sign from the already computed complete index enumeration. -/
def signTask {I : Type} [DecidableEq I] (E : Enumeration I) (π : Equiv.Perm I) : FinTask ℤ :=
  signAuxTask E.values π

@[simp] theorem signTask_result {I : Type} [DecidableEq I] [Fintype I]
    (E : Enumeration I) (π : Equiv.Perm I) :
    (signTask E π).result = (Equiv.Perm.sign π : ℤ) := by
  rw [signTask,signAuxTask_result,signAux2_eq_sign_of_cover E.values π (fun i _ => E.complete i)]

theorem signTask_zero_unknown {I : Type} [DecidableEq I]
    (E : Enumeration I) (π : Equiv.Perm I) : FinTask.run 0 (signTask E π) = none := by
  unfold signTask
  cases E.values <;> rfl

theorem signTask_run_sound {I : Type} [DecidableEq I] [Fintype I]
    (E : Enumeration I) (π : Equiv.Perm I) (fuel : ℕ) (z : ℤ)
    (hr : FinTask.run fuel (signTask E π) = some z) : z = (Equiv.Perm.sign π : ℤ) := by
  have h := FinTask.run_sound fuel _ _ hr
  rw [signTask_result] at h
  exact h.symm

end Cover.FiniteEnumeration

namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

/-- Equality-free candidate sorting when the producer has already established nodup. -/
def sortedNodupCandidatesTask {I : Type} [Fintype I] [LinearOrder I]
    (xs : List I) (hn : xs.Nodup) (complete : ∀ i,i∈xs) : FinTask (Enumeration I) := do
  let raw ← ofNodupTask xs hn complete
  sortedTask raw
@[simp] theorem sortedNodupCandidatesTask_result {I : Type} [Fintype I] [LinearOrder I]
    (xs : List I) (hn : xs.Nodup) (complete : ∀ i,i∈xs) :
    (sortedNodupCandidatesTask xs hn complete).result = (sorted : Enumeration I) := by
  simp [sortedNodupCandidatesTask]

/-- Predicate callbacks expose any input-dependent membership traversal. -/
def sortedSubtypeByTask {I : Type} [Fintype I] [LinearOrder I]
    (E : Enumeration I) (P : I → Prop) [DecidablePred P]
    (test : I → FinTask Bool) (htest : ∀ i,(test i).result=decide (P i)) :
    FinTask (Enumeration {i // P i}) := do
  let raw ← subtypeByTask E P test htest
  sortedTask raw
@[simp] theorem sortedSubtypeByTask_result {I : Type} [Fintype I] [LinearOrder I]
    (E : Enumeration I) (P : I → Prop) [DecidablePred P]
    (test : I → FinTask Bool) (htest : ∀ i,(test i).result=decide (P i)) :
    (sortedSubtypeByTask E P test htest).result = (sorted : Enumeration {i // P i}) := by
  simp [sortedSubtypeByTask]

end Cover.FiniteEnumeration

namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

/-- Ordered lookup uses the supplied stepped equality callback. The membership and
Fin-bound proofs erase; no list length or pure idxOf traversal precedes a checkpoint. -/
def indexListTaskWith {I : Type} [DecidableEq I] (i : I)
    (eqTask : I → I → FinTask Bool) (heq : ∀ a b,(eqTask a b).result=decide (a=b)) :
    (xs : List I) → i∈xs → FinTask (Fin xs.length)
  | [],h => False.elim (List.not_mem_nil h)
  | a::as,h => .step fun _ => do
      let same ← (eqTask i a).attach
      if hs : same.val=true then .done ⟨0,Nat.zero_lt_succ _⟩ else
        have hne : i≠a := by
          intro hi
          have hb := same.property.trans (heq i a)
          have ht : decide (i=a)=true := decide_eq_true hi
          exact hs (hb.trans ht)
        do
          let k ← indexListTaskWith i eqTask heq as ((List.mem_cons.mp h).resolve_left hne)
          .step fun _ => .done ⟨k.val+1,Nat.succ_lt_succ k.isLt⟩

theorem indexListTaskWith_get {I : Type} [DecidableEq I] (i : I)
    (eqTask : I → I → FinTask Bool) (heq : ∀ a b,(eqTask a b).result=decide (a=b))
    (xs : List I) (h : i∈xs) : xs.get ((indexListTaskWith i eqTask heq xs h).result) = i := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons a as ih =>
      simp only [indexListTaskWith,FinTask.result_step,FinTask.result_bindM,FinTask.attach_result,heq]
      split_ifs with hs
      · have hi : i=a := of_decide_eq_true hs
        subst i
        rfl
      · simp only [FinTask.result_bindM,FinTask.result_step,FinTask.result_done]
        exact ih _

/-- Exact index in E's supplied order, with every candidate comparison resumable. -/
def indexTaskWith {I : Type} [DecidableEq I] (E : Enumeration I) (i : I)
    (eqTask : I → I → FinTask Bool) (heq : ∀ a b,(eqTask a b).result=decide (a=b)) :
    FinTask (Fin E.values.length) := .step fun _ =>
  indexListTaskWith i eqTask heq E.values (E.complete i)

@[simp] theorem indexTaskWith_result {I : Type} [DecidableEq I] (E : Enumeration I) (i : I)
    (eqTask : I → I → FinTask Bool) (heq : ∀ a b,(eqTask a b).result=decide (a=b)) :
    (indexTaskWith E i eqTask heq).result = (indexEquiv E).symm i := by
  apply (indexEquiv E).injective
  rw [Equiv.apply_symm_apply]
  change E.values.get ((indexTaskWith E i eqTask heq).result) = i
  exact indexListTaskWith_get i eqTask heq E.values (E.complete i)

/-- Convenience wrapper only for scalar/cached-key equality primitives. Structured
coordinate or function equality must use indexTaskWith with its explicit callback. -/
def indexTask {I : Type} [DecidableEq I] (E : Enumeration I) (i : I) : FinTask (Fin E.values.length) :=
  indexTaskWith E i (fun a b => FinTask.primitive (fun _ => decide (a=b))) (fun _ _ => rfl)

@[simp] theorem indexTask_result {I : Type} [DecidableEq I] (E : Enumeration I) (i : I) :
    (indexTask E i).result = (indexEquiv E).symm i := indexTaskWith_result _ _ _ _

theorem indexTaskWith_zero_unknown {I : Type} [DecidableEq I] (E : Enumeration I) (i : I)
    (eqTask : I → I → FinTask Bool) (heq : ∀ a b,(eqTask a b).result=decide (a=b)) :
    FinTask.run 0 (indexTaskWith E i eqTask heq) = none := rfl

theorem indexTaskWith_run_sound {I : Type} [DecidableEq I] (E : Enumeration I) (i : I)
    (eqTask : I → I → FinTask Bool) (heq : ∀ a b,(eqTask a b).result=decide (a=b))
    (fuel : ℕ) (k : Fin E.values.length)
    (hr : FinTask.run fuel (indexTaskWith E i eqTask heq) = some k) :
    k = (indexEquiv E).symm i := by
  have h := FinTask.run_sound fuel _ _ hr
  rw [indexTaskWith_result] at h
  exact h.symm

end Cover.FiniteEnumeration

namespace Cover.FiniteEnumeration
open Gen.ModelEncoding.Ordered

/-- The exact Cartesian raw list already has no duplicates; the old dedup changes nothing. -/
theorem pi_values {I : Type} [Fintype I] [DecidableEq I]
    {J : I → Type} [∀ i,DecidableEq (J i)] (E : Enumeration I) (F : ∀ i,Enumeration (J i)) :
    (pi E F).values = (List.pi E.values (fun i => (F i).values)).map (fun f i => f i (E.complete i)) := by
  exact List.dedup_eq_self.mpr (piRaw_nodup E F)

end Cover.FiniteEnumeration
