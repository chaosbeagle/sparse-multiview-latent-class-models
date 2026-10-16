import Cover.FiniteTasks

namespace Cover.FinTask

/-- A declared native representation-copy operation. Allocation limits are external;
the copy is not claimed to have constant physical cost. -/
def copyArrayTask {α : Type} (xs : List α) : FinTask {a : Array α // a=xs.toArray} :=
  .step fun _ => .done ⟨xs.toArray,rfl⟩
@[simp] theorem copyArrayTask_result {α : Type} (xs : List α) :
    (copyArrayTask xs).result = ⟨xs.toArray,rfl⟩ := rfl

/-- Dependent Fin-indexed values are materialized once and accessed by native index.
The proof cast erases; the returned function contains no List.get or key search. -/
def certifiedFinFamilyTask {n : ℕ} {β : Fin n → Type} (f : (i : Fin n) → FinTask (β i)) :
    FinTask {g : (i : Fin n) → β i // ∀ i,g i=(f i).result} := .step fun _ => do
  let indices ← certify (finRangeTask n)
  let rows ← certify (mapTask (fun i => do
    let value ← f i
    primitive (fun _ => (⟨i,value⟩ : Sigma β))) indices.val)
  let arr ← copyArrayTask rows.val
  have hind : indices.val = List.finRange n := indices.property.trans (finRangeTask_result n)
  have hrows : rows.val = (List.finRange n).map (fun i => (⟨i,(f i).result⟩ : Sigma β)) := by
    rw [rows.property,mapTask_result,hind]
    simp
  have harr : arr.val = ((List.finRange n).map (fun i => (⟨i,(f i).result⟩ : Sigma β))).toArray :=
    arr.property.trans (congrArg List.toArray hrows)
  have hsize : arr.val.size=n := by simp [harr]
  have hkey (i : Fin n) : (arr.val[i.val]'(hsize.symm ▸ i.isLt)).1=i := by
    simp [harr]
  .step fun _ => .done ⟨(fun i => hkey i ▸ (arr.val[i.val]'(hsize.symm ▸ i.isLt)).2), by
    intro i
    have hval : (arr.val[i.val]'(hsize.symm ▸ i.isLt)) = ⟨i,(f i).result⟩ := by
      have hi : (List.finRange n)[i.val]'(by simpa using i.isLt) = i := by
        apply Fin.ext
        simp
      simp only [harr,List.getElem_toArray,List.getElem_map]
      exact congrArg (fun j => (⟨j,(f j).result⟩ : Sigma β)) hi
    exact eq_of_heq ((eqRec_heq (hkey i) _).trans (Sigma.ext_iff.mp hval).2)⟩

def finFamilyTask {n : ℕ} {β : Fin n → Type} (f : (i : Fin n) → FinTask (β i)) :
    FinTask ((i : Fin n) → β i) := do
  let cached ← certifiedFinFamilyTask f
  .done cached.val

@[simp] theorem finFamilyTask_result {n : ℕ} {β : Fin n → Type}
    (f : (i : Fin n) → FinTask (β i)) :
    (finFamilyTask f).result = fun i => (f i).result := by
  simp only [finFamilyTask,FinTask.result_bindM,FinTask.result_done]
  funext i
  exact (certifiedFinFamilyTask f).result.property i

end Cover.FinTask
