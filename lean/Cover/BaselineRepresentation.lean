import Cover.FiniteDesign
import Cover.FiniteTasks

namespace Cover.FiniteDesign

/-- A valid input already has distinct edges. Reuse that list as the finset's
multiset representation instead of running List.toFinset's deduplication. -/
def directBaseline (I : Syntax) (h : Valid I) : Ext.TripleDesign (Fin I.groups) where
  edges := ⟨(I.edges : Multiset (Finset (Fin I.groups))),Multiset.coe_nodup.mpr h.2.2.2.1⟩
  edges_nonempty := by
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ h.2.2.1
    exact ⟨e,by simpa using he⟩
  edge_card := by
    intro e he
    exact h.2.2.2.2.1 e (by simpa using he)
  covered := by
    intro g
    simpa using h.2.2.2.2.2 g

theorem directBaseline_eq (I : Syntax) (h : Valid I) : directBaseline I h=toBaseline I h := by
  simp only [directBaseline,toBaseline,Ext.TripleDesign.mk.injEq]
  exact List.toFinset_eq h.2.2.2.1

def directBaselineTask (I : Syntax) (h : Valid I) :
    FinTask {D : Ext.TripleDesign (Fin I.groups) // D=toBaseline I h} :=
  .step fun _ => .done ⟨directBaseline I h,directBaseline_eq I h⟩

@[simp] theorem directBaselineTask_result (I : Syntax) (h : Valid I) :
    (directBaselineTask I h).result.val=toBaseline I h := (directBaselineTask I h).result.property

end Cover.FiniteDesign
