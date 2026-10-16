import Cover.FiniteEnumeration
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace Cover.FiniteDesign
open Gen.ModelEncoding.Ordered Cover.FiniteEnumeration

/-- Finite discrete input. Rank and output sizes are represented by their predecessor. -/
structure Syntax where
  groups : ℕ
  rankPred : ℕ
  outputPred : Fin groups → ℕ
  edges : List (Finset (Fin groups))

def Valid (I : Syntax) : Prop :=
  0 < I.rankPred ∧
  (∀ g, I.rankPred ≤ I.outputPred g) ∧
  I.edges ≠ [] ∧
  I.edges.Nodup ∧
  (∀ e ∈ I.edges, e.card = 3) ∧
  ∀ g, ∃ e ∈ I.edges, g ∈ e

instance (I : Syntax) : Decidable (Valid I) := by unfold Valid; infer_instance
/-- Total finite validation, with no tests on real values. -/
def validate (I : Syntax) : Bool := decide (Valid I)
@[simp] theorem validate_iff (I : Syntax) : validate I = true ↔ Valid I := by simp [validate]

/-- Exact bridge into the accepted mathematical design. -/
def toBaseline (I : Syntax) (h : Valid I) : Ext.TripleDesign (Fin I.groups) where
  edges := I.edges.toFinset
  edges_nonempty := by
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ h.2.2.1
    exact ⟨e,List.mem_toFinset.mpr he⟩
  edge_card e he := h.2.2.2.2.1 e (List.mem_toFinset.mp he)
  covered g := by
    obtain ⟨e,he,hg⟩ := h.2.2.2.2.2 g
    exact ⟨e,List.mem_toFinset.mpr he,hg⟩

/-- Retain the input's exact edge order; distinct permutations of the input list are valid. -/
def inputEdges (I : Syntax) (h : Valid I) : Enumeration (toBaseline I h).Edge where
  values := I.edges.attach.map (fun e => ⟨e.val,List.mem_toFinset.mpr e.property⟩)
  nodup := by
    apply List.Nodup.map
    · intro e f hef; exact Subtype.ext (congrArg (fun z : (toBaseline I h).Edge => z.val) hef)
    · exact List.nodup_attach.mpr h.2.2.2.1
  complete e := by
    refine List.mem_map.mpr ⟨⟨e.val,List.mem_toFinset.mp e.property⟩,?_,?_⟩
    · exact List.mem_attach _ _
    · exact Subtype.ext rfl

theorem inputEdges_preserves_order (I : Syntax) (h : Valid I) :
    (inputEdges I h).values.map Subtype.val = I.edges := by
  simp [inputEdges,List.map_map,Function.comp_def]

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G)

/-- Actual finite edge-intersection graph. -/
def edgeGraph : SimpleGraph D.Edge where
  Adj := D.Adjacent
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,by obtain ⟨g,hg,hg'⟩ := h.2; exact ⟨g,hg',hg⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance edgeGraphAdjDecidable : DecidableRel (edgeGraph D).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ ∃ g : G, _ ∧ _))

theorem reachable_iff_components (e f : D.Edge) :
    (edgeGraph D).Reachable e f ↔ D.component e = D.component f := by
  rw [D.component_eq_iff_path,SimpleGraph.reachable_iff_reflTransGen]
  rfl

/-- Deciding reachability searches only path lengths below the number of edges. -/
@[reducible] def componentRelationDecidable : DecidableRel (Relation.EqvGen D.Overlap) := fun e f =>
  decidable_of_iff ((edgeGraph D).Reachable e f)
    ((reachable_iff_components D e f).trans (D.component_eq_iff e f))

/-- Computable quotient equality, using finite graph reachability rather than choice. -/
def componentDecidableEq : DecidableEq D.Component := by
  letI := componentRelationDecidable D
  exact Quotient.decidableEq

/-- Reimplemented literal quotient constructor to avoid legacy noncomputable declarations. -/
def componentOfEdge (e : D.Edge) : D.Component := Quotient.mk _ e
@[simp] theorem componentOfEdge_eq (e : D.Edge) : componentOfEdge D e = D.component e := rfl

/-- Complete component list, computed from edge classes; earliest edge orders each class. -/
def components (edges : Enumeration D.Edge) : Enumeration D.Component := by
  letI := componentDecidableEq D
  let xs := (edges.values.map (componentOfEdge D)).reverse.dedup.reverse
  exact ⟨xs, by simp only [xs,List.nodup_reverse]; exact List.nodup_dedup _, by
    intro c
    induction c using Quotient.inductionOn with
    | h e =>
      simp only [xs,List.mem_reverse,List.mem_dedup]
      exact List.mem_map.mpr ⟨e,edges.complete e,rfl⟩⟩

/-- Choose the first incident edge by finite list search. -/
def incident (edges : Enumeration D.Edge) (g : G) : D.Edge :=
  ((edges.values.filter fun e => g ∈ e.val).head (by
    intro hnil
    obtain ⟨e,he,hg⟩ := D.covered g
    have hm : (⟨e,he⟩ : D.Edge) ∈ edges.values.filter (fun e => g ∈ e.val) := by
      simp only [List.mem_filter,decide_eq_true_eq]; exact ⟨edges.complete _,hg⟩
    rw [hnil] at hm; exact List.not_mem_nil hm))

theorem mem_incident (edges : Enumeration D.Edge) (g : G) : g ∈ (incident D edges g).val := by
  have h := List.head_mem (show (edges.values.filter fun e => g ∈ e.val) ≠ [] from ?_)
  · exact (List.mem_filter.mp h).2 |> of_decide_eq_true
  · intro hnil
    obtain ⟨e,he,hg⟩ := D.covered g
    have hm : (⟨e,he⟩ : D.Edge) ∈ edges.values.filter (fun e => g ∈ e.val) := by
      simp only [List.mem_filter,decide_eq_true_eq]; exact ⟨edges.complete _,hg⟩
    rw [hnil] at hm; exact List.not_mem_nil hm

def groupComponent (edges : Enumeration D.Edge) (g : G) : D.Component :=
  componentOfEdge D (incident D edges g)

theorem groupComponent_eq (edges : Enumeration D.Edge) (g : G) :
    groupComponent D edges g = D.groupComponent g := by
  exact (D.groupComponent_eq (incident D edges g) ⟨g,mem_incident D edges g⟩).symm

end Cover.FiniteDesign
