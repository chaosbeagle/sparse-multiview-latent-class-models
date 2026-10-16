import Ext.Core
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators Classical
noncomputable section
namespace Ext

/-- The exact finite, nonempty, covered design of unordered three-element edges. -/
structure TripleDesign (G : Type*) [Fintype G] [DecidableEq G] where
  edges : Finset (Finset G)
  edges_nonempty : edges.Nonempty
  edge_card : ∀ e ∈ edges, e.card = 3
  covered : ∀ g : G, ∃ e ∈ edges, g ∈ e

namespace TripleDesign
variable {G : Type*} [Fintype G] [DecidableEq G] (D : TripleDesign G)
abbrev Edge := {e : Finset G // e ∈ D.edges}
abbrev GroupAt (e : D.Edge) := {g : G // g ∈ e.val}
def Overlap (e f : D.Edge) : Prop := ∃ g, g ∈ e.val ∧ g ∈ f.val
/-- Reachability closure; self-overlap adds only reflexive steps, so this is precisely
    the edge-intersection graph's component relation. -/
def Adjacent (e f : D.Edge) : Prop := e ≠ f ∧ D.Overlap e f

instance adjacent_symm : Std.Symm D.Adjacent where
  symm := by
    intro e f h
    obtain ⟨hne, g, hge, hgf⟩ := h
    exact ⟨Ne.symm hne, g, hgf, hge⟩

theorem overlap_closure_eq_adjacency (e f : D.Edge) :
    Relation.EqvGen D.Overlap e f ↔ Relation.EqvGen D.Adjacent e f := by
  constructor
  · intro h
    induction h with
    | rel e f hef =>
      by_cases heq : e = f
      · subst f; exact Relation.EqvGen.refl e
      · exact Relation.EqvGen.rel e f ⟨heq, hef⟩
    | refl e => exact Relation.EqvGen.refl e
    | symm e f h ih => exact Relation.EqvGen.symm e f ih
    | trans e f g h₁ h₂ ih₁ ih₂ => exact Relation.EqvGen.trans e f g ih₁ ih₂
  · exact Relation.EqvGen.mono (fun _ _ h => h.2) e f

def Component := Quotient (Relation.EqvGen.setoid D.Overlap)
instance componentFintype : Fintype D.Component := by
  unfold Component
  exact Fintype.ofFinite _
def component (e : D.Edge) : D.Component := Quotient.mk _ e

theorem component_eq_iff (e f : D.Edge) :
    D.component e = D.component f ↔ Relation.EqvGen D.Overlap e f :=
  Quotient.eq

theorem component_eq_iff_path (e f : D.Edge) :
    D.component e = D.component f ↔ Relation.ReflTransGen D.Adjacent e f := by
  rw [D.component_eq_iff, D.overlap_closure_eq_adjacency,
    Relation.EqvGen.eqvGen_eq_reflTransGen]

theorem overlap_component_eq {e f : D.Edge} (h : D.Overlap e f) :
    D.component e = D.component f :=
  Quotient.sound (Relation.EqvGen.rel _ _ h)

theorem edge_nonempty : Nonempty D.Edge := by
  obtain ⟨e, he⟩ := D.edges_nonempty
  exact ⟨⟨e, he⟩⟩

theorem component_nonempty : Nonempty D.Component := by
  obtain ⟨e⟩ := D.edge_nonempty
  exact ⟨D.component e⟩

def incident (g : G) : D.Edge := ⟨(D.covered g).choose, (D.covered g).choose_spec.1⟩
theorem mem_incident (g : G) : g ∈ (D.incident g).val := (D.covered g).choose_spec.2
def groupComponent (g : G) : D.Component := D.component (D.incident g)

theorem groupComponent_eq (e : D.Edge) (g : D.GroupAt e) :
    D.groupComponent g.val = D.component e := by
  apply D.overlap_component_eq
  exact ⟨g.val, D.mem_incident g.val, g.property⟩

/-- Every finite set of actual v2 triples with precisely the stipulated coverage
    gives this design. No cardinal bound, ordering of groups, or grid is imposed. -/
def ofEdges (E : Finset (Finset G)) (hE : E.Nonempty)
    (hcard : ∀ e ∈ E, e.card = 3) (hcover : ∀ g : G, ∃ e ∈ E, g ∈ e) :
    TripleDesign G := ⟨E, hE, hcard, hcover⟩
@[simp] theorem ofEdges_edges (E : Finset (Finset G)) (hE hcard hcover) :
    (ofEdges E hE hcard hcover).edges = E := rfl

abbrev Outcome (Y : G → Type*) (e : D.Edge) := ∀ g : D.GroupAt e, Y g.val
end TripleDesign

namespace FiniteLaw
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]
/-- The actual dependent finite product law, with its normalization proved. -/
def productLaw (P : ∀ i, FiniteLaw (X i)) : FiniteLaw (∀ i, X i) where
  mass x := ∏ i, (P i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (P i).nonneg (x i))
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp only [FiniteLaw.total, Finset.prod_const_one]

variable {J Ω : Type*} [Fintype J] [Fintype Ω]
/-- Convex mixing of normalized real probability vectors. -/
def mixLaw (w : FiniteLaw J) (P : J → FiniteLaw Ω) : FiniteLaw Ω where
  mass x := ∑ j, w.mass j * (P j).mass x
  nonneg x := Finset.sum_nonneg (fun j _ => mul_nonneg (w.nonneg j) ((P j).nonneg x))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FiniteLaw.total, mul_one]

theorem card_pos (P : FiniteLaw Ω) : 0 < Fintype.card Ω := by
  by_contra h
  haveI : IsEmpty Ω := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
  have hbad : (0 : ℝ) = 1 := by simpa using P.total
  norm_num at hbad

theorem event_nonneg (P : FiniteLaw Ω) (A : Ω → Prop) : 0 ≤ P.prob A := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact P.nonneg x
  · exact le_rfl

theorem event_le_one (P : FiniteLaw Ω) (A : Ω → Prop) : P.prob A ≤ 1 := by
  classical
  rw [← P.total]
  apply Finset.sum_le_sum
  intro x hx
  split_ifs
  · exact le_rfl
  · exact P.nonneg x
end FiniteLaw

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)]
/-- All real v2 parameters. There is no discretization, margin, anchor or
    identifiability conclusion in these fields. Stationarity is by indexing kernels by group. -/
structure Theta2 where
  prevalence : D.Component → FiniteLaw Bool
  prevalence_pos : ∀ c t, 0 < (prevalence c).mass t
  kernel : ∀ g, Bool → FiniteLaw (Y g)
  rank_two : ∀ g (u v : ℝ),
    (∀ y, u * (kernel g false).mass y + v * (kernel g true).mass y = 0) → u = 0 ∧ v = 0

namespace Theta2
variable {D Y}
/-- Entrywise bridge from arbitrary real v2 arrays to the bundled full parameter space. -/
def ofArrays (π : D.Component → Bool → ℝ)
    (hπpos : ∀ c t, 0 < π c t) (hπtotal : ∀ c, ∑ t, π c t = 1)
    (K : ∀ g, Y g → Bool → ℝ) (hKnonneg : ∀ g y t, 0 ≤ K g y t)
    (hKtotal : ∀ g t, ∑ y, K g y t = 1)
    (hKrank : ∀ g (u v : ℝ), (∀ y, u * K g y false + v * K g y true = 0) →
      u = 0 ∧ v = 0) : Theta2 D Y where
  prevalence c := ⟨π c, fun t => (hπpos c t).le, hπtotal c⟩
  prevalence_pos := hπpos
  kernel g t := ⟨fun y => K g y t, fun y => hKnonneg g y t, hKtotal g t⟩
  rank_two := hKrank

def reference (θ : Theta2 D Y) (e : D.Edge) (t : Bool) : FiniteLaw (D.Outcome Y e) :=
  FiniteLaw.productLaw (fun g : D.GroupAt e => θ.kernel g.val t)
def observation (θ : Theta2 D Y) (e : D.Edge) : FiniteLaw (D.Outcome Y e) :=
  FiniteLaw.mixLaw (θ.prevalence (D.component e)) (θ.reference e)
@[simp] theorem reference_mass (θ : Theta2 D Y) (e : D.Edge) (t : Bool) (x : D.Outcome Y e) :
    (θ.reference e t).mass x = ∏ g, (θ.kernel g.val t).mass (x g) := rfl
@[simp] theorem observation_mass (θ : Theta2 D Y) (e : D.Edge) (x : D.Outcome Y e) :
    (θ.observation e).mass x =
      ∑ t, (θ.prevalence (D.component e)).mass t * ∏ g, (θ.kernel g.val t).mass (x g) := rfl
end Theta2

/-- Externally fixed metadata. No positivity constraint is part of gold metadata. -/
structure Anchor2 where
  group : G
  event : Y group → Prop
  sign : ℝ
  sign_valid : sign = -1 ∨ sign = 1
namespace Anchor2
variable {D Y}
def probability (a : Anchor2 Y) (θ : Theta2 D Y) (t : Bool) : ℝ :=
  (θ.kernel a.group t).prob a.event
def direction (a : Anchor2 Y) (θ : Theta2 D Y) : ℝ :=
  a.sign * (a.probability θ true - a.probability θ false)
end Anchor2

end Ext
