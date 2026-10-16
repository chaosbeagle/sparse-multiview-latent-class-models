import Cover.Interval
import Mathlib.Tactic

namespace Cover

abbrev QBox (n : Nat) := Fin n → QInterval

def QBox.Contains (B : QBox n) (x : Fin n → ℝ) : Prop := ∀ i, (B i).contains (x i)
def QBox.Valid (B : QBox n) : Prop := ∀ i, (B i).valid

def unitBox (n : Nat) : QBox n := fun _ => ⟨0, 1⟩

def splitBox (B : QBox n) (i : Fin n) (right : Bool) : QBox n :=
  fun j => if j = i then (if right then ⟨(B i).midpoint, (B i).upper⟩
    else ⟨(B i).lower, (B i).midpoint⟩) else B j

theorem midpoint_children_union_parent (B : QBox n) (i : Fin n) (x : Fin n → ℝ) :
    B.Contains x ↔ (splitBox B i false).Contains x ∨ (splitBox B i true).Contains x := by
  constructor
  · intro h
    by_cases hx : x i ≤ ((B i).midpoint : ℝ)
    · left
      intro j
      by_cases hj : j = i
      · subst j
        simpa [splitBox, QInterval.contains] using And.intro (h i).1 hx
      · simpa [splitBox, hj] using h j
    · right
      intro j
      by_cases hj : j = i
      · subst j
        simpa [splitBox, QInterval.contains] using And.intro (le_of_not_ge hx) (h i).2
      · simpa [splitBox, hj] using h j
  · rintro (h | h) j
    · by_cases hj : j = i
      · subst j
        have hi := h i
        simp only [splitBox, Bool.false_eq_true, ↓reduceIte, if_pos rfl,
          QInterval.contains, QInterval.midpoint, Rat.cast_div, Rat.cast_add,
          Rat.cast_ofNat] at hi
        constructor
        · exact hi.1
        · linarith
      · simpa [splitBox, hj] using h j
    · by_cases hj : j = i
      · subst j
        have hi := h i
        simp only [splitBox, ↓reduceIte, if_pos rfl,
          QInterval.contains, QInterval.midpoint, Rat.cast_div, Rat.cast_add,
          Rat.cast_ofNat] at hi
        constructor
        · linarith
        · exact hi.2
      · simpa [splitBox, hj] using h j

theorem splitBox_valid (B : QBox n) (hB : B.Valid) (i : Fin n) (right : Bool) :
    (splitBox B i right).Valid := by
  intro j
  by_cases hj : j = i
  · subst j
    have hi := hB i
    cases right <;> simp [splitBox, QInterval.valid, QInterval.midpoint] at * <;> linarith
  · simpa [splitBox, hj] using hB j

inductive CoverLeaf (j : Nat) where
  | exclude : Fin j → CoverLeaf j
  | gap : CoverLeaf j
  deriving DecidableEq, Repr

inductive CoverTree (n j : Nat) where
  | leaf : CoverLeaf j → CoverTree n j
  | split : Fin n → CoverTree n j → CoverTree n j → CoverTree n j
  deriving DecidableEq, Repr

namespace CoverTree

def nodes : CoverTree n j → Nat
  | .leaf _ => 1
  | .split _ l r => 1 + l.nodes + r.nodes

def leafBoxes (B : QBox n) : CoverTree n j → List (CoverLeaf j × QBox n)
  | .leaf label => [(label, B)]
  | .split i l r => l.leafBoxes (splitBox B i false) ++ r.leafBoxes (splitBox B i true)

theorem coverTree_covers_root (t : CoverTree n j) (B : QBox n) (x : Fin n → ℝ) :
    B.Contains x ↔ ∃ label box, (label, box) ∈ t.leafBoxes B ∧ box.Contains x := by
  induction t generalizing B with
  | leaf label =>
    constructor
    · intro hx
      exact ⟨label, B, by simp [leafBoxes], hx⟩
    · rintro ⟨lab, box, hmem, hx⟩
      simp only [leafBoxes, List.mem_singleton, Prod.mk.injEq] at hmem
      exact hmem.2 ▸ hx
  | split i l r ihl ihr =>
    constructor
    · intro hx
      rcases (midpoint_children_union_parent B i x).mp hx with hx | hx
      · obtain ⟨lab, box, hm, hb⟩ := (ihl _).mp hx
        exact ⟨lab, box, List.mem_append_left _ hm, hb⟩
      · obtain ⟨lab, box, hm, hb⟩ := (ihr _).mp hx
        exact ⟨lab, box, List.mem_append_right _ hm, hb⟩
    · rintro ⟨lab, box, hm, hb⟩
      apply (midpoint_children_union_parent B i x).mpr
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl ((ihl _).mpr ⟨lab, box, hm, hb⟩)
      · exact Or.inr ((ihr _).mpr ⟨lab, box, hm, hb⟩)

end CoverTree

def dyadic (k : Nat) : ℚ := (2 : ℚ)⁻¹ ^ k

theorem dyadic_pos (k : Nat) : 0 < dyadic k := by
  unfold dyadic
  positivity

def checkLeaf (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) : CoverLeaf j → Bool
  | .exclude i => decide ((gs i |>.interval cs B).upper < 0)
  | .gap => decide (dyadic (2*k) ≤ (H.interval cs B).lower)

def checkTree (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) : CoverTree n j → Bool
  | .leaf label => checkLeaf cs gs H k B label
  | .split i l r => checkTree cs gs H k (splitBox B i false) l &&
      checkTree cs gs H k (splitBox B i true) r

/-- This is a semantic predicate only. The executable checker uses the concrete interval evaluator. -/
def Encloses {n : Nat} (cs : Fin a → QInterval) (values : Fin a → ℝ) : Prop :=
  ∀ (B : QBox n) (x : Fin n → ℝ), B.Contains x →
    ∀ p : PolyExpr n a, (p.interval cs B).contains (p.eval values x)

theorem interval_encloses (cs : Fin a → QInterval) (values : Fin a → ℝ)
    (hcs : ∀ i, (cs i).contains (values i)) : Encloses (n := n) cs values := by
  intro B x hx p
  exact p.interval_sound hcs hx

theorem coverLeaf_sound (cs : Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (k : Nat) (B : QBox n)
    (label : CoverLeaf j) (hencl : Encloses (n := n) cs values)
    (hc : checkLeaf cs gs H k B label = true) (x : Fin n → ℝ)
    (hx : B.Contains x) (hfeas : ∀ i, 0 ≤ (gs i).eval values x) :
    (dyadic (2*k) : ℝ) ≤ H.eval values x := by
  cases label with
  | exclude i =>
    have he := (hencl B x hx (gs i)).2
    have hc' : ((gs i).interval cs B).upper < 0 := by simpa [checkLeaf] using hc
    have hneg : (((gs i).interval cs B).upper : ℝ) < 0 := by exact_mod_cast hc'
    exact False.elim (not_lt_of_ge (hfeas i) (lt_of_le_of_lt he hneg))
  | gap =>
    have hc' : dyadic (2*k) ≤ (H.interval cs B).lower := by simpa [checkLeaf] using hc
    have hreal : (dyadic (2*k) : ℝ) ≤ ((H.interval cs B).lower : ℝ) := by exact_mod_cast hc'
    exact hreal.trans (hencl B x hx H).1

theorem checkTree_sound (cs : Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (k : Nat)
    (hencl : Encloses (n := n) cs values) (t : CoverTree n j) (B : QBox n)
    (hc : checkTree cs gs H k B t = true) (x : Fin n → ℝ)
    (hx : B.Contains x) (hfeas : ∀ i, 0 ≤ (gs i).eval values x) :
    (dyadic (2*k) : ℝ) ≤ H.eval values x := by
  induction t generalizing B with
  | leaf label => exact coverLeaf_sound cs values gs H k B label hencl hc x hx hfeas
  | split i l r ihl ihr =>
    simp only [checkTree, Bool.and_eq_true] at hc
    rcases (midpoint_children_union_parent B i x).mp hx with hl | hr
    · exact ihl _ hc.1 hl
    · exact ihr _ hc.2 hr

end Cover

namespace Cover
/-- Concrete soundness: only the rational coefficient intervals need semantic denotations. -/
theorem verifyCoverTree_sound (cs : Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (k : Nat)
    (hcs : ∀ i, (cs i).contains (values i)) (t : CoverTree n j)
    (hc : checkTree cs gs H k (unitBox n) t = true) (x : Fin n → ℝ)
    (hx : (unitBox n).Contains x) (hfeas : ∀ i, 0 ≤ (gs i).eval values x) :
    (dyadic (2*k) : ℝ) ≤ H.eval values x :=
  checkTree_sound cs values gs H k (interval_encloses cs values hcs) t (unitBox n) hc x hx hfeas
end Cover

namespace Cover

def CoverTree.AllExclude : CoverTree n j → Prop
  | .leaf (.exclude _) => True
  | .leaf .gap => False
  | .split _ l r => l.AllExclude ∧ r.AllExclude

theorem allExclude_accepted_empty (cs : Fin a → QInterval) (values : Fin a → ℝ)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (k : Nat)
    (hcs : ∀ i, (cs i).contains (values i)) (t : CoverTree n j)
    (B : QBox n) (hall : t.AllExclude) (hc : checkTree cs gs H k B t = true) :
    ¬ ∃ x, B.Contains x ∧ ∀ i, 0 ≤ (gs i).eval values x := by
  induction t generalizing B with
  | leaf label =>
    cases label with
    | gap => exact False.elim hall
    | exclude i =>
      rintro ⟨x, hx, hf⟩
      have hi := (gs i).interval_sound hcs hx
      have hu : ((gs i).interval cs B).upper < 0 := by simpa [checkTree, checkLeaf] using hc
      have hur : (((gs i).interval cs B).upper : ℝ) < 0 := by exact_mod_cast hu
      exact not_lt_of_ge (hf i) (hi.2.trans_lt hur)
  | split i l r ihl ihr =>
    rintro ⟨x, hx, hf⟩
    simp only [checkTree, Bool.and_eq_true] at hc
    rcases (midpoint_children_union_parent B i x).mp hx with hx | hx
    · exact ihl _ hall.1 hc.1 ⟨x, hx, hf⟩
    · exact ihr _ hall.2 hc.2 ⟨x, hx, hf⟩
end Cover

namespace Cover

theorem dyadic_sq (k : Nat) : (dyadic k)^2 = dyadic (2*k) := by
  unfold dyadic
  rw [← pow_mul, Nat.mul_comm k 2]

theorem nonnegative_gap_of_squared_bound (k : Nat) (gap : ℝ) (hgap : 0 ≤ gap)
    (hbound : (dyadic (2*k) : ℝ) ≤ gap^2) : (dyadic k : ℝ) ≤ gap := by
  have hpos : (0 : ℝ) < dyadic k := by exact_mod_cast dyadic_pos k
  have hsq : (dyadic (2*k) : ℝ) = (dyadic k : ℝ)^2 := by exact_mod_cast (dyadic_sq k).symm
  rw [hsq] at hbound
  nlinarith

end Cover
