import Gen.Graph
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open scoped BigOperators Classical
noncomputable section
namespace Gen.Diagonal

variable {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]

/-- Diagonal array: only constant output strings have positive mass. -/
def diagonal (p : J → ℝ) (x : I → J) : ℝ :=
  ∑ j, if x = (fun _ => j) then p j else 0

lemma diagonal_zero (p : J → ℝ) (x : I → J)
    (h : ¬ ∃ j, x = fun _ => j) : diagonal p x = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact if_neg (fun hx => h ⟨j, hx⟩)

lemma diagonal_const [Nonempty I] (p : J → ℝ) (j : J) :
    diagonal p (fun _ : I => j) = p j := by
  classical
  have he : ∀ a : J, ((fun _ : I => j) = fun _ => a) ↔ j = a := by
    intro a
    constructor
    · intro h; exact congrFun h (Classical.arbitrary I)
    · rintro rfl; rfl
  simp [diagonal, he]

lemma exists_positive (q : J → ℝ) (hq : ∀ j, 0 ≤ q j) (ht : ∑ j, q j = 1) :
    ∃ j, 0 < q j := by
  by_contra! h
  have hz : ∀ j, q j = 0 := fun j => le_antisymm (h j) (hq j)
  simp [hz] at ht

/-- Positive terms in a nonnegative mixture cannot put mass off diagonal. -/
lemma positive_string_constant
    (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (K : I → J → Z → ℝ) (hK : ∀ i j z, 0 ≤ K i j z)
    (p : J → ℝ)
    (hobs : ∀ x, (∑ z, w z * ∏ i, K i (x i) z) = diagonal p x)
    (z : Z) (x : I → J) (hx : ∀ i, 0 < K i (x i) z) :
    ∃ j, x = fun _ => j := by
  by_contra h
  have hzero := hobs x
  rw [diagonal_zero p x h] at hzero
  have hle := Finset.single_le_sum
    (s := Finset.univ) (f := fun z => w z * ∏ i, K i (x i) z)
    (fun z _ => mul_nonneg (hw z).le (Finset.prod_nonneg fun i _ => hK i (x i) z))
    (Finset.mem_univ z)
  have hp : 0 < w z * ∏ i, K i (x i) z :=
    mul_pos (hw z) (Finset.prod_pos fun i _ => hx i)
  linarith

/-- Support collapse uses all real nonnegative normalized kernels, not a grid. -/
theorem support_collapse [Nontrivial I]
    (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (K : I → J → Z → ℝ) (hK : ∀ i j z, 0 ≤ K i j z)
    (hKt : ∀ i z, ∑ j, K i j z = 1)
    (p : J → ℝ)
    (hobs : ∀ x, (∑ z, w z * ∏ i, K i (x i) z) = diagonal p x) :
    ∃ b : Z → J, ∀ i j z, K i j z = if j = b z then 1 else 0 := by
  classical
  have hcolumn : ∀ z, ∃ b : J, ∀ i j, K i j z = if j = b then 1 else 0 := by
    intro z
    have hs : ∀ i, ∃ j, 0 < K i j z := fun i => exists_positive _ (fun j => hK i j z) (hKt i z)
    choose x hx using hs
    obtain ⟨b, hb⟩ := positive_string_constant w hw K hK p hobs z x hx
    have hxb : ∀ i, 0 < K i b z := by simpa only [hb] using hx
    have hzero : ∀ i j, j ≠ b → K i j z = 0 := by
      intro i j hj
      by_contra hz
      have hp : 0 < K i j z := lt_of_le_of_ne (hK i j z) (Ne.symm hz)
      let x' : I → J := Function.update (fun _ => b) i j
      have hx' : ∀ k, 0 < K k (x' k) z := by
        intro k
        by_cases hk : k = i
        · subst k; simpa [x'] using hp
        · simpa [x', Function.update_of_ne hk] using hxb k
      obtain ⟨c, hc⟩ := positive_string_constant w hw K hK p hobs z x' hx'
      obtain ⟨k, hki⟩ := exists_ne i
      have hci : j = c := by simpa [x'] using congrFun hc i
      have hck : b = c := by simpa [x', Function.update_of_ne hki] using congrFun hc k
      exact hj (hci.trans hck.symm)
    have hone : ∀ i, K i b z = 1 := by
      intro i
      have ht := hKt i z
      rw [Finset.sum_eq_single b] at ht
      · exact ht
      · intro j _ hj; exact hzero i j hj
      · simp
    refine ⟨b, ?_⟩
    intro i j
    by_cases hj : j = b
    · subst j; simp [hone]
    · simp [hj, hzero i j hj]
  choose b hb using hcolumn
  exact ⟨b, fun i j z => hb z i j⟩

lemma delta_product [Nonempty I] (b : J) (x : I → J) :
    (∏ i, (if x i = b then (1 : ℝ) else 0)) = if x = (fun _ => b) then 1 else 0 := by
  classical
  by_cases h : x = fun _ => b
  · simp [h]
  · rw [if_neg h]
    have hi : ∃ i, x i ≠ b := by
      by_contra! hh
      exact h (funext hh)
    obtain ⟨i, hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem local_diagonal_fiber [Nontrivial I]
    (hcard : Fintype.card Z = Fintype.card J)
    (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (K : I → J → Z → ℝ) (hK : ∀ i j z, 0 ≤ K i j z)
    (hKt : ∀ i z, ∑ j, K i j z = 1)
    (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hobs : ∀ x, (∑ z, w z * ∏ i, K i (x i) z) = diagonal p x) :
    ∃ b : Z ≃ J, (∀ z, w z = p (b z)) ∧
      ∀ i j z, K i j z = if j = b z then 1 else 0 := by
  classical
  obtain ⟨b, hb⟩ := support_collapse w hw K hK hKt p hobs
  have hmass : ∀ j, (∑ z, if j = b z then w z else 0) = p j := by
    intro j
    have ho := hobs (fun _ => j)
    simp_rw [hb, delta_product] at ho
    have he : ∀ a : J, ((fun _ : I => j) = fun _ => a) ↔ j = a := by
      intro a
      constructor
      · intro h; exact congrFun h (Classical.arbitrary I)
      · rintro rfl; rfl
    simpa [he, diagonal_const, mul_ite] using ho
  have hsurj : Function.Surjective b := by
    intro j
    by_contra! h
    have hz : (∑ z, if j = b z then w z else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      exact if_neg (Ne.symm (h z))
    have := hmass j
    rw [hz] at this
    linarith [hp j]
  have hbij : Function.Bijective b := (Fintype.bijective_iff_surjective_and_card b).2 ⟨hsurj, hcard⟩
  let e : Z ≃ J := Equiv.ofBijective b hbij
  refine ⟨e, ?_, hb⟩
  intro z
  have hm := hmass (b z)
  rw [Finset.sum_eq_single z] at hm
  · simpa [e] using hm
  · intro z' _ hne
    exact if_neg (fun he => hne (hbij.1 he).symm)
  · simp

/-- Any subset with the truth-block cardinality is realized by a latent bijection. -/
theorem exists_equiv_truth_subset (hcard : Fintype.card Z = Fintype.card J)
    (T : Finset Z) (S : Finset J) (hc : T.card = S.card) :
    ∃ b : Z ≃ J, ∀ z, z ∈ T ↔ b z ∈ S := by
  classical
  let e₁ : {z : Z // z ∈ T} ≃ {j : J // j ∈ S} :=
    Fintype.equivOfCardEq (by simpa using hc)
  let e₀ : {z : Z // z ∉ T} ≃ {j : J // j ∉ S} :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_subtype_compl]; simpa using congrArg₂ (· - ·) hcard hc)
  let b : Z ≃ J := (Equiv.sumCompl (· ∈ T)).symm |>.trans
    ((Equiv.sumCongr e₁ e₀).trans (Equiv.sumCompl (· ∈ S)))
  refine ⟨b, ?_⟩
  intro z
  by_cases hz : z ∈ T
  · have hb : b z ∈ S := by simpa [b, Equiv.sumCompl, hz] using (e₁ ⟨z,hz⟩).property
    exact ⟨fun _ => hb, fun _ => hz⟩
  · have hb : b z ∉ S := by simpa [b, Equiv.sumCompl, hz] using (e₀ ⟨z,hz⟩).property
    exact ⟨fun h => False.elim (hz h), fun h => False.elim (hb h)⟩

def subsetMass (p : J → ℝ) (S : Finset J) : ℝ := ∑ j ∈ S, p j

def eventMass (p : J → ℝ) (S B : Finset J) : ℝ := ∑ j ∈ S ∩ B, p j

def sensitivityValue (p : J → ℝ) (S R : Finset J) : ℝ :=
  eventMass p S R / subsetMass p S

def specificityValue (p : J → ℝ) (S R : Finset J) : ℝ :=
  eventMass p Sᶜ Rᶜ / (1 - subsetMass p S)

def anchorValue (p : J → ℝ) (S B : Finset J) : ℝ :=
  eventMass p S B / subsetMass p S - eventMass p Sᶜ B / (1 - subsetMass p S)

def truthWeight (w : Z → ℝ) (T : Finset Z) : ℝ := ∑ z ∈ T, w z

def truthEvent {G : Type*} (w : Z → ℝ) (K : G → J → Z → ℝ)
    (T : Finset Z) (g : G) (B : Finset J) : ℝ :=
  (∑ z ∈ T, w z * ∑ y ∈ B, K g y z) / truthWeight w T

lemma eventMass_filter (p : J → ℝ) (S B : Finset J) :
    eventMass p S B = ∑ j ∈ S, if j ∈ B then p j else 0 := by
  classical
  simp [eventMass, Finset.sum_filter]

lemma subsetMass_compl (p : J → ℝ) (ht : ∑ j, p j = 1) (S : Finset J) :
    subsetMass p Sᶜ = 1 - subsetMass p S := by
  have hh := Finset.sum_add_sum_compl S p
  unfold subsetMass
  linarith

lemma truthWeight_atom (p : J → ℝ) (b : Z ≃ J) (T : Finset Z) (S : Finset J)
    (hmem : ∀ z, z ∈ T ↔ b z ∈ S) :
    truthWeight (fun z => p (b z)) T = subsetMass p S := by
  exact Finset.sum_equiv b hmem (fun _ _ => rfl)

lemma truthEvent_atom {G : Type*} (p : J → ℝ) (b : Z ≃ J)
    (T : Finset Z) (S : Finset J) (hmem : ∀ z, z ∈ T ↔ b z ∈ S)
    (g : G) (B : Finset J) :
    truthEvent (fun z => p (b z)) (fun _ y z => if y = b z then 1 else 0) T g B =
      sensitivityValue p S B := by
  classical
  unfold truthEvent sensitivityValue
  rw [truthWeight_atom p b T S hmem, eventMass_filter]
  congr 1
  apply Finset.sum_equiv b hmem
  intro z hz
  by_cases hb : b z ∈ B <;> simp [hb]

lemma positive_subsetMass (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (S : Finset J) (hS : S.Nonempty) : 0 < subsetMass p S := by
  exact Finset.sum_pos (fun j _ => hp j) hS

lemma subsetMass_lt_one (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (ht : ∑ j, p j = 1) (S : Finset J) (hS : Sᶜ.Nonempty) : subsetMass p S < 1 := by
  have h := positive_subsetMass p hp Sᶜ hS
  rw [subsetMass_compl p ht S] at h
  linarith

section Design
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) {r : ℕ}

/-- The edge-intersection graph is connected, with its literal path relation. -/
def Connected : Prop := ∀ e f : D.Edge, Relation.ReflTransGen D.Adjacent e f

theorem connected_iff_components : Connected D ↔ ∀ e f, D.component e = D.component f := by
  simp only [Connected, D.component_eq_iff_path]

lemma triple_nontrivial (e : D.Edge) : Nontrivial (D.GroupAt e) := by
  apply Fintype.one_lt_card_iff_nontrivial.mp
  have hc : Fintype.card (D.GroupAt e) = 3 := by
    simpa only [Fintype.card_coe] using D.edge_card e.val e.property
  omega

/-- The real diagonal fiber, with every kernel and every positive weight free. -/
def FullFiber (p : J → ℝ) : Set (Gen.Parameter D (fun _ => J) r) :=
  {θ | ∀ e x, θ.observation e x = diagonal p x}

/-- Deterministic bijection parameters are a conclusion of fiber reduction. -/
def atom (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (b : Fin r ≃ J) : Gen.Parameter D (fun _ => J) r where
  weight _ z := p (b z)
  weight_pos _ z := hp (b z)
  weight_total _ := (Equiv.sum_comp b p).trans ht
  kernel _ j z := if j = b z then 1 else 0
  kernel_nonneg _ _ _ := by split_ifs <;> norm_num
  kernel_total _ _ := by simp

lemma atom_observation (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (b : Fin r ≃ J) : atom D p hp ht b ∈ FullFiber D p := by
  intro e x
  letI := triple_nontrivial D e
  simp only [Gen.Parameter.observation_formula, atom]
  simp_rw [delta_product]
  unfold diagonal
  rw [← b.sum_comp (fun j => if x = (fun _ => j) then p j else 0)]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

/-- GEN-F-DIAGONAL: full real same-r fiber equality on arbitrary finite covered connected triples. -/
theorem full_diagonal_fiber (hc : Connected D) (hcard : r = Fintype.card J)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (θ : Gen.Parameter D (fun _ => J) r) :
    θ ∈ FullFiber D p ↔ ∃ b : Fin r ≃ J, θ = atom D p hp ht b := by
  constructor
  · intro ho
    have hl : ∀ e : D.Edge, ∃ b : Fin r ≃ J,
        (∀ z, θ.weight (D.component e) z = p (b z)) ∧
        ∀ g : D.GroupAt e, ∀ j z, θ.kernel g.val j z = if j = b z then 1 else 0 := by
      intro e
      letI := triple_nontrivial D e
      exact local_diagonal_fiber (by simpa using hcard)
        (θ.weight (D.component e)) (θ.weight_pos (D.component e))
        (fun g : D.GroupAt e => θ.kernel g.val)
        (fun g => θ.kernel_nonneg g.val) (fun g => θ.kernel_total g.val) p hp (ho e)
    choose b hw hk using hl
    have hover : ∀ e f, D.Overlap e f → b e = b f := by
      intro e f hef
      obtain ⟨g, hge, hgf⟩ := hef
      apply Equiv.ext
      intro z
      have h₁ := hk e ⟨g,hge⟩ (b e z) z
      have h₂ := hk f ⟨g,hgf⟩ (b e z) z
      by_contra hne
      simp [hne] at h₁ h₂
      linarith
    have hbeq : ∀ e f, b e = b f := by
      intro e f
      have hh := (D.component_eq_iff e f).mp ((connected_iff_components D).mp hc e f)
      induction hh with
      | rel e f h => exact hover e f h
      | refl e => rfl
      | symm e f h ih => exact ih.symm
      | trans e f g h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
    let e₀ : D.Edge := Classical.choice D.edge_nonempty
    refine ⟨b e₀, ?_⟩
    apply Gen.Parameter.ext
    · funext c z
      induction c using Quotient.inductionOn with
      | h e => simpa only [atom, hbeq e e₀, Ext.TripleDesign.component] using hw e z
    · funext g j z
      simpa only [atom, hbeq (D.incident g) e₀] using
        hk (D.incident g) ⟨g,D.mem_incident g⟩ j z
  · rintro ⟨b,rfl⟩
    exact atom_observation D p hp ht b

/-- Fixed event-direction metadata; signs and group identities remain external. -/
structure EventAnchor where
  group : G
  event : Finset J
  sign : ℝ
  sign_valid : sign = -1 ∨ sign = 1

def prevalence (θ : Gen.Parameter D (fun _ => J) r) (T : Finset (Fin r)) (g : G) : ℝ :=
  truthWeight (θ.weight (D.groupComponent g)) T

def sensitivity (θ : Gen.Parameter D (fun _ => J) r)
    (T : Finset (Fin r)) (g : G) (R : Finset J) : ℝ :=
  truthEvent (θ.weight (D.groupComponent g)) θ.kernel T g R

def specificity (θ : Gen.Parameter D (fun _ => J) r)
    (T : Finset (Fin r)) (g : G) (R : Finset J) : ℝ :=
  truthEvent (θ.weight (D.groupComponent g)) θ.kernel Tᶜ g Rᶜ

variable {H : Type*} [Fintype H]

def Anchored (T : Finset (Fin r)) (A : H → EventAnchor (G := G) (J := J))
    (θ : Gen.Parameter D (fun _ => J) r) : Prop :=
  ∀ a, 0 < (A a).sign *
    (sensitivity D θ T (A a).group (A a).event -
      sensitivity D θ Tᶜ (A a).group (A a).event)

def Admissible (p : J → ℝ) (k : ℕ) (A : H → EventAnchor (G := G) (J := J)) : Set (Finset J) :=
  {S | S.card = k ∧ ∀ a, 0 < (A a).sign * anchorValue p S (A a).event}

def AnchoredFiber (p : J → ℝ) (T : Finset (Fin r)) (A : H → EventAnchor (G := G) (J := J)) :
    Set (Gen.Parameter D (fun _ => J) r) :=
  FullFiber D p ∩ {θ | Anchored D T A θ}

lemma atom_prevalence (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (b : Fin r ≃ J) (T : Finset (Fin r)) (S : Finset J)
    (hmem : ∀ z, z ∈ T ↔ b z ∈ S) (g : G) :
    prevalence D (atom D p hp ht b) T g = subsetMass p S :=
  truthWeight_atom p b T S hmem

lemma atom_sensitivity (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (b : Fin r ≃ J) (T : Finset (Fin r)) (S : Finset J)
    (hmem : ∀ z, z ∈ T ↔ b z ∈ S) (g : G) (R : Finset J) :
    sensitivity D (atom D p hp ht b) T g R = sensitivityValue p S R :=
  truthEvent_atom p b T S hmem g R

lemma atom_specificity (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (b : Fin r ≃ J) (T : Finset (Fin r)) (S : Finset J)
    (hmem : ∀ z, z ∈ T ↔ b z ∈ S) (g : G) (R : Finset J) :
    specificity D (atom D p hp ht b) T g R = specificityValue p S R := by
  have hm : ∀ z, z ∈ Tᶜ ↔ b z ∈ Sᶜ := by simpa using fun z => not_congr (hmem z)
  change sensitivity D (atom D p hp ht b) Tᶜ g Rᶜ = _
  rw [atom_sensitivity D p hp ht b Tᶜ Sᶜ hm]
  simp only [sensitivityValue, specificityValue, subsetMass_compl p ht S]

lemma atom_anchored (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (b : Fin r ≃ J) (T : Finset (Fin r)) (S : Finset J)
    (hmem : ∀ z, z ∈ T ↔ b z ∈ S) (A : H → EventAnchor (G := G) (J := J)) :
    Anchored D T A (atom D p hp ht b) ↔
      ∀ a, 0 < (A a).sign * anchorValue p S (A a).event := by
  have hm : ∀ z, z ∈ Tᶜ ↔ b z ∈ Sᶜ := by simpa using fun z => not_congr (hmem z)
  simp only [Anchored, atom_sensitivity D p hp ht b T S hmem,
    atom_sensitivity D p hp ht b Tᶜ Sᶜ hm, sensitivityValue,
    subsetMass_compl p ht S, anchorValue]

lemma image_mem (b : Fin r ≃ J) (T : Finset (Fin r)) :
    ∀ z, z ∈ T ↔ b z ∈ T.image b := by
  classical
  intro z
  simp only [Finset.mem_image, b.injective.eq_iff, exists_eq_right]

/-- Each actual full-fiber parameter yields a cardinality-k admissible subset. -/
theorem anchored_fiber_subset (hc : Connected D) (hcard : r = Fintype.card J)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (T : Finset (Fin r)) (A : H → EventAnchor (G := G) (J := J))
    (θ : Gen.Parameter D (fun _ => J) r) (hθ : θ ∈ AnchoredFiber D p T A) :
    ∃ S ∈ Admissible p T.card A,
      (∀ g R, sensitivity D θ T g R = sensitivityValue p S R) ∧
      (∀ g R, specificity D θ T g R = specificityValue p S R) ∧
      (∀ g, prevalence D θ T g = subsetMass p S) := by
  obtain ⟨b,rfl⟩ := (full_diagonal_fiber D hc hcard p hp ht θ).mp hθ.1
  let S := T.image b
  have hm : ∀ z, z ∈ T ↔ b z ∈ S := image_mem b T
  refine ⟨S, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Finset.card_image_of_injective T b.injective
  · exact (atom_anchored D p hp ht b T S hm A).mp hθ.2
  · exact atom_sensitivity D p hp ht b T S hm
  · exact atom_specificity D p hp ht b T S hm
  · exact atom_prevalence D p hp ht b T S hm

/-- Every admissible k-subset is realized in the unrestricted real model. -/
theorem subset_anchored_fiber (hcard : r = Fintype.card J)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (T : Finset (Fin r)) (A : H → EventAnchor (G := G) (J := J))
    (S : Finset J) (hS : S ∈ Admissible p T.card A) :
    ∃ θ ∈ AnchoredFiber D p T A,
      (∀ g R, sensitivity D θ T g R = sensitivityValue p S R) ∧
      (∀ g R, specificity D θ T g R = specificityValue p S R) ∧
      (∀ g, prevalence D θ T g = subsetMass p S) := by
  obtain ⟨b,hm⟩ := exists_equiv_truth_subset (by simpa using hcard) T S hS.1.symm
  refine ⟨atom D p hp ht b, ⟨atom_observation D p hp ht b,
    (atom_anchored D p hp ht b T S hm A).mpr hS.2⟩, ?_, ?_, ?_⟩
  · exact atom_sensitivity D p hp ht b T S hm
  · exact atom_specificity D p hp ht b T S hm
  · exact atom_prevalence D p hp ht b T S hm

/-- Exact finite image formulas for sensitivity, specificity, and truth prevalence. -/
theorem full_anchored_images (hc : Connected D) (hcard : r = Fintype.card J)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (T : Finset (Fin r)) (A : H → EventAnchor (G := G) (J := J)) (g : G) (R : Finset J) :
    (fun θ => sensitivity D θ T g R) '' AnchoredFiber D p T A =
      (fun S => sensitivityValue p S R) '' Admissible p T.card A ∧
    (fun θ => specificity D θ T g R) '' AnchoredFiber D p T A =
      (fun S => specificityValue p S R) '' Admissible p T.card A ∧
    (fun θ => prevalence D θ T g) '' AnchoredFiber D p T A =
      subsetMass p '' Admissible p T.card A := by
  have hf := anchored_fiber_subset D hc hcard p hp ht T A
  have hb := subset_anchored_fiber D hcard p hp ht T A
  refine ⟨?_, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨θ,hθ,rfl⟩
      obtain ⟨S,hS,hs,_,_⟩ := hf θ hθ
      exact ⟨S,hS,(hs g R).symm⟩
    · rintro ⟨S,hS,rfl⟩
      obtain ⟨θ,hθ,hs,_,_⟩ := hb S hS
      exact ⟨θ,hθ,hs g R⟩
  · ext v
    constructor
    · rintro ⟨θ,hθ,rfl⟩
      obtain ⟨S,hS,_,hs,_⟩ := hf θ hθ
      exact ⟨S,hS,(hs g R).symm⟩
    · rintro ⟨S,hS,rfl⟩
      obtain ⟨θ,hθ,_,hs,_⟩ := hb S hS
      exact ⟨θ,hθ,hs g R⟩
  · ext v
    constructor
    · rintro ⟨θ,hθ,rfl⟩
      obtain ⟨S,hS,_,_,hs⟩ := hf θ hθ
      exact ⟨S,hS,(hs g).symm⟩
    · rintro ⟨S,hS,rfl⟩
      obtain ⟨θ,hθ,_,_,hs⟩ := hb S hS
      exact ⟨θ,hθ,hs g⟩

/-- Every recovered deterministic kernel has all r columns linearly independent. -/
lemma atom_full_rank (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (b : Fin r ≃ J) (g : G) :
    LinearIndependent ℝ (fun z y => (atom D p hp ht b).kernel g y z) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc z
  have hh := congrFun hc (b z)
  simpa [atom, Finset.sum_apply, Pi.smul_apply, b.injective.eq_iff, eq_comm] using hh

theorem full_fiber_rank (hc : Connected D) (hcard : r = Fintype.card J)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (θ : Gen.Parameter D (fun _ => J) r) (hθ : θ ∈ FullFiber D p) (g : G) :
    LinearIndependent ℝ (fun z y => θ.kernel g y z) := by
  obtain ⟨b,rfl⟩ := (full_diagonal_fiber D hc hcard p hp ht θ).mp hθ
  exact atom_full_rank D p hp ht b g

/-- The named truth-kernel agrees with the normalized block mixture in GEN-D04. -/
def truthKernel (θ : Gen.Parameter D (fun _ => J) r)
    (T : Finset (Fin r)) (g : G) (y : J) : ℝ :=
  (∑ z ∈ T, θ.weight (D.groupComponent g) z * θ.kernel g y z) / prevalence D θ T g

lemma sensitivity_eq_sum_truthKernel (θ : Gen.Parameter D (fun _ => J) r)
    (T : Finset (Fin r)) (g : G) (R : Finset J) :
    sensitivity D θ T g R = ∑ y ∈ R, truthKernel D θ T g y := by
  simp only [sensitivity, truthEvent, truthKernel, prevalence, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  exact Finset.mul_sum R (fun y => θ.kernel g y z) (θ.weight (D.groupComponent g) z)

lemma semantic_denominators (θ : Gen.Parameter D (fun _ => J) r)
    (T : Finset (Fin r)) (hT : T.Nonempty) (hTc : Tᶜ.Nonempty) (g : G) :
    0 < prevalence D θ T g ∧ prevalence D θ T g < 1 := by
  refine ⟨positive_subsetMass _ (θ.weight_pos _) T hT, ?_⟩
  have hp0 : 0 < ∑ z ∈ Tᶜ, θ.weight (D.groupComponent g) z :=
    Finset.sum_pos (fun z _ => θ.weight_pos _ z) hTc
  have he : prevalence D θ T g + (∑ z ∈ Tᶜ, θ.weight (D.groupComponent g) z) = 1 := by
    exact (Finset.sum_add_sum_compl T (θ.weight (D.groupComponent g))).trans (θ.weight_total _)
  linarith

lemma truthKernel_nonneg (θ : Gen.Parameter D (fun _ => J) r)
    (T : Finset (Fin r)) (hT : T.Nonempty) (g : G) (y : J) :
    0 ≤ truthKernel D θ T g y := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun z _ => mul_nonneg (θ.weight_pos _ z).le (θ.kernel_nonneg g y z)
  · exact (positive_subsetMass _ (θ.weight_pos _) T hT).le

lemma truthKernel_total (θ : Gen.Parameter D (fun _ => J) r)
    (T : Finset (Fin r)) (hT : T.Nonempty) (g : G) :
    ∑ y, truthKernel D θ T g y = 1 := by
  simp only [truthKernel, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, θ.kernel_total, mul_one]
  exact div_self (ne_of_gt (positive_subsetMass _ (θ.weight_pos _) T hT))

/-- A surjective binary truth map is exactly a nonempty proper truth-one block. -/
def truthOne (τ : Fin r → Bool) : Finset (Fin r) := Finset.univ.filter (fun z => τ z = true)

lemma truthOne_blocks (τ : Fin r → Bool) (hτ : Function.Surjective τ) :
    (truthOne τ).Nonempty ∧ (truthOne τ)ᶜ.Nonempty := by
  obtain ⟨z₁,h₁⟩ := hτ true
  obtain ⟨z₀,h₀⟩ := hτ false
  exact ⟨⟨z₁, by simp [truthOne,h₁]⟩, ⟨z₀, by simp [truthOne,h₀]⟩⟩

lemma truthOne_compl (τ : Fin r → Bool) (z : Fin r) :
    z ∈ (truthOne τ)ᶜ ↔ τ z = false := by
  cases h : τ z <;> simp [truthOne,h]

lemma truthOne_card (τ : Fin r → Bool) (hτ : Function.Surjective τ) :
    1 ≤ (truthOne τ).card ∧ (truthOne τ).card < r := by
  obtain ⟨h₁,h₀⟩ := truthOne_blocks τ hτ
  have h₁' := Finset.card_pos.mpr h₁
  have h₀' := Finset.card_pos.mpr h₀
  rw [Finset.card_compl, Fintype.card_fin] at h₀'
  omega

/-- Empty admissible subset family is exactly empty anchored full real fiber. -/
theorem anchored_empty_iff (hc : Connected D) (hcard : r = Fintype.card J)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (T : Finset (Fin r)) (A : H → EventAnchor (G := G) (J := J)) :
    AnchoredFiber D p T A = ∅ ↔ Admissible p T.card A = ∅ := by
  constructor
  · intro he
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨θ,hθ,_⟩ := subset_anchored_fiber D hcard p hp ht T A S hS
    simpa [he] using hθ
  · intro he
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro θ hθ
    obtain ⟨S,hS,_⟩ := anchored_fiber_subset D hc hcard p hp ht T A θ hθ
    simpa [he] using hS

end Design

/-- A finite full-model functional image, with actual parameters at both sharp endpoints. -/
def SharpAttained {M : Type*} (f : M → ℝ) (P : Set M) : Prop :=
  (f '' P).Finite ∧ ∃ θlo ∈ P, ∃ θhi ∈ P,
    f θlo = sInf (f '' P) ∧ f θhi = sSup (f '' P) ∧
      ∀ θ ∈ P, f θlo ≤ f θ ∧ f θ ≤ f θhi

lemma sharpAttained_of_finite {M : Type*} (f : M → ℝ) (P : Set M)
    (hf : (f '' P).Finite) (hn : P.Nonempty) : SharpAttained f P := by
  have him : (f '' P).Nonempty := hn.image f
  let F := hf.toFinset
  have hF : F.Nonempty := hf.toFinset_nonempty.mpr him
  have hl : IsLeast (f '' P) (F.min' hF) := by
    simpa only [F, Set.Finite.coe_toFinset] using Finset.isLeast_min' F hF
  have hu : IsGreatest (f '' P) (F.max' hF) := by
    simpa only [F, Set.Finite.coe_toFinset] using Finset.isGreatest_max' F hF
  obtain ⟨θl,hθl,heql⟩ := hl.1
  obtain ⟨θu,hθu,hequ⟩ := hu.1
  refine ⟨hf, θl, hθl, θu, hθu, ?_, ?_, ?_⟩
  · exact heql.trans hl.csInf_eq.symm
  · exact hequ.trans hu.csSup_eq.symm
  · intro θ hθ
    exact ⟨heql ▸ hl.2 ⟨θ,hθ,rfl⟩, hequ ▸ hu.2 ⟨θ,hθ,rfl⟩⟩

section Sharp
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) {r : ℕ} {H : Type*} [Fintype H]

/-- The three displayed finite images give attained sharp lower and upper bounds in the full model. -/
theorem full_anchored_sharp (hc : Connected D) (hcard : r = Fintype.card J)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (T : Finset (Fin r)) (A : H → EventAnchor (G := G) (J := J)) (g : G) (R : Finset J)
    (hn : (Admissible p T.card A).Nonempty) :
    SharpAttained (fun θ => sensitivity D θ T g R) (AnchoredFiber D p T A) ∧
    SharpAttained (fun θ => specificity D θ T g R) (AnchoredFiber D p T A) ∧
    SharpAttained (fun θ => prevalence D θ T g) (AnchoredFiber D p T A) := by
  obtain ⟨S,hS⟩ := hn
  obtain ⟨θ,hθ,_⟩ := subset_anchored_fiber D hcard p hp ht T A S hS
  have hnon : (AnchoredFiber D p T A).Nonempty := ⟨θ,hθ⟩
  obtain ⟨hs,hsp,hpim⟩ := full_anchored_images D hc hcard p hp ht T A g R
  have hfin : (Admissible p T.card A).Finite := Set.toFinite _
  refine ⟨sharpAttained_of_finite _ _ ?_ hnon,
    sharpAttained_of_finite _ _ ?_ hnon, sharpAttained_of_finite _ _ ?_ hnon⟩
  · rw [hs]; exact hfin.image _
  · rw [hsp]; exact hfin.image _
  · rw [hpim]; exact hfin.image _

/-- GEN-F-DIAGONAL, packaged under the literal surjective binary truth metadata.
The auxiliary theorems allow an arbitrary block; this final theorem restricts it to
exactly the nonempty proper block required in the accepted statement. -/
theorem GEN_F_DIAGONAL (hc : Connected D) (hr : 2 ≤ r) (hcard : r = Fintype.card J)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (ht : ∑ j, p j = 1)
    (τ : Fin r → Bool) (hτ : Function.Surjective τ)
    (A : H → EventAnchor (G := G) (J := J)) (g : G) (R : Finset J) :
    (∀ θ : Gen.Parameter D (fun _ => J) r,
      θ ∈ FullFiber D p ↔ ∃ b : Fin r ≃ J, θ = atom D p hp ht b) ∧
    (∀ θ : Gen.Parameter D (fun _ => J) r, θ ∈ FullFiber D p →
      ∀ g, LinearIndependent ℝ (fun z y => θ.kernel g y z)) ∧
    (1 ≤ (truthOne τ).card ∧ (truthOne τ).card < r) ∧
    (∀ θ : Gen.Parameter D (fun _ => J) r, ∀ g,
      0 < prevalence D θ (truthOne τ) g ∧ prevalence D θ (truthOne τ) g < 1) ∧
    ((fun θ => sensitivity D θ (truthOne τ) g R) '' AnchoredFiber D p (truthOne τ) A =
      (fun S => sensitivityValue p S R) '' Admissible p (truthOne τ).card A) ∧
    ((fun θ => specificity D θ (truthOne τ) g R) '' AnchoredFiber D p (truthOne τ) A =
      (fun S => specificityValue p S R) '' Admissible p (truthOne τ).card A) ∧
    ((fun θ => prevalence D θ (truthOne τ) g) '' AnchoredFiber D p (truthOne τ) A =
      subsetMass p '' Admissible p (truthOne τ).card A) ∧
    (AnchoredFiber D p (truthOne τ) A = ∅ ↔ Admissible p (truthOne τ).card A = ∅) ∧
    ((Admissible p (truthOne τ).card A).Nonempty →
      SharpAttained (fun θ => sensitivity D θ (truthOne τ) g R) (AnchoredFiber D p (truthOne τ) A) ∧
      SharpAttained (fun θ => specificity D θ (truthOne τ) g R) (AnchoredFiber D p (truthOne τ) A) ∧
      SharpAttained (fun θ => prevalence D θ (truthOne τ) g) (AnchoredFiber D p (truthOne τ) A)) := by
  obtain ⟨hT,hTc⟩ := truthOne_blocks τ hτ
  obtain ⟨hs,hsp,hprev⟩ := full_anchored_images D hc hcard p hp ht (truthOne τ) A g R
  refine ⟨full_diagonal_fiber D hc hcard p hp ht,
    fun θ hθ g => full_fiber_rank D hc hcard p hp ht θ hθ g,
    truthOne_card τ hτ, ?_, hs, hsp, hprev,
    anchored_empty_iff D hc hcard p hp ht (truthOne τ) A,
    full_anchored_sharp D hc hcard p hp ht (truthOne τ) A g R⟩
  intro θ g
  exact semantic_denominators D θ (truthOne τ) hT hTc g

end Sharp
end Gen.Diagonal
