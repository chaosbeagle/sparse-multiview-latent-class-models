import Ext.Model2
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open scoped BigOperators Classical
noncomputable section
namespace Gen

variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G) (Y : G → Type*) [∀ g, Fintype (Y g)] (r : ℕ)

/-- GEN-D02: the full real same-state-count model. No rank or margin premise is bundled. -/
@[ext] structure Parameter where
  weight : D.Component → Fin r → ℝ
  weight_pos : ∀ c z, 0 < weight c z
  weight_total : ∀ c, ∑ z, weight c z = 1
  kernel : (g : G) → Y g → Fin r → ℝ
  kernel_nonneg : ∀ g y z, 0 ≤ kernel g y z
  kernel_total : ∀ g z, ∑ y, kernel g y z = 1

abbrev W := D.Component → Equiv.Perm (Fin r)

namespace Parameter
variable {D Y r}

def weightLaw (θ : Parameter D Y r) (c : D.Component) : Ext.FiniteLaw (Fin r) :=
  ⟨θ.weight c, fun z => (θ.weight_pos c z).le, θ.weight_total c⟩
def kernelLaw (θ : Parameter D Y r) (g : G) (z : Fin r) : Ext.FiniteLaw (Y g) :=
  ⟨fun y => θ.kernel g y z, fun y => θ.kernel_nonneg g y z, θ.kernel_total g z⟩
def observationLaw (θ : Parameter D Y r) (e : D.Edge) :
    Ext.FiniteLaw (D.Outcome Y e) :=
  Ext.FiniteLaw.mixLaw (θ.weightLaw (D.component e))
    (fun z => Ext.FiniteLaw.productLaw (fun g : D.GroupAt e => θ.kernelLaw g.val z))
def observation (θ : Parameter D Y r) (e : D.Edge) (x : D.Outcome Y e) : ℝ :=
  (θ.observationLaw e).mass x
@[simp] theorem observation_formula (θ : Parameter D Y r) (e : D.Edge) (x : D.Outcome Y e) :
    θ.observation e x = ∑ z, θ.weight (D.component e) z * ∏ g : D.GroupAt e,
      θ.kernel g.val (x g) z := rfl

theorem observation_nonneg (θ : Parameter D Y r) (e : D.Edge) (x : D.Outcome Y e) :
    0 ≤ θ.observation e x := (θ.observationLaw e).nonneg x
theorem observation_total (θ : Parameter D Y r) (e : D.Edge) :
    ∑ x, θ.observation e x = 1 := (θ.observationLaw e).total

/-- The componentwise pullback action, with composition in the right-action order. -/
def permute (θ : Parameter D Y r) (q : W D r) : Parameter D Y r where
  weight c z := θ.weight c (q c z)
  weight_pos c z := θ.weight_pos c (q c z)
  weight_total c := by simpa using Equiv.sum_comp (q c) (θ.weight c) |>.trans (θ.weight_total c)
  kernel g y z := θ.kernel g y (q (D.groupComponent g) z)
  kernel_nonneg g y z := θ.kernel_nonneg g y _
  kernel_total g z := θ.kernel_total g _

@[simp] theorem permute_weight (θ : Parameter D Y r) (q : W D r) (c) (z) :
    (θ.permute q).weight c z = θ.weight c (q c z) := rfl
@[simp] theorem permute_kernel (θ : Parameter D Y r) (q : W D r) (g) (y) (z) :
    (θ.permute q).kernel g y z = θ.kernel g y (q (D.groupComponent g) z) := rfl
@[simp] theorem permute_one (θ : Parameter D Y r) : θ.permute 1 = θ := by ext <;> rfl
/-- S_p(S_q θ) = S_(q ∘ p) θ. -/
theorem permute_comp (θ : Parameter D Y r) (q p : W D r) :
    (θ.permute q).permute p = θ.permute (q * p) := by ext <;> rfl
@[simp] theorem permute_observation (θ : Parameter D Y r) (q : W D r)
    (e : D.Edge) (x : D.Outcome Y e) :
    (θ.permute q).observation e x = θ.observation e x := by
  simp only [observation_formula, permute_weight, permute_kernel]
  simp_rw [D.groupComponent_eq e]
  exact Equiv.sum_comp (q (D.component e))
    (fun z => θ.weight (D.component e) z * ∏ g : D.GroupAt e, θ.kernel g.val (x g) z)

end Parameter

/-- GEN-D03: arbitrary information, without any invariance or decidability assumption. -/
def fiber (θ : Parameter D Y r) (A : Parameter D Y r → Prop) : Set (Parameter D Y r) :=
  {η | (∀ e x, η.observation e x = θ.observation e x) ∧ A η}
def orbit (θ : Parameter D Y r) (Γ : Subgroup (W D r)) : Set (Parameter D Y r) :=
  {η | ∃ q ∈ Γ, η = θ.permute q}
def IdentifiesModulo (θ : Parameter D Y r) (A : Parameter D Y r → Prop)
    (Γ : Subgroup (W D r)) : Prop :=
  fiber D Y r θ A = orbit D Y r θ Γ ∩ {η | A η}


variable {D Y r}

/-- A local competitor has arbitrary real normalized factors and positive weights. -/
structure LocalSystem (e : D.Edge) where
  weight : Fin r → ℝ
  weight_pos : ∀ z, 0 < weight z
  weight_total : ∑ z, weight z = 1
  kernel : (g : D.GroupAt e) → Y g.val → Fin r → ℝ
  kernel_nonneg : ∀ g y z, 0 ≤ kernel g y z
  kernel_total : ∀ g z, ∑ y, kernel g y z = 1

def LocalSystem.observation {e : D.Edge} (η : LocalSystem (Y := Y) (r := r) e)
    (x : D.Outcome Y e) : ℝ :=
  ∑ z, η.weight z * ∏ g, η.kernel g (x g) z

def Parameter.local (θ : Parameter D Y r) (e : D.Edge) : LocalSystem (Y := Y) (r := r) e where
  weight := θ.weight (D.component e)
  weight_pos := θ.weight_pos (D.component e)
  weight_total := θ.weight_total (D.component e)
  kernel g := θ.kernel g.val
  kernel_nonneg g := θ.kernel_nonneg g.val
  kernel_total g := θ.kernel_total g.val

/-- GEN-D05's explicit local-rigidity premise, with no competitor rank restriction. -/
def LocalRigid (θ : Parameter D Y r) (e : D.Edge) : Prop :=
  ∀ η : LocalSystem (Y := Y) (r := r) e,
    (∀ x, η.observation x = θ.observation e x) →
    ∃ q : Equiv.Perm (Fin r),
      (∀ z, η.weight z = θ.weight (D.component e) (q z)) ∧
      ∀ g y z, η.kernel g y z = θ.kernel g.val y (q z)

/-- Stabilizers include the weights. This is a subgroup by exact pullback composition. -/
def edgeStabilizer (θ : Parameter D Y r) (e : D.Edge) : Subgroup (Equiv.Perm (Fin r)) where
  carrier q := (∀ z, θ.weight (D.component e) (q z) = θ.weight (D.component e) z) ∧
    ∀ (g : D.GroupAt e) y z, θ.kernel g.val y (q z) = θ.kernel g.val y z
  one_mem' := ⟨fun _ => rfl, fun _ _ _ => rfl⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨fun z => (ha.1 (b z)).trans (hb.1 z),
      fun g y z => (ha.2 g y (b z)).trans (hb.2 g y z)⟩
  inv_mem' := by
    intro a ha
    constructor
    · intro z; simpa using (ha.1 (a⁻¹ z)).symm
    · intro g y z; simpa using (ha.2 g y (a⁻¹ z)).symm

def overlapStabilizer (θ : Parameter D Y r) (e f : D.Edge) :
    Subgroup (Equiv.Perm (Fin r)) where
  carrier q := (∀ z, θ.weight (D.component e) (q z) = θ.weight (D.component e) z) ∧
    ∀ (g : G), g ∈ e.val → g ∈ f.val → ∀ y z, θ.kernel g y (q z) = θ.kernel g y z
  one_mem' := ⟨fun _ => rfl, fun _ _ _ _ _ => rfl⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨fun z => (ha.1 (b z)).trans (hb.1 z),
      fun g he hf y z => (ha.2 g he hf y (b z)).trans (hb.2 g he hf y z)⟩
  inv_mem' := by
    intro a ha
    constructor
    · intro z; simpa using (ha.1 (a⁻¹ z)).symm
    · intro g he hf y z; simpa using (ha.2 g he hf y (a⁻¹ z)).symm

/-- The order q_e ∘ q_f⁻¹ is literal, never commuted. -/
def Compatible (θ : Parameter D Y r) (q : D.Edge → Equiv.Perm (Fin r)) : Prop :=
  ∀ e f, D.Adjacent e f → q e * (q f)⁻¹ ∈ overlapStabilizer θ e f

lemma pullback_eq_iff {Z V : Type*} (F : Z → V) (a b : Equiv.Perm Z) :
    (∀ z, F (a z) = F (b z)) ↔ ∀ z, F ((a * b⁻¹) z) = F z := by
  constructor
  · intro h z
    simpa using h (b⁻¹ z)
  · intro h z
    simpa using h (b z)

lemma compatible_overlap (θ : Parameter D Y r) {q : D.Edge → Equiv.Perm (Fin r)}
    (h : Compatible θ q) {e f : D.Edge} (hef : D.Overlap e f) :
    (∀ z, θ.weight (D.component e) (q e z) = θ.weight (D.component f) (q f z)) ∧
    ∀ g, g ∈ e.val → g ∈ f.val → ∀ y z,
      θ.kernel g y (q e z) = θ.kernel g y (q f z) := by
  by_cases heq : e = f
  · subst f; exact ⟨fun _ => rfl, fun _ _ _ _ _ => rfl⟩
  · have hh := h e f ⟨heq, hef⟩
    constructor
    · rw [← D.overlap_component_eq hef]
      exact (pullback_eq_iff _ _ _).mpr hh.1
    · intro g hge hgf y
      exact (pullback_eq_iff _ _ _).mpr (hh.2 g hge hgf y)

lemma compatible_weight_path (θ : Parameter D Y r) {q : D.Edge → Equiv.Perm (Fin r)}
    (h : Compatible θ q) {e f : D.Edge} (hef : D.component e = D.component f) :
    ∀ z, θ.weight (D.component e) (q e z) = θ.weight (D.component f) (q f z) := by
  have hp := (D.component_eq_iff e f).mp hef
  clear hef
  induction hp with
  | rel e f hrel => exact (compatible_overlap θ h hrel).1
  | refl e => exact fun _ => rfl
  | symm e f hrel ih => exact fun z => (ih z).symm
  | trans e f k h₁ h₂ ih₁ ih₂ => exact fun z => (ih₁ z).trans (ih₂ z)

/-- Choice of representative is followed by a proof of choice-independence. -/
def componentEdge (c : D.Component) : D.Edge := Quotient.out c
@[simp] theorem component_componentEdge (c : D.Component) :
    D.component (componentEdge c) = c := Quotient.out_eq c

/-- The displayed representative arrays are well-defined by the following edge equations. -/
def assemble (θ : Parameter D Y r) (q : D.Edge → Equiv.Perm (Fin r)) : Parameter D Y r where
  weight c z := θ.weight c (q (componentEdge c) z)
  weight_pos c z := θ.weight_pos c _
  weight_total c := (Equiv.sum_comp (q (componentEdge c)) (θ.weight c)).trans (θ.weight_total c)
  kernel g y z := θ.kernel g y (q (D.incident g) z)
  kernel_nonneg g y z := θ.kernel_nonneg g y _
  kernel_total g z := θ.kernel_total g _

/-- Well-definedness on every edge, including component weights propagated along paths. -/
theorem assemble_on_edge (θ : Parameter D Y r) {q : D.Edge → Equiv.Perm (Fin r)}
    (h : Compatible θ q) (e : D.Edge) :
    (∀ z, (assemble θ q).weight (D.component e) z = θ.weight (D.component e) (q e z)) ∧
    ∀ (g : D.GroupAt e) y z, (assemble θ q).kernel g.val y z = θ.kernel g.val y (q e z) := by
  constructor
  · intro z
    have hh := compatible_weight_path θ h
      (component_componentEdge (D.component e)) z
    simpa only [component_componentEdge, assemble] using hh
  · intro g y z
    exact (compatible_overlap θ h ⟨g.val, D.mem_incident g.val, g.property⟩).2
      g.val (D.mem_incident g.val) g.property y z

lemma assemble_observation (θ : Parameter D Y r) {q : D.Edge → Equiv.Perm (Fin r)}
    (h : Compatible θ q) (e : D.Edge) (x : D.Outcome Y e) :
    (assemble θ q).observation e x = θ.observation e x := by
  simp only [Parameter.observation_formula]
  simp_rw [(assemble_on_edge θ h e).1, (assemble_on_edge θ h e).2]
  exact Equiv.sum_comp (q e)
    (fun z => θ.weight (D.component e) z * ∏ g : D.GroupAt e, θ.kernel g.val (x g) z)


/-- Coverage makes equality of every edge restriction equality of complete arrays. -/
theorem edgewise_ext (θ η : Parameter D Y r)
    (hw : ∀ e z, θ.weight (D.component e) z = η.weight (D.component e) z)
    (hk : ∀ e (g : D.GroupAt e) y z, θ.kernel g.val y z = η.kernel g.val y z) : θ = η := by
  apply Parameter.ext
  · funext c z
    simpa only [component_componentEdge] using hw (componentEdge c) z
  · funext g y z
    exact hk (D.incident g) ⟨g, D.mem_incident g⟩ y z

def EdgeMatch (θ η : Parameter D Y r) (q : D.Edge → Equiv.Perm (Fin r)) : Prop :=
  ∀ e, (∀ z, η.weight (D.component e) z = θ.weight (D.component e) (q e z)) ∧
    ∀ (g : D.GroupAt e) y z, η.kernel g.val y z = θ.kernel g.val y (q e z)

lemma edgeMatch_compatible (θ η : Parameter D Y r) {q : D.Edge → Equiv.Perm (Fin r)}
    (hm : EdgeMatch θ η q) : Compatible θ q := by
  intro e f hef
  constructor
  · apply (pullback_eq_iff _ _ _).mp
    intro z
    rw [← (hm e).1 z, D.overlap_component_eq hef.2, (hm f).1 z]
  · intro g hge hgf y
    apply (pullback_eq_iff _ _ _).mp
    intro z
    exact ((hm e).2 ⟨g, hge⟩ y z).symm.trans ((hm f).2 ⟨g, hgf⟩ y z)

/-- GEN-G-SYNC.1: equality with the compatible assembled image in the full real fiber. -/
theorem fiber_eq_compatible_image (θ : Parameter D Y r) (A : Parameter D Y r → Prop)
    (hRigid : ∀ e, LocalRigid θ e) :
    fiber D Y r θ A =
      {η | ∃ q, Compatible θ q ∧ A (assemble θ q) ∧ η = assemble θ q} := by
  ext η
  constructor
  · rintro ⟨ho, hA⟩
    have hall : ∀ e, ∃ q : Equiv.Perm (Fin r),
        (∀ z, η.weight (D.component e) z = θ.weight (D.component e) (q z)) ∧
        ∀ (g : D.GroupAt e) y z, η.kernel g.val y z = θ.kernel g.val y (q z) := by
      intro e
      exact hRigid e (η.local e) (ho e)
    choose q hq using hall
    have hc : Compatible θ q := edgeMatch_compatible θ η hq
    have heq : η = assemble θ q := edgewise_ext η (assemble θ q)
      (fun e z => ((hq e).1 z).trans ((assemble_on_edge θ hc e).1 z).symm)
      (fun e g y z => ((hq e).2 g y z).trans ((assemble_on_edge θ hc e).2 g y z).symm)
    exact ⟨q, hc, heq ▸ hA, heq⟩
  · rintro ⟨q, hc, hA, rfl⟩
    exact ⟨assemble_observation θ hc, hA⟩

/-- Every exact edge stabilizer test is equivalent to full array equality with a gauge image. -/
theorem assemble_eq_permute_iff (θ : Parameter D Y r)
    {q : D.Edge → Equiv.Perm (Fin r)} (hc : Compatible θ q) (γ : W D r) :
    assemble θ q = θ.permute γ ↔
      ∀ e, q e * (γ (D.component e))⁻¹ ∈ edgeStabilizer θ e := by
  constructor
  · intro heq e
    constructor
    · apply (pullback_eq_iff _ _ _).mp
      intro z
      rw [← (assemble_on_edge θ hc e).1 z, heq]
      rfl
    · intro g y
      apply (pullback_eq_iff _ _ _).mp
      intro z
      rw [← (assemble_on_edge θ hc e).2 g y z, heq]
      simp only [Parameter.permute_kernel, D.groupComponent_eq e g]
  · intro h
    apply edgewise_ext
    · intro e z
      exact ((assemble_on_edge θ hc e).1 z).trans
        (((pullback_eq_iff _ _ _).mpr (h e).1) z)
    · intro e g y z
      rw [(assemble_on_edge θ hc e).2 g y z]
      simp only [Parameter.permute_kernel, D.groupComponent_eq e g]
      exact ((pullback_eq_iff _ _ _).mpr ((h e).2 g y)) z

/-- GEN-G-SYNC.2: arbitrary A and arbitrary subgroup, with the exact ∀q∃γ∀e order. -/
theorem identifies_iff_compatible_mod_gauge (θ : Parameter D Y r)
    (A : Parameter D Y r → Prop) (_hA : A θ) (Γ : Subgroup (W D r))
    (hRigid : ∀ e, LocalRigid θ e) :
    IdentifiesModulo D Y r θ A Γ ↔
      ∀ q, Compatible θ q → A (assemble θ q) →
        ∃ γ ∈ Γ, ∀ e, q e * (γ (D.component e))⁻¹ ∈ edgeStabilizer θ e := by
  constructor
  · intro hid q hc hAq
    have hf : assemble θ q ∈ fiber D Y r θ A := ⟨assemble_observation θ hc, hAq⟩
    rw [hid] at hf
    obtain ⟨⟨γ, hγ, heq⟩, _⟩ := hf
    exact ⟨γ, hγ, (assemble_eq_permute_iff θ hc γ).mp heq⟩
  · intro h
    apply Set.ext
    intro η
    constructor
    · intro hf
      have himage := hf
      rw [fiber_eq_compatible_image θ A hRigid] at himage
      obtain ⟨q, hc, hAq, rfl⟩ := himage
      obtain ⟨γ, hγ, hs⟩ := h q hc hAq
      exact ⟨⟨γ, hγ, (assemble_eq_permute_iff θ hc γ).mpr hs⟩, hAq⟩
    · rintro ⟨⟨γ, hγ, rfl⟩, hAγ⟩
      exact ⟨θ.permute_observation γ, hAγ⟩


/-- Actual Kruskal independence quantifies over every k-column subset. -/
def KruskalIndependent (θ : Parameter D Y r) (g : G) (k : ℕ) : Prop :=
  ∀ s : Finset (Fin r), s.card = k →
    LinearIndependent ℝ (fun z : s => fun y => θ.kernel g y z.val)

/-- The maximum among the finitely many possible column counts 0,...,r. -/
def kruskalRank (θ : Parameter D Y r) (g : G) : ℕ :=
  ((Finset.range (r + 1)).filter (KruskalIndependent θ g)).sup id

def KCond (θ : Parameter D Y r) (e : D.Edge) : Prop :=
  2 * r + 2 ≤ ∑ g : D.GroupAt e, kruskalRank θ g.val

/-- This pointwise property is a consequence needed after local uniqueness, not a
    replacement for the unproved generic Kruskal tensor theorem. -/
def DistinctColumns (θ : Parameter D Y r) : Prop :=
  ∀ g, Function.Injective (fun z : Fin r => fun y => θ.kernel g y z)

lemma compatible_constant_overlap (θ : Parameter D Y r) (hd : DistinctColumns θ)
    {q : D.Edge → Equiv.Perm (Fin r)} (hc : Compatible θ q)
    {e f : D.Edge} (hef : D.Overlap e f) : q e = q f := by
  obtain ⟨g, hge, hgf⟩ := hef
  apply Equiv.ext
  intro z
  apply hd g
  funext y
  exact (compatible_overlap θ hc ⟨g, hge, hgf⟩).2 g hge hgf y z

lemma compatible_constant_component (θ : Parameter D Y r) (hd : DistinctColumns θ)
    {q : D.Edge → Equiv.Perm (Fin r)} (hc : Compatible θ q)
    {e f : D.Edge} (hef : D.component e = D.component f) : q e = q f := by
  have hp := (D.component_eq_iff e f).mp hef
  clear hef
  induction hp with
  | rel e f hrel => exact compatible_constant_overlap θ hd hc hrel
  | refl e => rfl
  | symm e f hrel ih => exact ih.symm
  | trans e f k h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma assemble_eq_component_permutation (θ : Parameter D Y r) (hd : DistinctColumns θ)
    {q : D.Edge → Equiv.Perm (Fin r)} (hc : Compatible θ q) :
    assemble θ q = θ.permute (fun c => q (componentEdge c)) := by
  apply Parameter.ext
  · rfl
  · funext g y z
    change θ.kernel g y (q (D.incident g) z) =
      θ.kernel g y (q (componentEdge (D.groupComponent g)) z)
    rw [compatible_constant_component θ hd hc
      (component_componentEdge (D.groupComponent g)).symm]

lemma exists_group_component (c : D.Component) : ∃ g : G, D.groupComponent g = c := by
  let e := componentEdge c
  have hcard : 0 < e.val.card := by rw [D.edge_card e.val e.property]; decide
  obtain ⟨g, hg⟩ := Finset.card_pos.mp hcard
  exact ⟨g, (D.groupComponent_eq e ⟨g, hg⟩).trans (component_componentEdge c)⟩

/-- Distinct columns imply freeness on complete parameter arrays, component by component. -/
theorem component_orbit_free (θ : Parameter D Y r) (hd : DistinctColumns θ) :
    Function.Injective θ.permute := by
  intro p q heq
  funext c
  apply Equiv.ext
  intro z
  obtain ⟨g, hg⟩ := exists_group_component c
  apply hd g
  funext y
  have h := congrArg (fun η : Parameter D Y r => η.kernel g y z) heq
  simpa only [Parameter.permute_kernel, hg] using h

/-- Conditional downstream synchronization; this declaration does not assert KCond⇒LocalRigid. -/
theorem fiber_eq_component_orbit_of_localRigid (θ : Parameter D Y r)
    (hRigid : ∀ e, LocalRigid θ e) (hd : DistinctColumns θ) :
    fiber D Y r θ (fun _ => True) = orbit D Y r θ ⊤ := by
  rw [fiber_eq_compatible_image θ (fun _ => True) hRigid]
  ext η
  constructor
  · rintro ⟨q, hc, _, rfl⟩
    exact ⟨(fun c => q (componentEdge c)), Subgroup.mem_top _,
      assemble_eq_component_permutation θ hd hc⟩
  · rintro ⟨q, _, rfl⟩
    have hf : θ.permute q ∈ fiber D Y r θ (fun _ => True) :=
      ⟨θ.permute_observation q, trivial⟩
    rwa [fiber_eq_compatible_image θ (fun _ => True) hRigid] at hf

/-- Restriction by a fixed arbitrary A is exactly the surviving component permutations. -/
theorem anchored_fiber_eq_surviving_perms_of_localRigid (θ : Parameter D Y r)
    (A : Parameter D Y r → Prop) (hRigid : ∀ e, LocalRigid θ e) (hd : DistinctColumns θ) :
    fiber D Y r θ A = {η | ∃ q : W D r, A (θ.permute q) ∧ η = θ.permute q} := by
  ext η
  constructor
  · rintro ⟨ho, hA⟩
    have hf : η ∈ fiber D Y r θ (fun _ => True) := ⟨ho, trivial⟩
    rw [fiber_eq_component_orbit_of_localRigid θ hRigid hd] at hf
    obtain ⟨q, _, rfl⟩ := hf
    exact ⟨q, hA, rfl⟩
  · rintro ⟨q, hA, rfl⟩
    exact ⟨θ.permute_observation q, hA⟩

/-- General surviving-permutation criterion, conditional on the separately displayed local input. -/
theorem identifies_iff_surviving_perms_of_localRigid (θ : Parameter D Y r)
    (A : Parameter D Y r → Prop) (Γ : Subgroup (W D r))
    (hRigid : ∀ e, LocalRigid θ e) (hd : DistinctColumns θ) :
    IdentifiesModulo D Y r θ A Γ ↔ ∀ q : W D r, A (θ.permute q) → q ∈ Γ := by
  constructor
  · intro hid q hA
    have hf : θ.permute q ∈ fiber D Y r θ A := ⟨θ.permute_observation q, hA⟩
    rw [hid] at hf
    obtain ⟨⟨γ, hγ, heq⟩, _⟩ := hf
    exact (component_orbit_free θ hd heq) ▸ hγ
  · intro h
    apply Set.ext
    intro η
    constructor
    · intro hf
      rw [anchored_fiber_eq_surviving_perms_of_localRigid θ A hRigid hd] at hf
      obtain ⟨q, hA, rfl⟩ := hf
      exact ⟨⟨q, h q hA, rfl⟩, hA⟩
    · rintro ⟨⟨q, _, rfl⟩, hA⟩
      exact ⟨θ.permute_observation q, hA⟩


/-- GEN-D04: externally supplied truth metadata, with both blocks nonempty. -/
structure TruthPartition (r : ℕ) where
  truth : Fin r → Bool
  surjective : Function.Surjective truth

namespace TruthPartition
variable (τ : TruthPartition r)
def block (t : Bool) : Finset (Fin r) := Finset.univ.filter (fun z => τ.truth z = t)
def blockSize (t : Bool) : ℕ := (τ.block t).card
@[simp] theorem mem_block (t : Bool) (z : Fin r) : z ∈ τ.block t ↔ τ.truth z = t := by
  simp [block]
theorem block_nonempty (t : Bool) : (τ.block t).Nonempty := by
  obtain ⟨z, hz⟩ := τ.surjective t
  exact ⟨z, (τ.mem_block t z).mpr hz⟩
theorem blockSize_pos (t : Bool) : 0 < τ.blockSize t := Finset.card_pos.mpr (τ.block_nonempty t)
end TruthPartition

namespace Parameter

def truthWeight (θ : Parameter D Y r) (τ : TruthPartition r) (c : D.Component) (t : Bool) : ℝ :=
  ∑ z ∈ τ.block t, θ.weight c z

theorem truthWeight_pos (θ : Parameter D Y r) (τ : TruthPartition r) (c) (t) :
    0 < θ.truthWeight τ c t := by
  obtain ⟨z, hz⟩ := τ.block_nonempty t
  exact Finset.sum_pos' (fun z _ => (θ.weight_pos c z).le) ⟨z, hz, θ.weight_pos c z⟩

def truthKernel (θ : Parameter D Y r) (τ : TruthPartition r) (g : G) (y : Y g) (t : Bool) : ℝ :=
  (∑ z ∈ τ.block t, θ.weight (D.groupComponent g) z * θ.kernel g y z) /
    θ.truthWeight τ (D.groupComponent g) t

theorem truthKernel_nonneg (θ : Parameter D Y r) (τ : TruthPartition r) (g) (y) (t) :
    0 ≤ θ.truthKernel τ g y t := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun z _ => mul_nonneg (θ.weight_pos _ z).le (θ.kernel_nonneg g y z))
  · exact (θ.truthWeight_pos τ _ t).le

theorem truthKernel_total (θ : Parameter D Y r) (τ : TruthPartition r) (g) (t) :
    ∑ y, θ.truthKernel τ g y t = 1 := by
  simp only [truthKernel, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, θ.kernel_total, mul_one]
  exact div_self (ne_of_gt (θ.truthWeight_pos τ _ t))

def truthLaw (θ : Parameter D Y r) (τ : TruthPartition r) (g : G) (t : Bool) :
    Ext.FiniteLaw (Y g) :=
  ⟨fun y => θ.truthKernel τ g y t, fun y => θ.truthKernel_nonneg τ g y t, θ.truthKernel_total τ g t⟩

def sensitivity (θ : Parameter D Y r) (τ : TruthPartition r) (g : G) (R : Y g → Prop) : ℝ :=
  (θ.truthLaw τ g true).prob R

def specificity (θ : Parameter D Y r) (τ : TruthPartition r) (g : G) (R : Y g → Prop) : ℝ :=
  (θ.truthLaw τ g false).prob (fun y => ¬ R y)

end Parameter

/-- Componentwise truth-preserving permutations. -/
def truthPreservingGauge (τ : TruthPartition r) : Subgroup (W D r) where
  carrier q := ∀ c z, τ.truth (q c z) = τ.truth z
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro q p hq hp c z
    exact (hq c (p c z)).trans (hp c z)
  inv_mem' := by
    intro q hq c z
    simpa using (hq c ((q c)⁻¹ z)).symm

/-- A permutation of Bool is precisely either the identity or a whole-block exchange. -/
def truthGauge (τ : TruthPartition r) : Subgroup (W D r) where
  carrier q := ∀ c, ∃ b : Equiv.Perm Bool, ∀ z, τ.truth (q c z) = b (τ.truth z)
  one_mem' := fun _ => ⟨1, fun _ => rfl⟩
  mul_mem' := by
    intro q p hq hp c
    obtain ⟨a, ha⟩ := hq c
    obtain ⟨b, hb⟩ := hp c
    refine ⟨a * b, ?_⟩
    intro z
    exact (ha (p c z)).trans (congrArg a (hb z))
  inv_mem' := by
    intro q hq c
    obtain ⟨b, hb⟩ := hq c
    refine ⟨b⁻¹, ?_⟩
    intro z
    apply b.injective
    simpa using (hb ((q c)⁻¹ z)).symm

/-- The Bool-permutation presentation is exactly the paper's identity/flip convention. -/
theorem mem_truthGauge_iff (τ : TruthPartition r) (q : W D r) :
    q ∈ truthGauge (D := D) τ ↔
      ∀ c, ∃ a : Bool, ∀ z, τ.truth (q c z) = if a then !(τ.truth z) else τ.truth z := by
  constructor
  · intro h c
    obtain ⟨b, hb⟩ := h c
    by_cases hfalse : b false = false
    · refine ⟨false, ?_⟩
      intro z
      rw [hb z]
      have htrue : b true = true := by
        cases ht : b true
        · exact False.elim (Bool.noConfusion (b.injective (ht.trans hfalse.symm)))
        · rfl
      cases τ.truth z <;> simp [hfalse, htrue]
    · have hfalse' : b false = true := by cases h : b false <;> simp_all
      have htrue : b true = false := by
        cases ht : b true
        · rfl
        · exact False.elim (Bool.noConfusion (b.injective (ht.trans hfalse'.symm)))
      refine ⟨true, ?_⟩
      intro z
      rw [hb z]
      cases τ.truth z <;> simp [hfalse', htrue]
  · intro h c
    obtain ⟨a, ha⟩ := h c
    cases a
    · exact ⟨1, fun z => by simpa using ha z⟩
    · exact ⟨Equiv.swap false true, fun z => by
        rw [ha z]
        cases τ.truth z <;> simp⟩

/-- Fixed sign information is a strict population truth-kernel contrast. -/
structure EventAnchor (Y : G → Type*) where
  group : G
  event : Y group → Prop
  sign : ℝ
  sign_valid : sign = -1 ∨ sign = 1

def EventAnchor.Holds (a : EventAnchor Y) (τ : TruthPartition r) (θ : Parameter D Y r) : Prop :=
  0 < a.sign * ((θ.truthLaw τ a.group true).prob a.event -
    (θ.truthLaw τ a.group false).prob a.event)


namespace Parameter

theorem truthWeight_permute (θ : Parameter D Y r) (τ : TruthPartition r)
    {q : W D r} (hq : q ∈ truthPreservingGauge (D := D) τ) (c) (t) :
    (θ.permute q).truthWeight τ c t = θ.truthWeight τ c t := by
  unfold truthWeight TruthPartition.block
  simp only [Finset.sum_filter, permute_weight]
  have hh := Equiv.sum_comp (q c) (fun z => if τ.truth z = t then θ.weight c z else 0)
  simpa only [hq c] using hh

theorem truthKernel_permute (θ : Parameter D Y r) (τ : TruthPartition r)
    {q : W D r} (hq : q ∈ truthPreservingGauge (D := D) τ) (g) (y) (t) :
    (θ.permute q).truthKernel τ g y t = θ.truthKernel τ g y t := by
  unfold truthKernel
  rw [truthWeight_permute θ τ hq]
  congr 1
  unfold TruthPartition.block
  simp only [Finset.sum_filter, permute_weight, permute_kernel]
  have hh := Equiv.sum_comp (q (D.groupComponent g))
    (fun z => if τ.truth z = t then θ.weight (D.groupComponent g) z * θ.kernel g y z else 0)
  simpa only [hq (D.groupComponent g)] using hh

theorem sensitivity_permute (θ : Parameter D Y r) (τ : TruthPartition r)
    {q : W D r} (hq : q ∈ truthPreservingGauge (D := D) τ) (g) (R : Y g → Prop) :
    (θ.permute q).sensitivity τ g R = θ.sensitivity τ g R := by
  simp only [sensitivity, Ext.FiniteLaw.prob, truthLaw, truthKernel_permute θ τ hq]

theorem truthWeight_total (θ : Parameter D Y r) (τ : TruthPartition r) (c) :
    θ.truthWeight τ c false + θ.truthWeight τ c true = 1 := by
  unfold truthWeight TruthPartition.block
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  convert θ.weight_total c using 1
  apply Finset.sum_congr rfl
  intro z _
  cases τ.truth z <;> simp

end Parameter

/-- If the fixed truth block profile is unequal, no whole-block exchange can exist. -/
theorem truthGauge_eq_preserving_of_unequal (τ : TruthPartition r)
    (hu : τ.blockSize false ≠ τ.blockSize true) :
    truthGauge (D := D) τ = truthPreservingGauge (D := D) τ := by
  ext q
  constructor
  · intro h c z
    obtain ⟨a, ha⟩ := (mem_truthGauge_iff τ q).mp h c
    cases a
    · simpa using ha z
    · have he : {z // τ.truth z = false} ≃ {z // τ.truth z = true} :=
        Equiv.subtypeEquiv (q c) (fun z => by rw [ha z]; cases τ.truth z <;> simp)
      have hc := Fintype.card_congr he
      have hb : τ.blockSize false = τ.blockSize true := by
        simpa only [TruthPartition.blockSize, TruthPartition.block, Fintype.card_subtype] using hc
      exact False.elim (hu hb)
  · intro h c
    exact ⟨1, fun z => h c z⟩

lemma kruskalRank_le (θ : Parameter D Y r) (g : G) : kruskalRank θ g ≤ r := by
  apply Finset.sup_le
  intro k hk
  have h := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  change k ≤ r
  omega

lemma kruskalIndependent_zero (θ : Parameter D Y r) (g : G) : KruskalIndependent θ g 0 := by
  intro s hs
  have he : s = ∅ := Finset.card_eq_zero.mp hs
  subst s
  exact linearIndependent_empty_type

lemma kruskalRank_spec (θ : Parameter D Y r) (g : G) :
    KruskalIndependent θ g (kruskalRank θ g) := by
  have hn : ((Finset.range (r + 1)).filter (KruskalIndependent θ g)).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨?_, kruskalIndependent_zero θ g⟩⟩
    simp
  have hm := Finset.sup_mem_of_nonempty (f := id) hn
  obtain ⟨k, hk, heq⟩ := hm
  unfold kruskalRank
  rw [← heq]
  exact (Finset.mem_filter.mp hk).2

lemma le_kruskalRank (θ : Parameter D Y r) (g : G) {k : ℕ}
    (hk : k ≤ r) (hi : KruskalIndependent θ g k) : k ≤ kruskalRank θ g := by
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hi⟩)


/-- Full column rank suffices for the exact, maximal Kruskal rank. -/
theorem kruskalRank_eq_of_fullColumnRank (θ : Parameter D Y r) (g : G)
    (hi : LinearIndependent ℝ (fun z => fun y => θ.kernel g y z)) :
    kruskalRank θ g = r := by
  apply Nat.le_antisymm (kruskalRank_le θ g)
  apply le_kruskalRank θ g le_rfl
  intro s _
  exact hi.comp (fun z : s => z.val) Subtype.val_injective

/-- The design really has three distinct groups at every edge. -/
lemma card_groupAt (e : D.Edge) : Fintype.card (D.GroupAt e) = 3 := by
  simpa only [Fintype.card_coe] using D.edge_card e.val e.property

theorem fullColumnRank_KCond (θ : Parameter D Y r) (hr : 2 ≤ r)
    (hi : ∀ g, LinearIndependent ℝ (fun z => fun y => θ.kernel g y z)) (e : D.Edge) :
    KCond θ e := by
  unfold KCond
  simp_rw [kruskalRank_eq_of_fullColumnRank θ _ (hi _)]
  simp only [Finset.sum_const, Finset.card_univ, card_groupAt, nsmul_eq_mul]
  omega

/-- KCond forces each individual edge factor to have Kruskal rank at least two. -/
theorem KCond.kruskalRank_two_le (θ : Parameter D Y r) {e : D.Edge}
    (h : KCond θ e) (g : D.GroupAt e) : 2 ≤ kruskalRank θ g.val := by
  have hs : (∑ j ∈ Finset.univ.erase g, kruskalRank θ j.val) ≤ 2 * r := by
    calc
      _ ≤ ∑ _j ∈ (Finset.univ : Finset (D.GroupAt e)).erase g, r :=
        Finset.sum_le_sum (fun j _ => kruskalRank_le θ j.val)
      _ = 2 * r := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ g),
          Finset.card_univ, card_groupAt, nsmul_eq_mul]
        norm_num
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (D.GroupAt e))
    (fun j => kruskalRank θ j.val) (Finset.mem_univ g)
  unfold KCond at h
  omega

/-- Kruskal rank two is enough for pairwise distinct columns; no tensor theorem is used. -/
theorem distinct_of_kruskalRank_two_le (θ : Parameter D Y r) (g : G)
    (hk : 2 ≤ kruskalRank θ g) :
    Function.Injective (fun z : Fin r => fun y => θ.kernel g y z) := by
  intro i j hij
  by_contra hne
  have hp : ({i,j} : Finset (Fin r)).card = 2 := by simp [hne]
  obtain ⟨s, hps, _, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ ({i,j} : Finset (Fin r)))
    (show ({i,j} : Finset (Fin r)).card ≤ kruskalRank θ g by omega)
    (show kruskalRank θ g ≤ (Finset.univ : Finset (Fin r)).card by simpa using kruskalRank_le θ g)
  have hi : i ∈ s := hps (by simp)
  have hj : j ∈ s := hps (by simp)
  have hli := kruskalRank_spec θ g s hcard
  have heq : (⟨i,hi⟩ : s) = ⟨j,hj⟩ := hli.injective hij
  exact hne (congrArg Subtype.val heq)

theorem KCond.distinctColumns (θ : Parameter D Y r) (hk : ∀ e, KCond θ e) :
    DistinctColumns θ := by
  intro g
  exact distinct_of_kruskalRank_two_le θ g
    (KCond.kruskalRank_two_le θ (hk (D.incident g)) ⟨g, D.mem_incident g⟩)


/-- A bijection with the genuine full fiber, rather than merely a list of relabelings. -/
def fiberEquivPermsOfLocalRigid (θ : Parameter D Y r)
    (hRigid : ∀ e, LocalRigid θ e) (hd : DistinctColumns θ) :
    W D r ≃ {η // η ∈ fiber D Y r θ (fun _ => True)} :=
  Equiv.ofBijective (fun q => ⟨θ.permute q, θ.permute_observation q, trivial⟩) (by
    constructor
    · intro p q heq
      exact component_orbit_free θ hd (congrArg Subtype.val heq)
    · intro η
      have hη := (Set.ext_iff.mp (fiber_eq_component_orbit_of_localRigid θ hRigid hd) η.val).mp η.property
      obtain ⟨q, _, hq⟩ := hη
      exact ⟨q, Subtype.ext hq.symm⟩)

theorem fiber_cardinality_of_localRigid (θ : Parameter D Y r)
    (hRigid : ∀ e, LocalRigid θ e) (hd : DistinctColumns θ) :
    Nat.card {η // η ∈ fiber D Y r θ (fun _ => True)} =
      (Nat.factorial r) ^ Fintype.card D.Component := by
  rw [← Nat.card_congr (fiberEquivPermsOfLocalRigid θ hRigid hd)]
  simp [W, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_perm]


/-- All graph conclusions after a separately proved local-rigidity input. This is not
    a proof that Kruskal's condition supplies that input. -/
theorem graph_conclusions_of_localRigid_and_KCond (θ : Parameter D Y r)
    (hk : ∀ e, KCond θ e) (hl : ∀ e, LocalRigid θ e) :
    fiber D Y r θ (fun _ => True) = orbit D Y r θ ⊤ ∧
    Function.Injective θ.permute ∧
    Nat.card {η // η ∈ fiber D Y r θ (fun _ => True)} =
      (Nat.factorial r) ^ Fintype.card D.Component := by
  have hd := KCond.distinctColumns θ hk
  exact ⟨fiber_eq_component_orbit_of_localRigid θ hl hd,
    component_orbit_free θ hd, fiber_cardinality_of_localRigid θ hl hd⟩

/-- Raw factor-column Kruskal condition, also usable after absorbing mixture weights. -/
def ColumnKruskalIndependent {Z O : Type*} [Fintype Z] (L : O → Z → ℝ) (k : ℕ) : Prop :=
  ∀ s : Finset Z, s.card = k → LinearIndependent ℝ (fun z : s => fun y => L y z.val)

def columnKruskalRank {Z O : Type*} [Fintype Z] (L : O → Z → ℝ) : ℕ :=
  ((Finset.range (Fintype.card Z + 1)).filter (ColumnKruskalIndependent L)).sup id

lemma columnKruskalRank_parameter (θ : Parameter D Y r) (g : G) :
    columnKruskalRank (θ.kernel g) = kruskalRank θ g := by
  simp only [columnKruskalRank, kruskalRank, ColumnKruskalIndependent, KruskalIndependent,
    Fintype.card_fin]

/-- Nonzero rescaling preserves every column-subset independence test. -/
theorem columnKruskalIndependent_scale_iff {Z O : Type*} [Fintype Z]
    (L : O → Z → ℝ) (w : Z → ℝ) (hw : ∀ z, w z ≠ 0) (k : ℕ) :
    ColumnKruskalIndependent (fun y z => w z * L y z) k ↔ ColumnKruskalIndependent L k := by
  unfold ColumnKruskalIndependent
  apply forall_congr'
  intro s
  apply imp_congr_right
  intro _
  have heq : ((fun z : s => Units.mk0 (w z.val) (hw z.val)) •
      (fun z : s => fun y => L y z.val)) = (fun z : s => fun y => w z.val * L y z.val) := by
    funext z y
    rfl
  rw [← heq]
  exact LinearIndependent.units_smul_iff (fun z : s => fun y => L y z.val)
    (fun z => Units.mk0 (w z.val) (hw z.val))

/-- In particular, absorbing the positive weights into one factor does not change krank. -/
theorem columnKruskalRank_scale {Z O : Type*} [Fintype Z]
    (L : O → Z → ℝ) (w : Z → ℝ) (hw : ∀ z, w z ≠ 0) :
    columnKruskalRank (fun y z => w z * L y z) = columnKruskalRank L := by
  unfold columnKruskalRank
  simp_rw [columnKruskalIndependent_scale_iff L w hw]

/-- Normalization removes a single column's real scaling ambiguity exactly. -/
lemma stochastic_column_scaling_eq_one {O : Type*} [Fintype O]
    (u v : O → ℝ) (a : ℝ) (hu : ∑ y, u y = 1) (hv : ∑ y, v y = 1)
    (he : ∀ y, v y = a * u y) : a = 1 := by
  have hs := congrArg (fun f : O → ℝ => ∑ y, f y) (funext he)
  simpa only [hv, ← Finset.mul_sum, hu, mul_one] using hs.symm

/-- The weighted first factor determines both its positive weight and its normalized column. -/
lemma weighted_stochastic_column_unique {O : Type*} [Fintype O]
    (u v : O → ℝ) {w w' : ℝ} (hw : w ≠ 0)
    (hu : ∑ y, u y = 1) (hv : ∑ y, v y = 1)
    (he : ∀ y, w' * v y = w * u y) : w' = w ∧ v = u := by
  have hs := congrArg (fun f : O → ℝ => ∑ y, f y) (funext he)
  simp only [← Finset.mul_sum, hu, hv, mul_one] at hs
  refine ⟨hs, ?_⟩
  funext y
  exact mul_left_cancel₀ hw (by simpa only [hs] using he y)


/-- Exact normalization/scaling conversion from the supplied mature tensor-theorem
    interface. The existence of the common permutation and scalings is not assumed
    elsewhere and is not proved here from KCond. -/
theorem normalize_scaled_local_match (θ : Parameter D Y r) (e : D.Edge)
    (η : LocalSystem (Y := Y) (r := r) e) (q : Equiv.Perm (Fin r))
    (a : D.GroupAt e) (d : D.GroupAt e → Fin r → ℝ)
    (hprod : ∀ z, ∏ g, d g z = 1)
    (ha : ∀ y z, η.weight z * η.kernel a y z =
      d a z * θ.weight (D.component e) (q z) * θ.kernel a.val y (q z))
    (hk : ∀ g, g ≠ a → ∀ y z, η.kernel g y z = d g z * θ.kernel g.val y (q z)) :
    (∀ z, η.weight z = θ.weight (D.component e) (q z)) ∧
      ∀ g y z, η.kernel g y z = θ.kernel g.val y (q z) := by
  have hd : ∀ z g, d g z = 1 := by
    intro z
    have hother : ∀ g, g ≠ a → d g z = 1 := by
      intro g hne
      exact stochastic_column_scaling_eq_one (fun y => θ.kernel g.val y (q z))
        (fun y => η.kernel g y z) (d g z) (θ.kernel_total g.val (q z))
        (η.kernel_total g z) (fun y => hk g hne y z)
    have hap : d a z = 1 := by
      rw [← hprod z]
      symm
      apply Finset.prod_eq_single a
      · intro g _ hne
        exact hother g hne
      · simp
    intro g
    by_cases hga : g = a
    · simpa only [hga] using hap
    · exact hother g hga
  have hea : ∀ z, η.weight z = θ.weight (D.component e) (q z) ∧
      (fun y => η.kernel a y z) = (fun y => θ.kernel a.val y (q z)) := by
    intro z
    apply weighted_stochastic_column_unique
      (fun y => θ.kernel a.val y (q z)) (fun y => η.kernel a y z)
      (ne_of_gt (θ.weight_pos (D.component e) (q z)))
      (θ.kernel_total a.val (q z)) (η.kernel_total a z)
    intro y
    simpa only [hd z a, one_mul] using ha y z
  refine ⟨fun z => (hea z).1, ?_⟩
  intro g y z
  by_cases hga : g = a
  · subst g
    exact congrFun (hea z).2 y
  · simpa only [hd z g, one_mul] using hk g hga y z

end Gen
