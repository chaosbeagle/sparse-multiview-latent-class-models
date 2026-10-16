import Gen.Diagonal

open scoped BigOperators Classical
noncomputable section
namespace Gen.NoSemantic

variable {h : ℕ}
local instance : DecidableEq (Fin (2*h)) := fun a b => Classical.propDecidable (a = b)

def zero (hh : 2 ≤ h) : Fin (2*h) := ⟨0, by omega⟩
def second (hh : 2 ≤ h) : Fin (2*h) := ⟨1, by omega⟩
def middle (hh : 2 ≤ h) : Fin (2*h) := ⟨h, by omega⟩

def firstBlock (hh : 2 ≤ h) : Finset (Fin (2*h)) := Finset.Iio (middle hh)
def swapSecond (hh : 2 ≤ h) : Equiv.Perm (Fin (2*h)) := Equiv.swap (second hh) (middle hh)
def secondBlock (hh : 2 ≤ h) : Finset (Fin (2*h)) := (firstBlock hh).image (swapSecond hh)
def anchorEvent (hh : 2 ≤ h) : Finset (Fin (2*h)) := {zero hh}
def readout (hh : 2 ≤ h) : Finset (Fin (2*h)) := {zero hh, second hh}

lemma firstBlock_card (hh : 2 ≤ h) : (firstBlock hh).card = h := by
  simp [firstBlock, middle]
lemma secondBlock_card (hh : 2 ≤ h) : (secondBlock hh).card = h := by
  rw [secondBlock, Finset.card_image_of_injective _ (swapSecond hh).injective, firstBlock_card]

lemma zero_ne_second (hh : 2 ≤ h) : zero hh ≠ second hh := by simp [zero,second,Fin.ext_iff]
lemma zero_ne_middle (hh : 2 ≤ h) : zero hh ≠ middle hh := by simp [zero,middle,Fin.ext_iff]; omega
lemma second_ne_middle (hh : 2 ≤ h) : second hh ≠ middle hh := by simp [second,middle,Fin.ext_iff]; omega

@[simp] lemma zero_mem_first (hh : 2 ≤ h) : zero hh ∈ firstBlock hh := by
  simp [firstBlock,zero,middle]; omega
@[simp] lemma second_mem_first (hh : 2 ≤ h) : second hh ∈ firstBlock hh := by
  simp [firstBlock,second,middle]; omega
@[simp] lemma middle_not_mem_first (hh : 2 ≤ h) : middle hh ∉ firstBlock hh := by
  simp [firstBlock]

@[simp] lemma zero_mem_second (hh : 2 ≤ h) : zero hh ∈ secondBlock hh := by
  apply Finset.mem_image.mpr
  refine ⟨zero hh, zero_mem_first hh, ?_⟩
  simp [swapSecond, Equiv.swap_apply_of_ne_of_ne (zero_ne_second hh) (zero_ne_middle hh)]

@[simp] lemma second_not_mem_second (hh : 2 ≤ h) : second hh ∉ secondBlock hh := by
  intro hm
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
  have he' : j = middle hh := by
    apply (swapSecond hh).injective
    simpa [swapSecond] using he
  subst j
  exact middle_not_mem_first hh hj

lemma subset_events (hh : 2 ≤ h) :
    firstBlock hh ∩ anchorEvent hh = {zero hh} ∧
    secondBlock hh ∩ anchorEvent hh = {zero hh} ∧
    (firstBlock hh)ᶜ ∩ anchorEvent hh = ∅ ∧
    (secondBlock hh)ᶜ ∩ anchorEvent hh = ∅ ∧
    firstBlock hh ∩ readout hh = readout hh ∧
    secondBlock hh ∩ readout hh = {zero hh} := by
  simp [anchorEvent,readout,Finset.inter_insert,Finset.inter_singleton_of_mem,
    zero_mem_first,second_mem_first,zero_mem_second,second_not_mem_second]

def uniform (hh : 2 ≤ h) (_ : Fin (2*h)) : ℝ := 1 / (2*h : ℕ)
lemma uniform_pos (hh : 2 ≤ h) : ∀ j, 0 < uniform hh j := by
  intro j
  apply one_div_pos.mpr
  exact_mod_cast (show 0 < 2*h by omega)
lemma uniform_total (hh : 2 ≤ h) : ∑ j, uniform hh j = 1 := by
  have hz : (2*h : ℕ) ≠ 0 := by omega
  simp only [uniform, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_one_div_cancel (by exact_mod_cast hz)

lemma uniform_mass (hh : 2 ≤ h) (S : Finset (Fin (2*h))) :
    Diagonal.subsetMass (uniform hh) S = S.card / (2*h : ℕ) := by
  simp [Diagonal.subsetMass,uniform,div_eq_mul_inv]
lemma uniform_eventMass (hh : 2 ≤ h) (S R : Finset (Fin (2*h))) :
    Diagonal.eventMass (uniform hh) S R = (S ∩ R).card / (2*h : ℕ) := by
  simp [Diagonal.eventMass,uniform,div_eq_mul_inv]

lemma subset_values (hh : 2 ≤ h) :
    Diagonal.anchorValue (uniform hh) (firstBlock hh) (anchorEvent hh) = 1/(h:ℝ) ∧
    Diagonal.anchorValue (uniform hh) (secondBlock hh) (anchorEvent hh) = 1/(h:ℝ) ∧
    Diagonal.sensitivityValue (uniform hh) (firstBlock hh) (readout hh) = 2/(h:ℝ) ∧
    Diagonal.sensitivityValue (uniform hh) (secondBlock hh) (readout hh) = 1/(h:ℝ) := by
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
  obtain ⟨ha,hb,hca,hcb,hra,hrb⟩ := subset_events hh
  have hcR : (readout hh).card = 2 := by simp [readout,zero_ne_second hh]
  constructor
  · simp [Diagonal.anchorValue, Diagonal.eventMass, anchorEvent, uniform_mass,
      firstBlock_card, uniform]
    field_simp
  constructor
  · simp [Diagonal.anchorValue, Diagonal.eventMass, anchorEvent, uniform_mass,
      secondBlock_card, uniform]
    field_simp
  simp only [Diagonal.sensitivityValue,uniform_eventMass,uniform_mass,
    firstBlock_card,secondBlock_card,hra,hrb,hcR,Finset.card_singleton]
  push_cast
  constructor <;> field_simp <;> ring

section Model
variable {G : Type*} [Fintype G] [DecidableEq G]
variable (D : Ext.TripleDesign G)

abbrev model (hh : 2 ≤ h) (b : Equiv.Perm (Fin (2*h))) : Gen.Parameter D (fun _ => Fin (2*h)) (2*h) :=
  Diagonal.atom D (uniform hh) (uniform_pos hh) (uniform_total hh) b

lemma probability_bridge (θ : Gen.Parameter D (fun _ => Fin (2*h)) (2*h))
    (τ : TruthPartition (2*h)) (g : G) (t : Bool) (B : Finset (Fin (2*h))) :
    (θ.truthLaw τ g t).prob (fun y => y ∈ B) =
      Diagonal.sensitivity D θ (τ.block t) g B := by
  rw [Diagonal.sensitivity_eq_sum_truthKernel]
  simp only [Ext.FiniteLaw.prob, Parameter.truthLaw, Parameter.truthKernel,
    Diagonal.truthKernel, Diagonal.prevalence, Diagonal.truthWeight, Parameter.truthWeight]
  simp only [← Finset.sum_filter]
  congr 1
  ext y
  simp

lemma block_false_compl (τ : TruthPartition (2*h)) : τ.block false = (τ.block true)ᶜ := by
  ext z
  cases hz : τ.truth z <;> simp [TruthPartition.mem_block,hz]

lemma atom_event (hh : 2 ≤ h) (b : Equiv.Perm (Fin (2*h)))
    (τ : TruthPartition (2*h)) (S : Finset (Fin (2*h)))
    (hm : ∀ z, z ∈ τ.block true ↔ b z ∈ S) (g : G) (B : Finset (Fin (2*h))) :
    (model D hh b).sensitivity τ g (fun y => y ∈ B) =
      Diagonal.sensitivityValue (uniform hh) S B := by
  unfold Parameter.sensitivity
  rw [probability_bridge]
  exact Diagonal.atom_sensitivity D (uniform hh) (uniform_pos hh) (uniform_total hh) b
    (τ.block true) S hm g B

lemma atom_anchor_gap (hh : 2 ≤ h) (b : Equiv.Perm (Fin (2*h)))
    (τ : TruthPartition (2*h)) (S : Finset (Fin (2*h)))
    (hm : ∀ z, z ∈ τ.block true ↔ b z ∈ S) (g : G) (B : Finset (Fin (2*h))) :
    (model D hh b).sensitivity τ g (fun y => y ∈ B) -
      ((model D hh b).truthLaw τ g false).prob (fun y => y ∈ B) =
      Diagonal.anchorValue (uniform hh) S B := by
  rw [atom_event D hh b τ S hm g B,probability_bridge,block_false_compl]
  have hm' : ∀ z, z ∈ (τ.block true)ᶜ ↔ b z ∈ Sᶜ := by
    simpa only [Finset.mem_compl] using fun z => not_congr (hm z)
  rw [Diagonal.atom_sensitivity D (uniform hh) (uniform_pos hh) (uniform_total hh)
    b (τ.block true)ᶜ Sᶜ hm']
  simp only [Diagonal.sensitivityValue,Diagonal.anchorValue,
    Diagonal.subsetMass_compl _ (uniform_total hh) S]

/-- Full joint law over all groups in the connected design, using its common weight vector. -/
def joint (θ : Gen.Parameter D (fun _ => Fin (2*h)) (2*h)) (root : G) (x : G → Fin (2*h)) : ℝ :=
  ∑ z, θ.weight (D.groupComponent root) z * ∏ g, θ.kernel g (x g) z

lemma model_joint (hh : 2 ≤ h) (b : Equiv.Perm (Fin (2*h))) (root : G) (x : G → Fin (2*h)) :
    joint D (model D hh b) root x = Diagonal.diagonal (uniform hh) x := by
  letI : Nonempty G := ⟨root⟩
  simp only [joint,model,Diagonal.atom]
  simp_rw [Diagonal.delta_product]
  unfold Diagonal.diagonal
  rw [← Equiv.sum_comp b (fun j => if x = (fun _ => j) then uniform hh j else 0)]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

lemma model_gram (hh : 2 ≤ h) (b : Equiv.Perm (Fin (2*h))) (g : G) (z z' : Fin (2*h)) :
    (∑ y, (model D hh b).kernel g y z * (model D hh b).kernel g y z') =
      if z = z' then 1 else 0 := by
  simp [model,Diagonal.atom,b.injective.eq_iff,eq_comm]

lemma models_not_semantic (hh : 2 ≤ h) (τ : TruthPartition (2*h))
    (b b' : Equiv.Perm (Fin (2*h)))
    (hb : ∀ z, z ∈ τ.block true ↔ b z ∈ firstBlock hh)
    (hb' : ∀ z, z ∈ τ.block true ↔ b' z ∈ secondBlock hh) (g : G) :
    ¬ ∃ q ∈ Gen.truthGauge (D := D) τ, model D hh b' = (model D hh b).permute q := by
  rintro ⟨q,hq,heq⟩
  let c := D.groupComponent g
  obtain ⟨a,ha⟩ := hq c
  have hmap : ∀ z, b (q c z) = b' z := by
    intro z
    have hk := congrArg (fun θ : Gen.Parameter D (fun _ => Fin (2*h)) (2*h) =>
      θ.kernel g (b' z) z) heq
    by_contra hn
    simp [model,Diagonal.atom,Parameter.permute_kernel,c,Ne.symm hn] at hk
  let z₀ := b'.symm (zero hh)
  let z₁ := b'.symm (second hh)
  have ht₀ : τ.truth z₀ = true := by
    apply (τ.mem_block true z₀).mp
    apply (hb' z₀).mpr
    simpa [z₀] using zero_mem_second hh
  have ht₁ : τ.truth z₁ = false := by
    have hn : τ.truth z₁ ≠ true := by
      intro he
      have hm := (hb' z₁).mp ((τ.mem_block true z₁).mpr he)
      exact second_not_mem_second hh (by simpa [z₁] using hm)
    cases hz : τ.truth z₁ <;> simp_all
  have hq₀ : τ.truth (q c z₀) = true := by
    apply (τ.mem_block true _).mp
    apply (hb _).mpr
    rw [hmap]
    simpa [z₀] using zero_mem_first hh
  have hq₁ : τ.truth (q c z₁) = true := by
    apply (τ.mem_block true _).mp
    apply (hb _).mpr
    rw [hmap]
    simpa [z₁] using second_mem_first hh
  have ha₀ := ha z₀
  have ha₁ := ha z₁
  rw [hq₀,ht₀] at ha₀
  rw [hq₁,ht₁] at ha₁
  have hx : true = false := a.injective (ha₀.symm.trans ha₁)
  cases hx

def fixedAnchor (hh : 2 ≤ h) (g : G) : Gen.EventAnchor (fun _ : G => Fin (2*h)) where
  group := g
  event y := y ∈ anchorEvent hh
  sign := 1
  sign_valid := Or.inr rfl

/-- A complete arbitrary-h assignment table: first h outputs form truth one, then only
output 1 (paper atom 2) and output h (paper atom h+1) exchange assignments. -/
theorem assignment_realization (hh : 2 ≤ h) (τ : TruthPartition (2*h))
    (hbal : ∀ t, τ.blockSize t = h) :
    ∃ b b' : Equiv.Perm (Fin (2*h)),
      (∀ z, z ∈ τ.block true ↔ b z ∈ firstBlock hh) ∧
      (∀ z, z ∈ τ.block true ↔ b' z ∈ secondBlock hh) ∧
      b' = b.trans (swapSecond hh) ∧
      b' (b.symm (second hh)) = middle hh ∧
      b' (b.symm (middle hh)) = second hh ∧
      (∀ z, b z ≠ second hh → b z ≠ middle hh → b' z = b z) := by
  have hc : (τ.block true).card = (firstBlock hh).card := by
    rw [firstBlock_card]
    exact hbal true
  obtain ⟨b,hb⟩ := Diagonal.exists_equiv_truth_subset rfl (τ.block true) (firstBlock hh) hc
  let b' := b.trans (swapSecond hh)
  have hb' : ∀ z, z ∈ τ.block true ↔ b' z ∈ secondBlock hh := by
    intro z
    constructor
    · intro hz
      exact Finset.mem_image.mpr ⟨b z,(hb z).mp hz,rfl⟩
    · intro hz
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hz
      have hj' : j = b z := (swapSecond hh).injective he
      exact (hb z).mpr (hj' ▸ hj)
  refine ⟨b,b',hb,hb',rfl,?_,?_,?_⟩
  · simp [b',swapSecond]
  · simp [b',swapSecond]
  · intro z hz₁ hz₂
    simp [b',swapSecond,Equiv.swap_apply_of_ne_of_ne hz₁ hz₂]

/-- Arbitrary-h, full-design semantic nonidentification, including full-joint equality.
The comparison uses the shared full real model and the exact fixed truth gauge. -/
theorem GEN_G_NOSEM (hh : 2 ≤ h) (hc : Diagonal.Connected D)
    (τ : TruthPartition (2*h)) (hbal : ∀ t, τ.blockSize t = h) (gₐ : G) :
    ∃ θ η : Gen.Parameter D (fun _ => Fin (2*h)) (2*h),
      (∃ b b' : Equiv.Perm (Fin (2*h)), θ = model D hh b ∧ η = model D hh b' ∧
        b' = b.trans (swapSecond hh) ∧
        (∀ z, z ∈ τ.block true ↔ b z ∈ firstBlock hh) ∧
        (∀ z, z ∈ τ.block true ↔ b' z ∈ secondBlock hh)) ∧
      (∀ c z, θ.weight c z = 1/(2*h:ℕ) ∧ η.weight c z = 1/(2*h:ℕ)) ∧
      (∀ g, LinearIndependent ℝ (fun z y => θ.kernel g y z) ∧
        LinearIndependent ℝ (fun z y => η.kernel g y z)) ∧
      (∀ g z z', (∑ y, θ.kernel g y z * θ.kernel g y z') = (if z = z' then 1 else 0) ∧
        (∑ y, η.kernel g y z * η.kernel g y z') = (if z = z' then 1 else 0)) ∧
      (∀ e x, θ.observation e x = η.observation e x) ∧
      (θ.sensitivity τ gₐ (fun y => y ∈ anchorEvent hh) -
        (θ.truthLaw τ gₐ false).prob (fun y => y ∈ anchorEvent hh) = 1/(h:ℝ)) ∧
      (η.sensitivity τ gₐ (fun y => y ∈ anchorEvent hh) -
        (η.truthLaw τ gₐ false).prob (fun y => y ∈ anchorEvent hh) = 1/(h:ℝ)) ∧
      (fixedAnchor hh gₐ).Holds τ θ ∧ (fixedAnchor hh gₐ).Holds τ η ∧
      θ.sensitivity τ gₐ (fun y => y ∈ readout hh) = 2/(h:ℝ) ∧
      η.sensitivity τ gₐ (fun y => y ∈ readout hh) = 1/(h:ℝ) ∧
      (¬ ∃ q ∈ Gen.truthGauge (D := D) τ, η = θ.permute q) ∧
      (∀ root x, joint D θ root x = joint D η root x) := by
  obtain ⟨b,b',hb,hb',hswap,_⟩ := assignment_realization hh τ hbal
  have hvals := subset_values hh
  have hga := (atom_anchor_gap D hh b τ (firstBlock hh) hb gₐ (anchorEvent hh)).trans hvals.1
  have hgb := (atom_anchor_gap D hh b' τ (secondBlock hh) hb' gₐ (anchorEvent hh)).trans hvals.2.1
  have hp : 0 < (1:ℝ)/h := one_div_pos.mpr (by exact_mod_cast (show 0 < h by omega))
  refine ⟨model D hh b, model D hh b', ⟨b,b',rfl,rfl,hswap,hb,hb'⟩,
    ?_, ?_, ?_, ?_, hga, hgb, ?_, ?_, ?_, ?_,
    models_not_semantic D hh τ b b' hb hb' gₐ, ?_⟩
  · intro c z; exact ⟨rfl,rfl⟩
  · intro g
    exact ⟨Diagonal.atom_full_rank D _ (uniform_pos hh) (uniform_total hh) b g,
      Diagonal.atom_full_rank D _ (uniform_pos hh) (uniform_total hh) b' g⟩
  · intro g z z'
    exact ⟨model_gram D hh b g z z',model_gram D hh b' g z z'⟩
  · intro e x
    exact (Diagonal.atom_observation D _ (uniform_pos hh) (uniform_total hh) b e x).trans
      (Diagonal.atom_observation D _ (uniform_pos hh) (uniform_total hh) b' e x).symm
  · change 0 < 1 * ((model D hh b).sensitivity τ gₐ (fun y => y ∈ anchorEvent hh) - _)
    simp only [fixedAnchor]
    rw [hga,one_mul]; exact hp
  · change 0 < 1 * ((model D hh b').sensitivity τ gₐ (fun y => y ∈ anchorEvent hh) - _)
    simp only [fixedAnchor]
    rw [hgb,one_mul]; exact hp
  · exact (atom_event D hh b τ (firstBlock hh) hb gₐ (readout hh)).trans hvals.2.2.1
  · exact (atom_event D hh b' τ (secondBlock hh) hb' gₐ (readout hh)).trans hvals.2.2.2
  · intro root x
    rw [model_joint D hh b root x,model_joint D hh b' root x]

/-- The added all-group observation is a normalized finite probability law. -/
lemma joint_total (θ : Gen.Parameter D (fun _ => Fin (2*h)) (2*h)) (root : G) :
    ∑ x, joint D θ root x = 1 := by
  exact (Ext.FiniteLaw.mixLaw (θ.weightLaw (D.groupComponent root))
    (fun z => Ext.FiniteLaw.productLaw (fun g => θ.kernelLaw g z))).total

lemma joint_nonneg (θ : Gen.Parameter D (fun _ => Fin (2*h)) (2*h)) (root : G) (x) :
    0 ≤ joint D θ root x := by
  exact (Ext.FiniteLaw.mixLaw (θ.weightLaw (D.groupComponent root))
    (fun z => Ext.FiniteLaw.productLaw (fun g => θ.kernelLaw g z))).nonneg x

lemma joint_root_independent (hc : Diagonal.Connected D)
    (θ : Gen.Parameter D (fun _ => Fin (2*h)) (2*h)) (root other : G) (x) :
    joint D θ root x = joint D θ other x := by
  have hh : D.groupComponent root = D.groupComponent other :=
    (Diagonal.connected_iff_components D).mp hc (D.incident root) (D.incident other)
  simp only [joint,hh]

/-- No connected covered triple design uniformly identifies truth modulo the full
truth gauge from its observations and this one fixed direction anchor. -/
theorem graph_anchor_not_uniform (hh : 2 ≤ h) (hc : Diagonal.Connected D)
    (τ : TruthPartition (2*h)) (hbal : ∀ t, τ.blockSize t = h) (gₐ : G) :
    ∃ θ : Gen.Parameter D (fun _ => Fin (2*h)) (2*h),
      (fixedAnchor hh gₐ).Holds τ θ ∧
      ¬ Gen.IdentifiesModulo D (fun _ => Fin (2*h)) (2*h) θ
        ((fixedAnchor hh gₐ).Holds τ) (Gen.truthGauge (D := D) τ) := by
  obtain ⟨θ,η,_,_,_,_,hobs,_,_,hθ,hη,_,_,hneq,_⟩ := GEN_G_NOSEM D hh hc τ hbal gₐ
  refine ⟨θ,hθ,?_⟩
  intro hid
  have hηfiber : η ∈ Gen.fiber D (fun _ => Fin (2*h)) (2*h) θ ((fixedAnchor hh gₐ).Holds τ) :=
    ⟨fun e x => (hobs e x).symm,hη⟩
  rw [Gen.IdentifiesModulo] at hid
  rw [hid] at hηfiber
  exact hneq hηfiber.1

end Model
end Gen.NoSemantic
