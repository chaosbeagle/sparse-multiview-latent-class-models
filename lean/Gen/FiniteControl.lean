import Gen.ConditionedRates

set_option maxHeartbeats 1600000
open scoped BigOperators Classical
noncomputable section
namespace Gen.FiniteControl

/-- The two binary permutation kernels, bit false = identity, bit true = swap. -/
def binaryKernel (b : Bool) (y z : Fin 2) : ℝ :=
  if b then (if y = z then 0 else 1) else (if y = z then 1 else 0)

lemma binaryKernel_nonneg (b : Bool) (y z : Fin 2) : 0 ≤ binaryKernel b y z := by
  unfold binaryKernel
  split_ifs <;> norm_num

lemma binaryKernel_total (b : Bool) (z : Fin 2) : ∑ y, binaryKernel b y z = 1 := by
  cases b <;> fin_cases z <;> norm_num [binaryKernel,Fin.sum_univ_two]

lemma binaryKernel_gram (b : Bool) : Gen.Conditioned.GramMargin 1 (binaryKernel b) := by
  intro v
  cases b <;> simp [binaryKernel,Fin.sum_univ_two,add_comm]

/-- Real simplex columns with norm at least one are exactly simplex vertices. -/
theorem binary_column_vertex (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : a + b = 1) (hn : 1 ≤ a^2+b^2) :
    (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  have hab : a*b = 0 := by nlinarith [mul_nonneg ha hb]
  rcases mul_eq_zero.mp hab with ha0 | hb0
  · exact Or.inr ⟨ha0,by linarith⟩
  · exact Or.inl ⟨by linarith,hb0⟩

/-- Full-real binary Gram>=I reduction, with no algebraic/grid restriction.
The (1,-1) direction rules out equal deterministic columns. -/
theorem binary_gram_permutation (L : Fin 2 → Fin 2 → ℝ)
    (hnonneg : ∀ y z, 0 ≤ L y z) (htotal : ∀ z, ∑ y, L y z = 1)
    (hGram : Gen.Conditioned.GramMargin 1 L) :
    ∃ b : Bool, ∀ y z, L y z = binaryKernel b y z := by
  have hcol (z : Fin 2) : 1 ≤ (L 0 z)^2+(L 1 z)^2 := by
    have h := hGram (Pi.single z (1:ℝ))
    simpa [Pi.single_apply,Fin.sum_univ_two] using h
  have htotal' (z : Fin 2) : L 0 z + L 1 z = 1 := by simpa [Fin.sum_univ_two] using htotal z
  have h0 := binary_column_vertex (L 0 0) (L 1 0) (hnonneg 0 0) (hnonneg 1 0) (htotal' 0) (hcol 0)
  have h1 := binary_column_vertex (L 0 1) (L 1 1) (hnonneg 0 1) (hnonneg 1 1) (htotal' 1) (hcol 1)
  have hanti := hGram (fun z : Fin 2 => if z = 0 then 1 else -1)
  norm_num [Fin.sum_univ_two] at hanti
  rcases h0 with ⟨h00,h10⟩ | ⟨h00,h10⟩ <;> rcases h1 with ⟨h01,h11⟩ | ⟨h01,h11⟩
  · norm_num [h00,h10,h01,h11] at hanti
  · refine ⟨false,?_⟩
    intro y z
    fin_cases y <;> fin_cases z <;> simp [binaryKernel,h00,h10,h01,h11]
  · refine ⟨true,?_⟩
    intro y z
    fin_cases y <;> fin_cases z <;> simp [binaryKernel,h00,h10,h01,h11]
  · norm_num [h00,h10,h01,h11] at hanti

lemma binary_weights_half (w : Fin 2 → ℝ) (hw : ∀ z, (1/2:ℝ) ≤ w z)
    (ht : ∑ z, w z = 1) : ∀ z, w z = 1/2 := by
  have h0 := hw 0
  have h1 := hw 1
  simp only [Fin.sum_univ_two] at ht
  have he0 : w 0 = (1/2:ℝ) := by linarith
  have he1 : w 1 = (1/2:ℝ) := by linarith
  intro z
  fin_cases z
  · exact he0
  · exact he1

section AnyBinaryDesign
variable {G : Type*} [Fintype G] [DecidableEq G] (D : Ext.TripleDesign G)

def binaryParameter (bits : G → Bool) : Gen.Parameter D (fun _ => Fin 2) 2 where
  weight _ _ := 1/2
  weight_pos _ _ := by norm_num
  weight_total _ := by norm_num [Fin.sum_univ_two]
  kernel g := binaryKernel (bits g)
  kernel_nonneg g := binaryKernel_nonneg (bits g)
  kernel_total g := binaryKernel_total (bits g)

theorem binaryParameter_mem_K (bits : G → Bool) :
    Gen.Geometry.embed D (fun _ => Fin 2) 2 (binaryParameter D bits) ∈
      Gen.Conditioned.K D (fun _ => Fin 2) 2 (1/2) 1 := by
  rw [Gen.Conditioned.mem_K_embed_iff]
  exact ⟨fun _ _ => le_rfl,fun g => binaryKernel_gram (bits g)⟩

/-- Equality of the entire real K with the finite binary kernel family, for any
covered binary design. Every component's weights are exactly half. -/
theorem full_real_K_eq_binary_family :
    Gen.Conditioned.K D (fun _ => Fin 2) 2 (1/2) 1 =
      Set.range (fun bits : G → Bool => Gen.Geometry.embed D (fun _ => Fin 2) 2 (binaryParameter D bits)) := by
  ext x
  constructor
  · intro hx
    let θ := Gen.Conditioned.toParameter (by norm_num : (0:ℝ)<1/2) x hx
    have hk (g : G) : ∃ b : Bool, ∀ y z, θ.kernel g y z = binaryKernel b y z :=
      binary_gram_permutation (θ.kernel g) (θ.kernel_nonneg g) (θ.kernel_total g) (hx.2.2.2 g)
    choose bits hbits using hk
    have hθ : θ = binaryParameter D bits := by
      apply Gen.Parameter.ext
      · funext c z
        exact binary_weights_half (θ.weight c) (hx.2.1 c) (θ.weight_total c) z
      · funext g y z
        exact hbits g y z
    refine ⟨bits,?_⟩
    change Gen.Geometry.embed D (fun _ => Fin 2) 2 (binaryParameter D bits) = x
    rw [← hθ]
    exact Gen.Conditioned.embed_toParameter _ _ _
  · rintro ⟨bits,rfl⟩
    exact binaryParameter_mem_K D bits

theorem binary_family_injective : Function.Injective
    (fun bits : G → Bool => Gen.Geometry.embed D (fun _ => Fin 2) 2 (binaryParameter D bits)) := by
  intro s t h
  have hp := (Gen.Geometry.embed_injective D (fun _ => Fin 2) 2) h
  funext g
  have hg := congrArg (fun θ : Gen.Parameter D (fun _ => Fin 2) 2 => θ.kernel g 0 0) hp
  cases hs : s g <;> cases ht : t g
  · rfl
  · norm_num [binaryParameter,binaryKernel,hs,ht] at hg
  · norm_num [binaryParameter,binaryKernel,hs,ht] at hg
  · rfl
/-- A full equivalence, rather than a grid inclusion, with all binary kernel choices. -/
def binaryFamilyEquiv : (G → Bool) ≃
    {x : Gen.Geometry.Ambient D (fun _ => Fin 2) 2 // x ∈ Gen.Conditioned.K D (fun _ => Fin 2) 2 (1/2) 1} :=
  Equiv.ofBijective
    (fun bits => ⟨Gen.Geometry.embed D (fun _ => Fin 2) 2 (binaryParameter D bits), binaryParameter_mem_K D bits⟩)
    ⟨fun s t h => binary_family_injective D (congrArg Subtype.val h), by
      intro x
      have hx := (Set.ext_iff.mp (full_real_K_eq_binary_family D) x.val).mp x.property
      obtain ⟨bits,hbits⟩ := hx
      exact ⟨bits,Subtype.ext hbits⟩⟩

theorem full_real_K_card :
    Nat.card {x : Gen.Geometry.Ambient D (fun _ => Fin 2) 2 //
      x ∈ Gen.Conditioned.K D (fun _ => Fin 2) 2 (1/2) 1} = 2 ^ Fintype.card G := by
  rw [Nat.card_congr (binaryFamilyEquiv D).symm]
  simp [Nat.card_eq_fintype_card,Fintype.card_fun]

end AnyBinaryDesign
/-- In particular, the entire real three-binary-group K has exactly eight arrays. -/
theorem full_real_K_has_eight (D : Ext.TripleDesign (Fin 3)) :
    Nat.card {x : Gen.Geometry.Ambient D (fun _ => Fin 2) 2 //
      x ∈ Gen.Conditioned.K D (fun _ => Fin 2) 2 (1/2) 1} = 8 := by
  simpa using full_real_K_card D

/-- The accepted one-triple design. Group labels 0,1,2 correspond to 1,2,3. -/
def tripleDesign : Ext.TripleDesign (Fin 3) where
  edges := {Finset.univ}
  edges_nonempty := Finset.singleton_nonempty _
  edge_card := by intro e he; simp only [Finset.mem_singleton] at he; subst e; simp
  covered := by intro g; exact ⟨Finset.univ,by simp,by simp⟩

abbrev binaryAlphabet : Fin 3 → Type := fun _ => Fin 2
abbrev Ambient := Gen.Geometry.Ambient tripleDesign binaryAlphabet 2
abbrev feasible := Gen.Conditioned.K tripleDesign binaryAlphabet 2 (1/2) 1

def soleEdge : tripleDesign.Edge := ⟨Finset.univ,by simp [tripleDesign]⟩
instance soleEdge_unique : Unique tripleDesign.Edge where
  default := soleEdge
  uniq e := by
    apply Subtype.ext
    have h := e.property
    simpa only [tripleDesign,Finset.mem_singleton,soleEdge] using h

instance component_unique : Unique tripleDesign.Component where
  default := tripleDesign.component soleEdge
  uniq c := by
    induction c using Quotient.inductionOn with
    | h e =>
      change tripleDesign.component e = tripleDesign.component soleEdge
      congr 1
      exact Subsingleton.elim _ _

def point (bits : Fin 3 → Bool) : Ambient :=
  Gen.Geometry.embed tripleDesign binaryAlphabet 2 (binaryParameter tripleDesign bits)

theorem point_mem (bits : Fin 3 → Bool) : point bits ∈ feasible := binaryParameter_mem_K _ _

theorem full_feasible_eq_eight_points : feasible = Set.range point := full_real_K_eq_binary_family _

theorem parameter_coordinate_count : Fintype.card (Gen.Geometry.Coordinate tripleDesign binaryAlphabet 2) = 14 := by
  simp [Gen.Geometry.Coordinate,Fintype.card_unique]

def groupEquiv : Fin 3 ≃ tripleDesign.GroupAt soleEdge where
  toFun g := ⟨g,by simp [soleEdge]⟩
  invFun g := g.val
  left_inv _ := rfl
  right_inv g := by cases g; rfl

def outcomeEquiv : tripleDesign.Outcome binaryAlphabet soleEdge ≃ Fin 2 × Fin 2 × Fin 2 :=
  Gen.Jacobian.edgeOutcomeEquiv tripleDesign binaryAlphabet soleEdge groupEquiv

def rawObservation (bits : Fin 3 → Bool) (p : Fin 2 × Fin 2 × Fin 2) : ℝ :=
  ∑ z : Fin 2, (1/2:ℝ) * (binaryKernel (bits 0) p.1 z * binaryKernel (bits 1) p.2.1 z * binaryKernel (bits 2) p.2.2 z)

theorem observation_point_cell (bits : Fin 3 → Bool) (x : tripleDesign.Outcome binaryAlphabet soleEdge) :
    Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point bits) ⟨soleEdge,x⟩ =
      rawObservation bits (outcomeEquiv x) := by
  change (binaryParameter tripleDesign bits).observation soleEdge x = _
  rw [Gen.Parameter.observation_formula]
  apply Finset.sum_congr rfl
  intro z _
  change (1/2:ℝ) * (∏ g : tripleDesign.GroupAt soleEdge, binaryKernel (bits g.val) (x g) z) = _
  rw [← groupEquiv.prod_comp (fun g : tripleDesign.GroupAt soleEdge => binaryKernel (bits g.val) (x g) z)]
  rw [Fin.prod_univ_three]
  rfl

def observationSquare (s t : Fin 3 → Bool) : ℝ :=
  ∑ p : Fin 2 × Fin 2 × Fin 2, (rawObservation s p - rawObservation t p)^2

theorem observation_square_eq (s t : Fin 3 → Bool) :
    ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point s) -
      Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point t)‖^2 = observationSquare s t := by
  rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_sigma]
  simp only [Fintype.sum_unique]
  change (∑ x : tripleDesign.Outcome binaryAlphabet soleEdge,
    (Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point s) ⟨soleEdge,x⟩ -
      Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point t) ⟨soleEdge,x⟩)^2) = _
  simp_rw [observation_point_cell]
  exact outcomeEquiv.sum_comp (fun p => (rawObservation s p - rawObservation t p)^2)

/-- Exhaustion is performed only after the whole real feasible set has been reduced. -/
theorem observation_square_zero_or_one (s t : Fin 3 → Bool) :
    observationSquare s t = 0 ∨ observationSquare s t = 1 := by
  cases hs0 : s 0 <;> cases hs1 : s 1 <;> cases hs2 : s 2 <;>
    cases ht0 : t 0 <;> cases ht1 : t 1 <;> cases ht2 : t 2 <;>
    norm_num [observationSquare,rawObservation,binaryKernel,Fintype.sum_prod_type,Fin.sum_univ_two,
      hs0,hs1,hs2,ht0,ht1,ht2]

def binaryPermutation (b : Bool) : Equiv.Perm (Fin 2) :=
  if b then Equiv.swap 0 1 else 1

theorem binaryPermutation_cases (q : Equiv.Perm (Fin 2)) : ∃ b, q = binaryPermutation b := by
  have htwo (z : Fin 2) : z = 0 ∨ z = 1 := by fin_cases z <;> simp
  rcases htwo (q 0) with h0 | h0 <;> rcases htwo (q 1) with h1 | h1
  · have h := q.injective (h0.trans h1.symm)
    norm_num at h
  · refine ⟨false,?_⟩
    apply Equiv.ext
    intro z
    fin_cases z
    · simpa [binaryPermutation] using h0
    · simpa [binaryPermutation] using h1
  · refine ⟨true,?_⟩
    apply Equiv.ext
    intro z
    fin_cases z
    · simpa [binaryPermutation] using h0
    · simpa [binaryPermutation] using h1
  · have h := q.injective (h0.trans h1.symm)
    norm_num at h

def globalPermutation (b : Bool) : Gen.W tripleDesign 2 := fun _ => binaryPermutation b

theorem globalPermutation_cases (q : Gen.W tripleDesign 2) : ∃ b, q = globalPermutation b := by
  obtain ⟨b,hb⟩ := binaryPermutation_cases (q default)
  refine ⟨b,?_⟩
  funext c
  exact (congrArg q (Subsingleton.elim c default)).trans hb

theorem globalPermutation_inv (b : Bool) : (globalPermutation b)⁻¹ = globalPermutation b := by
  funext c
  cases b <;> simp [globalPermutation,binaryPermutation]

def zeroBits : Fin 3 → Bool := fun _ => false
def oneBits : Fin 3 → Bool := fun g => if g = 2 then true else false

lemma norm_ge_one_of_coordinate {I : Type*} [Fintype I]
    (x y : EuclideanSpace ℝ I) (i : I) (hi : (x-y) i = 1) : 1 ≤ ‖x-y‖ := by
  have h := PiLp.norm_apply_le (x-y) i
  rw [hi] at h
  simpa using h

/-- The exhibited pair is at least unit distance under both complete S2 alignments. -/
theorem attaining_pair_distance : 1 ≤ Gen.ConditionedRates.distance tripleDesign binaryAlphabet 2 (point zeroBits) (point oneBits) := by
  apply Finset.le_inf'
  intro q _
  obtain ⟨b,rfl⟩ := globalPermutation_cases q
  have hp : globalPermutation b • point oneBits = Gen.Geometry.embed tripleDesign binaryAlphabet 2
      ((binaryParameter tripleDesign oneBits).permute (globalPermutation b)) := by
    rw [Gen.Geometry.embed_permute,globalPermutation_inv]
    rfl
  rw [dist_eq_norm,hp]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  cases b
  · apply norm_ge_one_of_coordinate _ _ (.inr ⟨2,0,0⟩)
    norm_num [point,Gen.Geometry.embed,binaryParameter,Gen.Parameter.permute,binaryKernel,
      globalPermutation,binaryPermutation,zeroBits,oneBits,h02,h12]
  · apply norm_ge_one_of_coordinate _ _ (.inr ⟨0,0,0⟩)
    norm_num [point,Gen.Geometry.embed,binaryParameter,Gen.Parameter.permute,binaryKernel,
      globalPermutation,binaryPermutation,zeroBits,oneBits,h02,h12]

theorem attaining_pair_observation_square :
    ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point zeroBits) -
      Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point oneBits)‖^2 = 1 := by
  rw [observation_square_eq]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  norm_num [observationSquare,rawObservation,binaryKernel,Fintype.sum_prod_type,Fin.sum_univ_two,zeroBits,oneBits,h02,h12]

/-- Every real far pair has squared observation gap exactly one. -/
theorem full_far_square_one {R : ℝ} (hR : 0 < R)
    (x y : Ambient) (hx : x ∈ feasible) (hy : y ∈ feasible)
    (hfar : R ≤ Gen.ConditionedRates.distance tripleDesign binaryAlphabet 2 x y) :
    ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 x - Gen.Geometry.observation tripleDesign binaryAlphabet 2 y‖^2 = 1 := by
  obtain ⟨s,rfl⟩ := (Set.ext_iff.mp full_feasible_eq_eight_points x).mp hx
  obtain ⟨t,rfl⟩ := (Set.ext_iff.mp full_feasible_eq_eight_points y).mp hy
  rcases observation_square_zero_or_one s t with hz | ho
  · have hzero : ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point s) -
        Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point t)‖^2 = 0 :=
      (observation_square_eq s t).trans hz
    have heq := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
    have hd := (Gen.ConditionedRates.observation_eq_iff_distance_zero tripleDesign binaryAlphabet 2
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1) (by norm_num : 0<(2:ℕ))
      (point s) (point t) (point_mem s) (point_mem t)).mp heq
    rw [hd] at hfar
    linarith
  · exact (observation_square_eq s t).trans ho

/-- Complete full-real attained minimum certificate h=1 for every 0<R<=1. -/
theorem full_far_minimum_one {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    (∀ x ∈ feasible, ∀ y ∈ feasible,
      R ≤ Gen.ConditionedRates.distance tripleDesign binaryAlphabet 2 x y →
        ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 x - Gen.Geometry.observation tripleDesign binaryAlphabet 2 y‖^2 = 1) ∧
    (∃ x ∈ feasible, ∃ y ∈ feasible,
      R ≤ Gen.ConditionedRates.distance tripleDesign binaryAlphabet 2 x y ∧
        ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 x - Gen.Geometry.observation tripleDesign binaryAlphabet 2 y‖^2 = 1) := by
  refine ⟨fun x hx y hy => full_far_square_one hR x y hx hy, ?_⟩
  exact ⟨point zeroBits,point_mem _,point oneBits,point_mem _,hR1.trans attaining_pair_distance,
    attaining_pair_observation_square⟩

/-- Delta=1 is valid over the whole real far set, not just the listed eight records. -/
theorem full_far_delta_one {R : ℝ} (hR : 0 < R)
    (x y : Ambient) (hx : x ∈ feasible) (hy : y ∈ feasible)
    (hfar : R ≤ Gen.ConditionedRates.distance tripleDesign binaryAlphabet 2 x y) :
    (1:ℝ) ≤ ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 x - Gen.Geometry.observation tripleDesign binaryAlphabet 2 y‖ := by
  have h := full_far_square_one hR x y hx hy hfar
  nlinarith [norm_nonneg (Gen.Geometry.observation tripleDesign binaryAlphabet 2 x - Gen.Geometry.observation tripleDesign binaryAlphabet 2 y)]

/-- The literal total observed-cell count in this control. -/
theorem cells_exact : Gen.ConditionedRates.cells tripleDesign binaryAlphabet = 8 := by
  rw [Gen.ConditionedRates.cells_eq_card,Fintype.card_sigma]
  simp only [Fintype.sum_unique]
  change Fintype.card (tripleDesign.Outcome binaryAlphabet soleEdge) = 8
  rw [Fintype.card_congr outcomeEquiv]
  norm_num

def Bvalue : ℝ := Real.sqrt (157 + 108 * Real.sqrt 2)

theorem a_exact (g : Fin 3) : Gen.Constants.a (fun _ : Fin 3 => 2) (1/2) 1 g = 2 + 2 * Real.sqrt 2 := by
  norm_num [Gen.Constants.a]
  ring

theorem b_exact (e : tripleDesign.Edge) :
    Gen.Constants.b (fun e : tripleDesign.Edge => e.val) (fun _ : Fin 3 => 2) (1/2) 1 e = 7 + 6 * Real.sqrt 2 := by
  have he : e = soleEdge := Subsingleton.elim _ _
  subst e
  norm_num [Gen.Constants.b,Gen.Constants.a,soleEdge,Finset.sum_const]
  ring

theorem B_exact :
    Gen.Constants.B (fun e : tripleDesign.Edge => e.val) (fun _ : Fin 3 => 2) (1/2) 1 = Bvalue := by
  simp only [Gen.Constants.B,Finset.univ_unique,Finset.sup'_singleton]
  change Real.sqrt ((Gen.Constants.b (fun e : tripleDesign.Edge => e.val) (fun _ : Fin 3 => 2) (1/2) 1 soleEdge)^2 +
    ∑ g : Fin 3, (Gen.Constants.a (fun _ : Fin 3 => 2) (1/2) 1 g)^2) = Bvalue
  rw [b_exact]
  simp_rw [a_exact]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold Bvalue
  congr 1
  norm_num only [Nat.cast_ofNat]
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

theorem kappa_exact : Gen.ConditionedRates.kappa tripleDesign binaryAlphabet (1/2) 1 = 1 / Bvalue := by
  unfold Gen.ConditionedRates.kappa Gen.Constants.kappa
  simp only [Fintype.card_fin]
  rw [B_exact]

theorem curvature_exact : Gen.ConditionedRates.curvature tripleDesign binaryAlphabet = 24 * Real.sqrt 2 := by
  rw [Gen.ConditionedRates.curvature,cells_exact]
  norm_num only [Nat.cast_ofNat]
  rw [show (8:ℝ) = 4*2 by norm_num,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  norm_num
  ring

theorem diameter_exact :
    Gen.Constants.diameter (Fintype.card tripleDesign.Component) 2 (Fintype.card (Fin 3)) = Real.sqrt 14 := by
  norm_num [Gen.Constants.diameter,Fintype.card_unique]

/-- Exact integer ceiling from the accepted algebraic expression; no floating point. -/
theorem prescribed_count_exact :
    Nat.ceil ((40960 / 7 : ℝ) * (157 + 108 * Real.sqrt 2)) = 1812393 := by
  have hlo : ((7 * (1812392:ℝ) / 40960 - 157) / 108) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hup : Real.sqrt 2 ≤ ((7 * (1812393:ℝ) / 40960 - 157) / 108) :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  apply (Nat.ceil_eq_iff (by decide : (1812393:ℕ) ≠ 0)).2
  constructor <;> norm_num only [Nat.cast_sub (by decide : (1:ℕ) ≤ 1812393),Nat.cast_ofNat]
  · linarith
  · linarith

theorem Bvalue_pos : 0 < Bvalue := by unfold Bvalue; positivity

theorem Bvalue_square : Bvalue^2 = 157 + 108 * Real.sqrt 2 := by
  unfold Bvalue
  exact Real.sq_sqrt (by positivity)

theorem sample_scale_le_quarter : Real.sqrt 14 / (8 * Bvalue) ≤ (1/4:ℝ) := by
  have hB := Bvalue_pos
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 8*Bvalue)).2
  have h : Real.sqrt 14 ≤ 2 * Bvalue := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤14),mul_pow,Bvalue_square]
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  nlinarith

/-- Exact binding of the literal general sample-planning formula to N=1,812,393. -/
theorem prescribed_rule_exact :
    Gen.Rates.informativeCount 8
      (min (Gen.ConditionedRates.kappa tripleDesign binaryAlphabet (1/2) 1 *
        Gen.Constants.diameter (Fintype.card tripleDesign.Component) 2 (Fintype.card (Fin 3)) / 8) (1/4)) = 1812393 := by
  rw [kappa_exact,diameter_exact]
  have he : (1 / Bvalue) * Real.sqrt 14 / 8 = Real.sqrt 14 / (8 * Bvalue) := by ring
  rw [he,min_eq_left sample_scale_le_quarter]
  unfold Gen.Rates.informativeCount
  have hformula : 20 * (8:ℝ)^2 / (Real.sqrt 14 / (8*Bvalue))^2 =
      (40960/7:ℝ)*(157+108*Real.sqrt 2) := by
    rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤14),mul_pow,Bvalue_square,div_div_eq_mul_div]
    ring
  rw [hformula]
  exact prescribed_count_exact

def controlRadius : ℝ := Gen.ConditionedRates.radius tripleDesign binaryAlphabet
  (Gen.ConditionedRates.kappa tripleDesign binaryAlphabet (1/2) 1)

theorem controlRadius_pos : 0 < controlRadius :=
  Gen.ConditionedRates.radius_pos tripleDesign binaryAlphabet 2
    (by norm_num : (0:ℝ)<1/2) ⟨point zeroBits,point_mem _⟩
    (Gen.ConditionedRates.kappa_pos tripleDesign binaryAlphabet (by norm_num) (by norm_num))

theorem controlRadius_le_one : controlRadius ≤ 1 := Gen.ConditionedRates.radius_le_one _ _ _

/-- The attained exact h=1 certificate at the accepted literal radius. -/
theorem literal_minimum_one :
    (∀ x ∈ feasible, ∀ y ∈ feasible,
      controlRadius ≤ Gen.ConditionedRates.distance tripleDesign binaryAlphabet 2 x y →
        ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 x - Gen.Geometry.observation tripleDesign binaryAlphabet 2 y‖^2 = 1) ∧
    (∃ x ∈ feasible, ∃ y ∈ feasible,
      controlRadius ≤ Gen.ConditionedRates.distance tripleDesign binaryAlphabet 2 x y ∧
        ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 x - Gen.Geometry.observation tripleDesign binaryAlphabet 2 y‖^2 = 1) :=
  full_far_minimum_one controlRadius_pos controlRadius_le_one

theorem literal_delta_one : ∀ x ∈ feasible, ∀ y ∈ feasible,
    controlRadius ≤ Gen.ConditionedRates.distance tripleDesign binaryAlphabet 2 x y →
      (1:ℝ) ≤ ‖Gen.Geometry.observation tripleDesign binaryAlphabet 2 x - Gen.Geometry.observation tripleDesign binaryAlphabet 2 y‖ :=
  fun x hx y hy => full_far_delta_one controlRadius_pos x y hx hy

/-- The concrete one-edge IID experiment used by the finite-control certificate. -/
def controlExperiment : Ext.ObservationExperiment tripleDesign.Edge (tripleDesign.Outcome binaryAlphabet) where
  n _ := 1812393
  n_pos _ := by norm_num
  law e := (binaryParameter tripleDesign zeroBits).observationLaw e

/-- The prescribed integer now has an actual finite-law probability guarantee for
the exact lexicographic baseline, with no assumed small residual or supplied Delta. -/
theorem prescribed_statistical_bound
    (order : Gen.Geometry.Coordinate tripleDesign binaryAlphabet 2 ≃
      Fin (Fintype.card (Gen.Geometry.Coordinate tripleDesign binaryAlphabet 2)))
    {Ω : Type*} [Fintype Ω] (μ : Ext.FiniteLaw Ω)
    (obs : Ω → Ext.ObservationSpace controlExperiment) (hIID : controlExperiment.IID μ obs) :
    (19/20:ℝ) ≤ μ.prob (fun ω => Gen.ConditionedRates.distance tripleDesign binaryAlphabet 2
      (Gen.ConditionedRates.baseline tripleDesign binaryAlphabet 2 (by norm_num : (0:ℝ)<1/2)
        ⟨point zeroBits,point_mem _⟩ order (Gen.Rates.stack (controlExperiment.empirical (obs ω))))
      (point zeroBits) ≤ Real.sqrt 14 / 2) := by
  have hcount : Gen.Rates.informativeCount (controlExperiment.totalCells : ℝ)
      (min (Gen.ConditionedRates.kappa tripleDesign binaryAlphabet (1/2) 1 *
        Gen.Constants.diameter (Fintype.card tripleDesign.Component) 2 (Fintype.card (Fin 3)) / 8) (1/4)) ≤ 1812393 := by
    rw [Gen.ConditionedRates.totalCells_eq_cells,cells_exact]
    norm_num only [Nat.cast_ofNat]
    rw [prescribed_rule_exact]
  have h := Gen.ConditionedRates.literal_baseline_informative tripleDesign binaryAlphabet 2
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
    literal_delta_one ⟨point zeroBits,point_mem _⟩ order controlExperiment μ obs hIID
    (point zeroBits) (point_mem _) (show Gen.Rates.stack (fun e => (controlExperiment.law e).mass) =
      Gen.Geometry.observation tripleDesign binaryAlphabet 2 (point zeroBits) from rfl)
    1812393 (fun _ => rfl) hcount
  simpa only [diameter_exact] using h

end Gen.FiniteControl
