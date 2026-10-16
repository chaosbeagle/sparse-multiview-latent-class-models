import Gen.KruskalRankBounds
import Gen.KruskalPermutation
import Gen.KruskalAlignment
import Gen.Uniqueness

/-! General real same-r Kruskal uniqueness, assembled from proved rank bounds,
proved permutation lemma, and proved common-permutation alignment. -/
noncomputable section
namespace Gen.Kruskal
open scoped BigOperators
open Gen.KruskalRankBounds
variable {Z X Y T : Type*} [Fintype Z] [DecidableEq Z]
  [Fintype X] [Fintype Y] [Fintype T]

lemma dual_eq_dot (ℓ : Module.Dual ℝ (T → ℝ)) :
    ∃ a : T → ℝ, ∀ v, ℓ v = ∑ t, v t * a t := by
  classical
  refine ⟨fun t => ℓ (Pi.single t 1), ?_⟩
  intro v
  have hv : v = ∑ t, v t • (Pi.single t 1 : T → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    ℓ v = ℓ (∑ t, v t • (Pi.single t 1 : T → ℝ)) := congrArg ℓ hv
    _ = _ := by simp [map_sum]

/-- Exact dual-form support interface of the independently proved permutation lemma. -/
theorem restrictedSupportComparison
    (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : Matrix T Z ℝ)
    {kA kB kC : ℕ}
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hC : Gen.ColumnKruskalIndependent C kC)
    (hkA : kA ≤ Fintype.card Z) (hkB : kB ≤ Fintype.card Z) (hkC : kC ≤ Fintype.card Z)
    (hK : 2 * Fintype.card Z + 2 ≤ kA+kB+kC)
    (h : TensorEqual A A' B B' C C') :
    Gen.KruskalPermutation.RestrictedSupportComparison (fun z t => C t z) (fun z t => C' t z) := by
  intro ℓ hℓ
  obtain ⟨a,ha⟩ := dual_eq_dot ℓ
  have hs (M : Matrix T Z ℝ) : Gen.KruskalPermutation.support (fun z t => M t z) ℓ =
      (support (dotCoefficients M a)).card := by
    simp only [Gen.KruskalPermutation.support, support, dotCoefficients, ha]
  have hr : Module.finrank ℝ (Gen.KruskalPermutation.totalSpan (fun z t => C' t z)) = C'.rank :=
    C'.rank_eq_finrank_span_cols.symm
  rw [hs, hr] at hℓ
  rw [hs, hs]
  exact kruskal_sparse_support A A' B B' C C' hA hB hC hkA hkB hkC hK h a hℓ

/-- One factor's common column matching is a theorem, not an oracle premise. -/
theorem third_factor_match
    (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : Matrix T Z ℝ)
    {kA kB kC : ℕ}
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hC : Gen.ColumnKruskalIndependent C kC)
    (hkA : kA ≤ Fintype.card Z) (hkB : kB ≤ Fintype.card Z) (hkC : kC ≤ Fintype.card Z)
    (hK : 2 * Fintype.card Z + 2 ≤ kA+kB+kC)
    (h : TensorEqual A A' B B' C C') :
    ∃ q : Equiv.Perm Z, ∃ d : Z → ℝ, (∀ z, d z ≠ 0) ∧
      ∀ t z, C' t z = d z * C t (q z) := by
  have h2 : 2 ≤ kC := by omega
  have hpd := Gen.KruskalPermutation.projectivelyDistinct_of_pair_independence
    (fun z t => C t z) (by omega : 2 ≤ Fintype.card Z)
    (columnIndependent_mono C hC hkC h2)
  obtain ⟨q,d,hd,heq⟩ := Gen.KruskalPermutation.permutation_of_restricted_support_comparison hpd
    (restrictedSupportComparison A A' B B' C C' hA hB hC hkA hkB hkC hK h)
  exact ⟨q,d,hd,fun t z => congrFun (heq z) t⟩

lemma TensorEqual.cycle (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : T → Z → ℝ)
    (h : TensorEqual A A' B B' C C') : TensorEqual B B' C C' A A' := by
  intro y t x
  calc
    _ = ∑ z, A x z * B y z * C t z := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := h x y t
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      ring

/-- Full real three-factor Kruskal uniqueness with unrestricted same-r competitors. -/
theorem uniqueness
    (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : Matrix T Z ℝ)
    {kA kB kC : ℕ}
    (hA : Gen.ColumnKruskalIndependent A kA) (hB : Gen.ColumnKruskalIndependent B kB)
    (hC : Gen.ColumnKruskalIndependent C kC)
    (hkA : kA ≤ Fintype.card Z) (hkB : kB ≤ Fintype.card Z) (hkC : kC ≤ Fintype.card Z)
    (hK : 2 * Fintype.card Z + 2 ≤ kA+kB+kC)
    (h : TensorEqual A A' B B' C C') :
    ∃ q : Equiv.Perm Z, ∃ da db dc : Z → ℝ,
      (∀ z, da z ≠ 0 ∧ db z ≠ 0 ∧ dc z ≠ 0) ∧
      (∀ x z, A' x z = da z * A x (q z)) ∧
      (∀ y z, B' y z = db z * B y (q z)) ∧
      (∀ t z, C' t z = dc z * C t (q z)) ∧
      ∀ z, da z * db z * dc z = 1 := by
  have hcycle := TensorEqual.cycle A A' B B' C C' h
  have hcycle2 := TensorEqual.cycle B B' C C' A A' hcycle
  obtain ⟨qc,dc,hdc,hCm⟩ := third_factor_match A A' B B' C C' hA hB hC hkA hkB hkC hK h
  obtain ⟨qa,da,hda,hAm⟩ := third_factor_match B B' C C' A A' hB hC hA hkB hkC hkA (by omega) hcycle
  obtain ⟨qb,db,hdb,hBm⟩ := third_factor_match C C' A A' B B' hC hA hB hkC hkA hkB (by omega) hcycle2
  obtain ⟨hab,hbc,hprod⟩ := Gen.KruskalAlignment.common_permutation_alignment
    A A' B B' C C' hkA hkB hkC hA hB hC hK qa qb qc da db dc hAm hBm hCm h
  refine ⟨qa,da,db,dc,fun z => ⟨hda z,hdb z,hdc z⟩,hAm,?_,?_,hprod⟩
  · simpa only [hab] using hBm
  · simpa only [hab, hbc] using hCm

/-- Positive stochastic normalization removes every scaling in the general
Kruskal theorem, with no rank hypotheses on the competitor. -/
theorem stochastic_uniqueness
    (w w' : Z → ℝ) (A A' : X → Z → ℝ) (B B' : Y → Z → ℝ) (C C' : T → Z → ℝ)
    (hw : ∀ z, 0 < w z) (hw' : ∀ z, 0 < w' z)
    (hA : Gen.Uniqueness.Normalized A) (hA' : Gen.Uniqueness.Normalized A')
    (hB : Gen.Uniqueness.Normalized B) (hB' : Gen.Uniqueness.Normalized B')
    (hC : Gen.Uniqueness.Normalized C) (hC' : Gen.Uniqueness.Normalized C')
    (hK : 2 * Fintype.card Z + 2 ≤ Gen.columnKruskalRank A +
      Gen.columnKruskalRank B + Gen.columnKruskalRank C)
    (h : ∀ x y t, Gen.Uniqueness.tensor w A B C x y t = Gen.Uniqueness.tensor w' A' B' C' x y t) :
    ∃ q : Equiv.Perm Z, (∀ z, w' z = w (q z)) ∧
      (∀ x z, A' x z = A x (q z)) ∧ (∀ y z, B' y z = B y (q z)) ∧
      (∀ t z, C' t z = C t (q z)) := by
  let WA := fun x z => w z * A x z
  let WA' := fun x z => w' z * A' x z
  have hk : Gen.columnKruskalRank WA = Gen.columnKruskalRank A :=
    Gen.columnKruskalRank_scale A w (fun z => ne_of_gt (hw z))
  obtain ⟨q,da,db,dc,_,ham,hbm,hcm,hprod⟩ := uniqueness WA WA' B B' C C'
    (kA := Gen.columnKruskalRank WA) (kB := Gen.columnKruskalRank B) (kC := Gen.columnKruskalRank C)
    (Gen.KruskalRankBounds.columnKruskalRank_spec WA) (Gen.KruskalRankBounds.columnKruskalRank_spec B) (Gen.KruskalRankBounds.columnKruskalRank_spec C)
    (Gen.KruskalRankBounds.columnKruskalRank_le WA) (Gen.KruskalRankBounds.columnKruskalRank_le B) (Gen.KruskalRankBounds.columnKruskalRank_le C)
    (by rwa [hk]) h
  have hdb : ∀ z, db z = 1 := fun z => Gen.stochastic_column_scaling_eq_one
    (fun y => B y (q z)) (fun y => B' y z) (db z) (hB (q z)) (hB' z) (fun y => hbm y z)
  have hdc : ∀ z, dc z = 1 := fun z => Gen.stochastic_column_scaling_eq_one
    (fun t => C t (q z)) (fun t => C' t z) (dc z) (hC (q z)) (hC' z) (fun t => hcm t z)
  have hda : ∀ z, da z = 1 := by intro z; simpa only [hdb, hdc, mul_one] using hprod z
  have hwa : ∀ z, w' z = w (q z) ∧ (fun x => A' x z) = (fun x => A x (q z)) := by
    intro z
    apply Gen.weighted_stochastic_column_unique (fun x => A x (q z)) (fun x => A' x z)
      (ne_of_gt (hw (q z))) (hA (q z)) (hA' z)
    intro x
    simpa only [hda, one_mul] using ham x z
  refine ⟨q,fun z => (hwa z).1,fun x z => congrFun (hwa z).2 x,?_,?_⟩
  · intro y z; simpa only [hdb, one_mul] using hbm y z
  · intro t z; simpa only [hdc, one_mul] using hcm t z

section Graph
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {D : Ext.TripleDesign G} {Yg : G → Type*} [∀ g, Fintype (Yg g)] {r : ℕ}

/-- GEN-G-KRUSKAL local theorem: the frozen actual Kruskal-rank condition proves
LocalRigid against every real positive stochastic same-r local competitor. -/
theorem localRigid_of_KCond (θ : Gen.Parameter D Yg r) (e : D.Edge) (hK : Gen.KCond θ e) :
    Gen.LocalRigid θ e := by
  classical
  let s : Fin 3 ≃ D.GroupAt e := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, D.edge_card e.val e.property])
  intro η ho
  have hT : ∀ (x : Yg (s 0).val) (y : Yg (s 1).val) (t : Yg (s 2).val),
      Gen.Uniqueness.tensor (θ.weight (D.component e))
        (θ.kernel (s 0).val) (θ.kernel (s 1).val) (θ.kernel (s 2).val) x y t =
      Gen.Uniqueness.tensor η.weight (η.kernel (s 0)) (η.kernel (s 1)) (η.kernel (s 2)) x y t := by
    intro x y t
    let f : (i : Fin 3) → Yg (s i).val :=
      Fin.cons x (Fin.cons y (Fin.cons t (fun i => Fin.elim0 i)))
    let o : D.Outcome Yg e := Equiv.piCongrLeft (fun g : D.GroupAt e => Yg g.val) s f
    have hf : ∀ i, o (s i) = f i := by intro i; simp [o]
    have hp (K : (g : D.GroupAt e) → Yg g.val → Fin r → ℝ) (z : Fin r) :
        (∏ g, K g (o g) z) = K (s 0) x z * K (s 1) y z * K (s 2) t z := by
      rw [← s.prod_comp (fun g => K g (o g) z)]
      simp_rw [hf]
      rw [Fin.prod_univ_three]
      rfl
    have h := ho o
    simp only [Gen.LocalSystem.observation, Gen.Parameter.observation_formula] at h
    simp_rw [hp] at h
    simpa only [Gen.Uniqueness.tensor, mul_assoc] using h.symm
  have hkrank : 2 * Fintype.card (Fin r) + 2 ≤
      Gen.columnKruskalRank (θ.kernel (s 0).val) + Gen.columnKruskalRank (θ.kernel (s 1).val) +
        Gen.columnKruskalRank (θ.kernel (s 2).val) := by
    simp only [Fintype.card_fin, Gen.columnKruskalRank_parameter]
    unfold Gen.KCond at hK
    rw [← s.sum_comp (fun g : D.GroupAt e => Gen.kruskalRank θ g.val), Fin.sum_univ_three] at hK
    exact hK
  obtain ⟨q,hw,hA,hB,hC⟩ := stochastic_uniqueness
    (θ.weight (D.component e)) η.weight
    (θ.kernel (s 0).val) (η.kernel (s 0))
    (θ.kernel (s 1).val) (η.kernel (s 1))
    (θ.kernel (s 2).val) (η.kernel (s 2))
    (θ.weight_pos (D.component e)) η.weight_pos
    (θ.kernel_total (s 0).val) (η.kernel_total (s 0))
    (θ.kernel_total (s 1).val) (η.kernel_total (s 1))
    (θ.kernel_total (s 2).val) (η.kernel_total (s 2)) hkrank hT
  refine ⟨q,hw,?_⟩
  intro g
  obtain ⟨i,rfl⟩ := s.surjective g
  fin_cases i
  · exact hA
  · exact hB
  · exact hC

/-- GEN-G-KRUSKAL full covered-design fiber, without an unproved LocalRigid premise. -/
theorem kruskal_fiber_eq_component_orbit (θ : Gen.Parameter D Yg r)
    (hK : ∀ e, Gen.KCond θ e) :
    Gen.fiber D Yg r θ (fun _ => True) = Gen.orbit D Yg r θ ⊤ :=
  Gen.fiber_eq_component_orbit_of_localRigid θ (fun e => localRigid_of_KCond θ e (hK e))
    (Gen.KCond.distinctColumns θ hK)

/-- The unrestricted fiber is free under component permutations. -/
theorem kruskal_component_orbit_free (θ : Gen.Parameter D Yg r)
    (hK : ∀ e, Gen.KCond θ e) : Function.Injective θ.permute :=
  Gen.component_orbit_free θ (Gen.KCond.distinctColumns θ hK)

end Graph

#print axioms uniqueness
#print axioms localRigid_of_KCond
#print axioms kruskal_fiber_eq_component_orbit
end Gen.Kruskal
