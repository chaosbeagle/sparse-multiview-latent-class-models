import Gen.Kruskal

open scoped BigOperators Classical
noncomputable section
namespace Gen.KruskalWitness

/-- A genuine rank-deficient stochastic factor: columns e₀,e₁,(e₀+e₁)/2. -/
def A : Fin 3 → Fin 3 → ℝ :=
  ![![1,0,1/2], ![0,1,1/2], ![0,0,0]]

def I : Fin 3 → Fin 3 → ℝ := fun y z => if y = z then 1 else 0

lemma A_nonneg (y z : Fin 3) : 0 ≤ A y z := by fin_cases y <;> fin_cases z <;> norm_num [A]
lemma A_total (z : Fin 3) : ∑ y, A y z = 1 := by fin_cases z <;> norm_num [A, Fin.sum_univ_succ]
lemma I_nonneg (y z : Fin 3) : 0 ≤ I y z := by unfold I; split_ifs <;> norm_num
lemma I_total (z : Fin 3) : ∑ y, I y z = 1 := by simp [I]

lemma A_pairIndependent : ColumnKruskalIndependent A 2 := by
  intro s hs
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hs
  change LinearIndepOn ℝ (fun z => fun y => A y z) (↑({i,j} : Finset (Fin 3)))
  simp only [Finset.coe_insert, Finset.coe_singleton]
  apply (LinearIndepOn.pair_iff _ hij).mpr
  intro c d hcd
  have h0 := congrFun hcd 0
  have h1 := congrFun hcd 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  all_goals norm_num [A] at h0 h1
  all_goals constructor <;> linarith

lemma A_not_fullColumnRank : ¬ LinearIndependent ℝ (fun z => fun y => A y z) := by
  intro h
  have hz : ∑ z : Fin 3, (![-1,-1,2] z : ℝ) • (fun y => A y z) = 0 := by
    ext y
    fin_cases y <;> norm_num [A, Fin.sum_univ_succ]
  have hh := Fintype.linearIndependent_iff.mp h ![-1,-1,2] hz 0
  norm_num at hh

lemma A_not_threeIndependent : ¬ ColumnKruskalIndependent A 3 := by
  intro h
  have hu := h Finset.univ (by decide)
  apply A_not_fullColumnRank
  exact hu.comp (fun z => ⟨z, Finset.mem_univ z⟩)
    (fun i j hij => congrArg Subtype.val hij)

lemma A_kruskalRank : columnKruskalRank A = 2 := by
  unfold columnKruskalRank
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro k hk
    obtain ⟨hrange, hi⟩ := Finset.mem_filter.mp hk
    have hk3 : k < 4 := by simpa using Finset.mem_range.mp hrange
    have hne : k ≠ 3 := by intro heq; exact A_not_threeIndependent (heq ▸ hi)
    change k ≤ 2
    omega
  · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨by decide, A_pairIndependent⟩)

lemma I_fullColumnRank : LinearIndependent ℝ (fun z => fun y => I y z) := by
  rw [Fintype.linearIndependent_iff]
  intro v hv z
  have h := congrFun hv z
  simpa [I, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

lemma I_kruskalRank : columnKruskalRank I = 3 := by
  unfold columnKruskalRank
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro k hk
    have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    change k ≤ 3
    simpa using Nat.le_of_lt_succ hrange
  · apply Finset.le_sup (f := id)
    apply Finset.mem_filter.mpr
    refine ⟨by decide, ?_⟩
    intro s _
    exact I_fullColumnRank.comp (fun z : s => z.val) Subtype.val_injective

/-- Exact finite numerical witness to the strict extension beyond full-column-rank factors. -/
theorem rank_deficient_Kruskal_witness :
    columnKruskalRank A = 2 ∧ columnKruskalRank I = 3 ∧
    columnKruskalRank A + columnKruskalRank I + columnKruskalRank I = 2 * 3 + 2 ∧
    ¬ LinearIndependent ℝ (fun z => fun y => A y z) := by
  exact ⟨A_kruskalRank, I_kruskalRank, by rw [A_kruskalRank, I_kruskalRank], A_not_fullColumnRank⟩


/-- One actual unordered three-group edge, with coverage and cardinality verified. -/
def design : Ext.TripleDesign (Fin 3) where
  edges := {Finset.univ}
  edges_nonempty := by simp
  edge_card e he := by
    have heq : e = Finset.univ := by simpa using he
    subst e
    decide
  covered g := ⟨Finset.univ, by simp, Finset.mem_univ g⟩

def edge : design.Edge := ⟨Finset.univ, by simp [design]⟩
lemma edge_unique (e : design.Edge) : e = edge := by
  apply Subtype.ext
  exact Finset.mem_singleton.mp e.property

/-- Uniform positive weights and factors A,I,I in the full real model. -/
def parameter : Parameter design (fun _ => Fin 3) 3 where
  weight _ _ := 1/3
  weight_pos _ _ := by norm_num
  weight_total _ := by norm_num
  kernel g := if g = 0 then A else I
  kernel_nonneg g y z := by split_ifs <;> first | exact A_nonneg y z | exact I_nonneg y z
  kernel_total g z := by split_ifs <;> first | exact A_total z | exact I_total z

lemma parameter_rank_zero : kruskalRank parameter 0 = 2 := by
  rw [← columnKruskalRank_parameter]
  simpa [parameter] using A_kruskalRank
lemma parameter_rank_one : kruskalRank parameter 1 = 3 := by
  rw [← columnKruskalRank_parameter]
  simpa only [parameter, if_neg (by decide : (1 : Fin 3) ≠ 0)] using I_kruskalRank
lemma parameter_rank_two : kruskalRank parameter 2 = 3 := by
  rw [← columnKruskalRank_parameter]
  simpa only [parameter, if_neg (by decide : (2 : Fin 3) ≠ 0)] using I_kruskalRank

lemma parameter_rank_sum (e : design.Edge) :
    (∑ g : design.GroupAt e, kruskalRank parameter g.val) = 8 := by
  rw [edge_unique e]
  have h := Equiv.sum_comp
    (Equiv.subtypeUnivEquiv (fun g : Fin 3 => Finset.mem_univ g))
    (fun g => kruskalRank parameter g)
  change (∑ g : {g : Fin 3 // g ∈ (Finset.univ : Finset (Fin 3))},
    kruskalRank parameter g.val) = 8
  calc
    _ = ∑ g : Fin 3, kruskalRank parameter g := h
    _ = 8 := by
      rw [Fin.sum_univ_three, parameter_rank_zero, parameter_rank_one, parameter_rank_two]

lemma parameter_KCond (e : design.Edge) : KCond parameter e := by
  unfold KCond
  rw [parameter_rank_sum]

lemma parameter_not_fullColumnRank :
    ¬ LinearIndependent ℝ (fun z => fun y => parameter.kernel 0 y z) := by
  simpa [parameter] using A_not_fullColumnRank

theorem parameter_outside_fullrank_scope :
    ¬ (∀ g, LinearIndependent ℝ (fun z => fun y => parameter.kernel g y z)) := by
  intro h
  exact parameter_not_fullColumnRank (h 0)

/-- The newly proved generic theorem applies to this rank-deficient-factor witness. -/
theorem rank_deficient_full_fiber_identified :
    fiber design (fun _ => Fin 3) 3 parameter (fun _ => True) =
      orbit design (fun _ => Fin 3) 3 parameter ⊤ :=
  Gen.Kruskal.kruskal_fiber_eq_component_orbit parameter parameter_KCond

theorem rank_deficient_localRigid (e : design.Edge) : LocalRigid parameter e :=
  Gen.Kruskal.localRigid_of_KCond parameter e (parameter_KCond e)

end Gen.KruskalWitness
