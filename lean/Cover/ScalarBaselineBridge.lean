import Cover.ScalarSyntax
import Cover.ConcreteCompiler
import Gen.ConditionedRates

open scoped BigOperators
namespace Cover.ScalarBaselineBridge
open Cover.FiniteDesign Gen.ModelEncoding.Ordered

/-- Exact input-edge order with each three-element edge in increasing group order. -/
def edgeLists (I : Syntax) : List (List (Fin I.groups)) := I.edges.map (fun e => e.sort (· ≤ ·))
def alphabet (I : Syntax) : Fin I.groups → ℕ := fun g => I.outputPred g + 1

local instance baselineEdgeNonempty (I : Syntax) (h : Valid I) : Nonempty (toBaseline I h).Edge :=
  (toBaseline I h).edge_nonempty

noncomputable section

theorem edgeLists_preserves_input_order (I : Syntax) (h : Valid I) :
    edgeLists I = (inputEdges I h).values.map (fun e => e.val.sort (· ≤ ·)) := by
  rw [edgeLists, ← inputEdges_preserves_order I h]
  simp only [List.map_map]
  rfl

private theorem sum_sorted {g : ℕ} (e : Finset (Fin g)) (f : Fin g → ℝ) :
    ((e.sort (· ≤ ·)).map f).sum = ∑ i ∈ e, f i := by
  rw [← List.sum_toFinset f (Finset.sort_nodup _ _), Finset.sort_toFinset]

private theorem prod_sorted {g : ℕ} (e : Finset (Fin g)) (f : Fin g → ℕ) :
    ((e.sort (· ≤ ·)).map f).prod = ∏ i ∈ e, f i := by
  rw [← List.prod_toFinset f (Finset.sort_nodup _ _), Finset.sort_toFinset]

theorem a_eq (I : Syntax) (w σ : ℝ) (i : Fin I.groups) :
    (Literal.a (alphabet I) i).eval w σ = Gen.Constants.a (alphabet I) w σ i := by
  simp only [Literal.eval_a,Gen.Constants.a]

theorem b_eq (I : Syntax) (h : Valid I) (w σ : ℝ) (e : (toBaseline I h).Edge) :
    (Literal.b (alphabet I) (e.val.sort (· ≤ ·))).eval w σ =
      Gen.Constants.b (fun e : (toBaseline I h).Edge => e.val) (alphabet I) w σ e := by
  rw [Literal.eval_b, sum_sorted]
  rfl

theorem edgeB_eq (I : Syntax) (h : Valid I) (w σ : ℝ) (e : (toBaseline I h).Edge) :
    (Literal.edgeB (alphabet I) (e.val.sort (· ≤ ·))).eval w σ =
      Real.sqrt ((Gen.Constants.b (fun e : (toBaseline I h).Edge => e.val) (alphabet I) w σ e)^2 +
        ∑ i ∈ e.val, (Gen.Constants.a (alphabet I) w σ i)^2) := by
  rw [Literal.eval_edgeB,b_eq,sum_sorted]
  simp only [a_eq]

theorem maxList_eval_le (ps : List ScalarExpr) (hne : ps ≠ []) (w σ b : ℝ)
    (hps : ∀ p ∈ ps, p.eval w σ ≤ b) : (ScalarExpr.maxList ps).eval w σ ≤ b := by
  induction ps with
  | nil => contradiction
  | cons p ps ih =>
      cases ps with
      | nil => exact hps p (by simp)
      | cons q qs =>
          exact max_le (hps p (by simp)) (ih (by simp) (fun p hp => hps p (by simp [hp])))

theorem B_eq (I : Syntax) (h : Valid I) (w σ : ℝ) :
    (Literal.B (alphabet I) (edgeLists I)).eval w σ =
      Gen.Constants.B (fun e : (toBaseline I h).Edge => e.val) (alphabet I) w σ := by
  have hel : (edgeLists I).map (Literal.edgeB (alphabet I)) =
      (inputEdges I h).values.map (fun e => Literal.edgeB (alphabet I) (e.val.sort (· ≤ ·))) := by
    rw [edgeLists_preserves_input_order I h,List.map_map]
    rfl
  change (ScalarExpr.maxList ((edgeLists I).map (Literal.edgeB (alphabet I)))).eval w σ = _
  rw [hel]
  apply le_antisymm
  · apply maxList_eval_le
    · intro hz
      obtain ⟨e⟩ := (toBaseline I h).edge_nonempty
      have hm : Literal.edgeB (alphabet I) (e.val.sort (· ≤ ·)) ∈
          (inputEdges I h).values.map (fun e => Literal.edgeB (alphabet I) (e.val.sort (· ≤ ·))) :=
        List.mem_map.mpr ⟨e,(inputEdges I h).complete e,rfl⟩
      rw [hz] at hm
      exact List.not_mem_nil hm
    · intro p hp
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
      rw [edgeB_eq]
      exact Gen.Constants.edge_bound_le_B _ _ _ _ e
  · apply Finset.sup'_le
    intro e he
    rw [← edgeB_eq I h w σ e]
    exact ScalarExpr.le_eval_maxList w σ (List.mem_map.mpr ⟨e,(inputEdges I h).complete e,rfl⟩)

theorem kappa_eq (I : Syntax) (h : Valid I) (w σ : ℝ) :
    (Literal.kappa (alphabet I) (edgeLists I)).eval w σ =
      Gen.ConditionedRates.kappa (toBaseline I h) (fun g => Fin (I.outputPred g+1)) w σ := by
  simp only [Literal.kappa,ScalarExpr.eval,B_eq I h w σ,Gen.ConditionedRates.kappa,Gen.Constants.kappa,
    Fintype.card_fin,one_div]
  rfl

theorem m_eq_cells (I : Syntax) (h : Valid I) :
    Literal.m (alphabet I) (edgeLists I) =
      Gen.ConditionedRates.cells (toBaseline I h) (fun g => Fin (I.outputPred g+1)) := by
  unfold Literal.m
  rw [edgeLists_preserves_input_order I h,List.map_map]
  rw [(inputEdges I h).sum_map]
  unfold Gen.ConditionedRates.cells
  apply Finset.sum_congr rfl
  intro e he
  dsimp only [Function.comp_def]
  rw [prod_sorted]
  simp only [Fintype.card_fin]
  exact Finset.prod_subtype e.val (fun i => Iff.rfl) (alphabet I)

theorem M_eq (I : Syntax) (h : Valid I) (w σ : ℝ) :
    (Literal.M (alphabet I) (edgeLists I)).eval w σ =
      Gen.ConditionedRates.curvature (toBaseline I h) (fun g => Fin (I.outputPred g+1)) := by
  simp only [Literal.M,ScalarExpr.eval,Rat.cast_ofNat,Rat.cast_natCast,m_eq_cells I h,
    Gen.ConditionedRates.curvature]

theorem R_eq (I : Syntax) (h : Valid I) (w σ : ℝ) :
    (Literal.R (alphabet I) (edgeLists I)).eval w σ =
      Gen.ConditionedRates.radius (toBaseline I h) (fun g => Fin (I.outputPred g+1))
        (Gen.ConditionedRates.kappa (toBaseline I h) (fun g => Fin (I.outputPred g+1)) w σ) := by
  simp only [Literal.R,ScalarExpr.eval,Rat.cast_one,kappa_eq I h w σ,M_eq I h w σ,
    Gen.ConditionedRates.radius,div_eq_mul_inv]

theorem D_eq (I : Syntax) (h : Valid I) (w σ : ℝ) :
    (Literal.D (ConcreteCompiler.modelOrdering I h).components.values.length (I.rankPred+1) I.groups).eval w σ =
      Gen.Constants.diameter (Fintype.card (toBaseline I h).Component) (I.rankPred+1) (Fintype.card (Fin I.groups)) := by
  rw [FiniteEnumeration.length_eq_card]
  simp [Literal.D,ScalarExpr.eval,Gen.Constants.diameter]

end
end Cover.ScalarBaselineBridge
