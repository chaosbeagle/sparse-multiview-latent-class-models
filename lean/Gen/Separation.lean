import Gen.Rates

open Set
noncomputable section
namespace Gen.Separation

/-- Compactness plus genuine quotient injectivity gives positive separation from the
    closed far set. This is qualitative and makes no effective-QE claim. -/
theorem compact_positive_separation {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (K : Set X) (hK : IsCompact K) (O : X → Y) (hO : Continuous O)
    (d : X → X → ℝ) (hd : Continuous (fun p : X × X => d p.1 p.2))
    (hinj : ∀ x ∈ K, ∀ y ∈ K, O x = O y → d x y = 0)
    {R : ℝ} (hR : 0 < R) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ K, ∀ y ∈ K, R ≤ d x y → Δ ≤ dist (O x) (O y) := by
  let Q : Set (X × X) := (K ×ˢ K) ∩ {p | R ≤ d p.1 p.2}
  have hQ : IsCompact Q := (hK.prod hK).inter_right (isClosed_le continuous_const hd)
  have hcont : ContinuousOn (fun p : X × X => dist (O p.1) (O p.2)) Q :=
    ((hO.comp continuous_fst).dist (hO.comp continuous_snd)).continuousOn
  by_cases hne : Q.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hQ.exists_isMinOn hne hcont
    have hpos : 0 < dist (O p.1) (O p.2) := by
      rw [dist_pos]
      intro heq
      have hz := hinj p.1 hp.1.1 p.2 hp.1.2 heq
      have hfar : R ≤ d p.1 p.2 := hp.2
      linarith
    refine ⟨dist (O p.1) (O p.2), hpos, ?_⟩
    intro x hx y hy hfar
    exact (isMinOn_iff.mp hmin) (x,y) ⟨⟨hx,hy⟩,hfar⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx y hy hfar
    exact False.elim (hne ⟨(x,y), ⟨⟨hx,hy⟩,hfar⟩⟩)

/-- Every positive squared minimum admits the literal dyadic lower witness used by
    RATE-CONSTANTS. Existence is not an encoded-algebraic decision procedure. -/
theorem dyadic_lower_exists {h : ℝ} (hh : 0 < h) :
    ∃ k : ℕ, 0 < (2:ℝ)⁻¹ ^ k ∧ ((2:ℝ)⁻¹ ^ k) ^ 2 ≤ h := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (x := h) (y := (1:ℝ)/4) hh (by norm_num)
  refine ⟨k, by positivity, le_of_lt ?_⟩
  have hpow : ((2:ℝ)⁻¹ ^ k) ^ 2 = ((1:ℝ)/4) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  simpa only [hpow] using hk

/-- Soundness of a fully checked nonempty minimum certificate. Universal exclusion is
    a proof input, not supplied by feasibility of the minimizing point. -/
theorem minimum_certificate_separation {X : Type*}
    (Q : X → Prop) (H : X → ℝ) (h Δ : ℝ)
    (hmin : ∀ x, Q x → h ≤ H x) (hΔ : 0 < Δ) (hsq : Δ ^ 2 ≤ h)
    (hnonneg : ∀ x, Q x → 0 ≤ H x) :
    ∀ x, Q x → Δ ≤ Real.sqrt (H x) := by
  intro x hx
  exact (Real.le_sqrt hΔ.le (hnonneg x hx)).2 (hsq.trans (hmin x hx))

/-- Continuity of the finite orbit minimum is proved from the actual isometric action. -/
theorem orbitDist_continuous {Γ X : Type*} [Fintype Γ] [Group Γ]
    [MetricSpace X] [MulAction Γ X] [IsIsometricSMul Γ X] :
    Continuous (fun p : X × X => Gen.Rates.orbitDist (Γ := Γ) p.1 p.2) := by
  unfold Gen.Rates.orbitDist
  have hc := Continuous.finset_inf' (s := Finset.univ)
    (f := fun (q : Γ) (p : X × X) => dist p.1 (q • p.2))
    Finset.univ_nonempty (fun q _ =>
      continuous_fst.dist ((isometry_smul X q).continuous.comp continuous_snd))
  convert hc using 1
  funext p
  exact (Finset.inf'_apply Finset.univ_nonempty
    (fun (q : Γ) (p : X × X) => dist p.1 (q • p.2)) p).symm

end Gen.Separation
