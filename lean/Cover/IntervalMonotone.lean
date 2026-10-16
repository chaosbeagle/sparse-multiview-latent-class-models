import Cover.IntervalEstimates

namespace Cover.QInterval

def Subinterval (I J : QInterval) : Prop := J.lower ≤ I.lower ∧ I.upper ≤ J.upper

theorem subinterval_contains {I J : QInterval} (h : I.Subinterval J) {x : ℝ}
    (hx : I.contains x) : J.contains x := by
  have hl : (J.lower : ℝ) ≤ I.lower := by exact_mod_cast h.1
  have hu : (I.upper : ℝ) ≤ J.upper := by exact_mod_cast h.2
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

theorem add_subinterval {I J I' J' : QInterval}
    (hI : I.Subinterval I') (hJ : J.Subinterval J') :
    (add I J).Subinterval (add I' J') :=
  ⟨add_le_add hI.1 hJ.1, add_le_add hI.2 hJ.2⟩

theorem neg_subinterval {I I' : QInterval} (hI : I.Subinterval I') :
    (neg I).Subinterval (neg I') := ⟨neg_le_neg hI.2, neg_le_neg hI.1⟩

theorem mul_subinterval {I J I' J' : QInterval} (hvI : I.valid) (hvJ : J.valid)
    (hI : I.Subinterval I') (hJ : J.Subinterval J') :
    (mul I J).Subinterval (mul I' J') := by
  obtain ⟨a,b,ha,hb,hl⟩ := mul_lower_choice I J
  obtain ⟨c,d,hc,hd,hu⟩ := mul_upper_choice I J
  have hae : I.contains (a : ℝ) := by
    exact ⟨by exact_mod_cast (endpoint_between hvI ha).1, by exact_mod_cast (endpoint_between hvI ha).2⟩
  have hbe : J.contains (b : ℝ) := by
    rcases endpoint_between hvJ hb with ⟨hbl,hbu⟩
    constructor <;> exact_mod_cast (by assumption : _)
  have hce : I.contains (c : ℝ) := by
    rcases endpoint_between hvI hc with ⟨hcl,hcu⟩
    constructor <;> exact_mod_cast (by assumption : _)
  have hde : J.contains (d : ℝ) := by
    rcases endpoint_between hvJ hd with ⟨hdl,hdu⟩
    constructor <;> exact_mod_cast (by assumption : _)
  have hlo := mul_contains (subinterval_contains hI hae) (subinterval_contains hJ hbe)
  have hup := mul_contains (subinterval_contains hI hce) (subinterval_contains hJ hde)
  constructor
  · rw [hl]; exact_mod_cast hlo.1
  · rw [hu]; exact_mod_cast hup.2

end Cover.QInterval

namespace Cover.PolyExpr

theorem interval_subinterval (p : PolyExpr n a)
    {ics ics' : Fin a → QInterval} {box box' : Fin n → QInterval}
    (hcv : ∀ i, (ics i).valid) (hxv : ∀ i, (box i).valid)
    (hc : ∀ i, (ics i).Subinterval (ics' i)) (hx : ∀ i, (box i).Subinterval (box' i)) :
    (interval ics box p).Subinterval (interval ics' box' p) := by
  induction p with
  | rat _ => exact ⟨le_refl _, le_refl _⟩
  | scalar i => exact hc i
  | var i => exact hx i
  | add p q hp hq => exact QInterval.add_subinterval hp hq
  | neg p hp => exact QInterval.neg_subinterval hp
  | mul p q hp hq =>
      exact QInterval.mul_subinterval (p.interval_valid hcv hxv)
        (q.interval_valid hcv hxv) hp hq

end Cover.PolyExpr
