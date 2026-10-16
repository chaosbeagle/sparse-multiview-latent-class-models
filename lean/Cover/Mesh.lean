import Cover.Stage
import Mathlib.Data.Nat.Count

namespace Cover

def splitCount (n : Nat) (i : Fin n) (depth : Nat) : Nat :=
  Nat.count (fun t => t % n = i.val) depth

theorem splitCount_succ (n : Nat) (i : Fin n) (depth : Nat) :
    splitCount n i (depth+1) = splitCount n i depth + if depth%n = i.val then 1 else 0 :=
  Nat.count_succ _ _

theorem splitCount_cycle (n : Nat) (i : Fin n) : splitCount n i n = 1 := by
  unfold splitCount
  rw [Nat.count_eq_card_filter_range]
  have hf : (Finset.range n).filter (fun t => t%n = i.val) = {i.val} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨ht, hm⟩
      simpa [Nat.mod_eq_of_lt ht] using hm
    · rintro rfl
      exact ⟨i.isLt, Nat.mod_eq_of_lt i.isLt⟩
  rw [hf]
  simp

theorem splitCount_full_depth (n : Nat) (i : Fin n) (s : Nat) :
    splitCount n i (n*s) = s := by
  induction s with
  | zero => simp [splitCount]
  | succ s ih =>
    unfold splitCount at *
    rw [Nat.mul_succ, Nat.count_add, ih]
    simpa [Nat.add_mod, splitCount] using congrArg (s + ·) (splitCount_cycle n i)

theorem splitBox_width_same (B : QBox n) (i : Fin n) (right : Bool) :
    (splitBox B i right i).width = (B i).width / 2 := by
  cases right <;> simp [splitBox, QInterval.width, QInterval.midpoint] <;> ring

theorem splitBox_width_other (B : QBox n) (i j : Fin n) (right : Bool) (h : j ≠ i) :
    (splitBox B i right j).width = (B j).width := by simp [splitBox, h]

/-- Proof-only reachability in the actual unpruned cyclic subdivision, starting at X. -/
inductive CyclicBox (hn : 0 < n) : Nat → QBox n → Prop where
  | root : CyclicBox hn 0 (unitBox n)
  | child {depth : Nat} {B : QBox n} (h : CyclicBox hn depth B) (right : Bool) :
      CyclicBox hn (depth+1) (splitBox B ⟨depth%n, Nat.mod_lt _ hn⟩ right)

theorem cyclicBox_valid (hn : 0 < n) (h : CyclicBox hn depth B) : B.Valid := by
  induction h with
  | root => intro i; norm_num [unitBox, QInterval.valid]
  | child _ right ih => exact splitBox_valid _ ih _ right

theorem cyclicBox_width (hn : 0 < n) (h : CyclicBox hn depth B) (i : Fin n) :
    (B i).width = dyadic (splitCount n i depth) := by
  induction h with
  | root => simp [unitBox, QInterval.width, splitCount, dyadic]
  | @child depth B hb right ih =>
    rw [splitCount_succ]
    by_cases heq : depth%n = i.val
    · have hfin : (⟨depth%n, Nat.mod_lt _ hn⟩ : Fin n) = i := Fin.ext heq
      rw [hfin, splitBox_width_same, ih, if_pos heq]
      simp [dyadic, pow_succ, div_eq_mul_inv]
    · have hfin : i ≠ (⟨depth%n, Nat.mod_lt _ hn⟩ : Fin n) := by
        intro hh; exact heq (congrArg Fin.val hh).symm
      rw [splitBox_width_other _ _ _ _ hfin, ih, if_neg heq, Nat.add_zero]

theorem full_depth_mesh_width (hn : 0 < n) (s : Nat)
    (h : CyclicBox hn (n*s) B) (i : Fin n) : (B i).width = dyadic s := by
  rw [cyclicBox_width hn h i, splitCount_full_depth]

theorem allTerminalPass_of_cyclic (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0 < n) (L : Nat)
    (hall : ∀ B, CyclicBox hn L B → ∃ label, chooseLeaf cs gs H k B = some label)
    (remaining depth : Nat) (B : QBox n) (hdepth : depth + remaining = L)
    (hB : CyclicBox hn depth B) : AllTerminalPass cs gs H k hn remaining depth B := by
  induction remaining generalizing depth B with
  | zero =>
    have hd : depth = L := by omega
    subst depth
    exact hall B hB
  | succ remaining ih =>
    constructor
    · exact ih _ _ (by omega) (.child hB false)
    · exact ih _ _ (by omega) (.child hB true)

theorem coverStage_succeeds_of_full_depth_boxes (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (s : Nat)
    (hall : ∀ B, CyclicBox hn (n*s) B → ∃ label, chooseLeaf (cs s) gs H s B = some label) :
    ∃ t, coverStage cs gs H hn s = .success t := by
  apply coverStage_succeeds_of_terminal_pass
  exact allTerminalPass_of_cyclic (cs s) gs H s hn (n*s) hall (n*s) 0 (unitBox n)
    (by omega) .root

end Cover
