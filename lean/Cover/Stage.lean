import Cover.Tree

namespace Cover

def firstExclude (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a) (B : QBox n) : Option (Fin j) :=
  (List.finRange j).find? fun i => decide (((gs i).interval cs B).upper < 0)

/-- Fixed ascending constraint order, followed by GAP. -/
def chooseLeaf (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) : Option (CoverLeaf j) :=
  match firstExclude cs gs B with
  | some i => some (.exclude i)
  | none => if dyadic (2*k) ≤ (H.interval cs B).lower then some .gap else none

theorem chooseLeaf_checked (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) (label : CoverLeaf j)
    (hc : chooseLeaf cs gs H k B = some label) :
    checkLeaf cs gs H k B label = true := by
  unfold chooseLeaf at hc
  split at hc
  · rename_i i hi
    cases hc
    exact List.find?_some (p := fun i => decide (((gs i).interval cs B).upper < 0)) hi
  · split at hc
    · cases hc
      simp_all [checkLeaf]
    · contradiction

theorem chooseLeaf_none_iff (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) :
    chooseLeaf cs gs H k B = none ↔ ∀ label, checkLeaf cs gs H k B label = false := by
  constructor
  · intro hc label
    unfold chooseLeaf at hc
    split at hc
    · contradiction
    · rename_i hn
      have hn' := List.find?_eq_none.mp hn
      cases label with
      | exclude i =>
        have hi := hn' i (List.mem_finRange i)
        simpa [checkLeaf] using hi
      | gap =>
        simp only [ite_eq_right_iff, Option.some_ne_none, imp_false] at hc
        simpa [checkLeaf] using hc
  · intro hc
    cases h : chooseLeaf cs gs H k B with
    | none => rfl
    | some label =>
      have := chooseLeaf_checked cs gs H k B label h
      rw [hc label] at this
      contradiction

/-- A node visit tests leaves before testing the depth limit. The Nat component counts
    generator visits only, not interval primitive operations or mandatory replay visits. -/
def visit (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0 < n) : Nat → Nat → QBox n → Nat × Option (CoverTree n j)
  | 0, _, B =>
    match chooseLeaf cs gs H k B with
    | some label => (1, some (.leaf label))
    | none => (1, none)
  | remaining + 1, depth, B =>
    match chooseLeaf cs gs H k B with
    | some label => (1, some (.leaf label))
    | none =>
      let i : Fin n := ⟨depth % n, Nat.mod_lt _ hn⟩
      let left := visit cs gs H k hn remaining (depth+1) (splitBox B i false)
      match left.2 with
      | none => (1 + left.1, none)
      | some lt =>
        let right := visit cs gs H k hn remaining (depth+1) (splitBox B i true)
        match right.2 with
        | none => (1 + left.1 + right.1, none)
        | some rt => (1 + left.1 + right.1, some (.split i lt rt))

 theorem visit_replays (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0 < n) (remaining depth : Nat)
    (B : QBox n) (t : CoverTree n j)
    (hs : (visit cs gs H k hn remaining depth B).2 = some t) :
    checkTree cs gs H k B t = true := by
  induction remaining generalizing depth B t with
  | zero =>
    unfold visit at hs
    split at hs
    · cases hs
      exact chooseLeaf_checked _ _ _ _ _ _ (by assumption)
    · contradiction
  | succ remaining ih =>
    unfold visit at hs
    split at hs
    · cases hs
      exact chooseLeaf_checked _ _ _ _ _ _ (by assumption)
    · dsimp only at hs
      split at hs
      · contradiction
      · rename_i lt hl
        try dsimp only at hs
        split at hs
        · contradiction
        · rename_i rt hr
          cases hs
          simp only [checkTree, Bool.and_eq_true]
          exact ⟨ih _ _ _ hl, ih _ _ _ hr⟩

/-- Exact full binary depth bound; aborted and pruned runs can be smaller. -/
theorem visit_nodes_bound (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0 < n) (remaining depth : Nat) (B : QBox n) :
    (visit cs gs H k hn remaining depth B).1 ≤ 2^(remaining+1)-1 := by
  induction remaining generalizing depth B with
  | zero => simp [visit]; split <;> simp
  | succ remaining ih =>
    have powpos : 1 ≤ 2^(remaining+1) := Nat.one_le_pow _ _ (by decide)
    have hl := ih (depth+1) (splitBox B ⟨depth % n, Nat.mod_lt _ hn⟩ false)
    have hr := ih (depth+1) (splitBox B ⟨depth % n, Nat.mod_lt _ hn⟩ true)
    unfold visit
    split
    · simp only [Prod.fst]
      have : 1 ≤ 2^(remaining+1+1) := Nat.one_le_pow _ _ (by decide)
      have : 2 ≤ 2^(remaining+1+1) := by rw [pow_succ]; omega
      omega
    · dsimp only
      split
      · simp only [Prod.fst]
        rw [pow_succ]
        omega
      · try dsimp only
        split <;> simp only [Prod.fst] <;> rw [pow_succ] <;> omega

/-- A proof-only description of every box at the full unpruned depth. -/
def AllTerminalPass (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0 < n) : Nat → Nat → QBox n → Prop
  | 0, _, B => ∃ label, chooseLeaf cs gs H k B = some label
  | rem+1, depth, B =>
    AllTerminalPass cs gs H k hn rem (depth+1) (splitBox B ⟨depth%n, Nat.mod_lt _ hn⟩ false) ∧
    AllTerminalPass cs gs H k hn rem (depth+1) (splitBox B ⟨depth%n, Nat.mod_lt _ hn⟩ true)

theorem visit_succeeds_of_terminal_pass (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0 < n) (remaining depth : Nat) (B : QBox n)
    (hall : AllTerminalPass cs gs H k hn remaining depth B) :
    ∃ t, (visit cs gs H k hn remaining depth B).2 = some t := by
  induction remaining generalizing depth B with
  | zero =>
    obtain ⟨label, hl⟩ := hall
    exact ⟨.leaf label, by simp [visit, hl]⟩
  | succ remaining ih =>
    cases hc : chooseLeaf cs gs H k B with
    | some label => exact ⟨.leaf label, by simp [visit, hc]⟩
    | none =>
      obtain ⟨lt, hl⟩ := ih _ _ hall.1
      obtain ⟨rt, hr⟩ := ih _ _ hall.2
      exact ⟨.split ⟨depth%n, Nat.mod_lt _ hn⟩ lt rt, by simp [visit, hc, hl, hr]⟩

inductive StageResult (n j : Nat) where
  | inconclusive
  | implementationError
  | success : CoverTree n j → StageResult n j
  deriving DecidableEq, Repr

/-- s is both coefficient precision (in the supplied family) and k; depth is exactly n*s. -/
def coverStage (cs : Nat → Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (hn : 0 < n) (s : Nat) : StageResult n j :=
  match (visit (cs s) gs H s hn (n*s) 0 (unitBox n)).2 with
  | none => .inconclusive
  | some t => if checkTree (cs s) gs H s (unitBox n) t then .success t else .implementationError

theorem coverStage_success_checked (cs : Nat → Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (hn : 0 < n) (s : Nat) (t : CoverTree n j)
    (h : coverStage cs gs H hn s = .success t) :
    checkTree (cs s) gs H s (unitBox n) t = true := by
  unfold coverStage at h
  split at h
  · contradiction
  · split at h
    · cases h; assumption
    · contradiction

theorem coverStage_no_implementationError (cs : Nat → Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (hn : 0 < n) (s : Nat) :
    coverStage cs gs H hn s ≠ .implementationError := by
  unfold coverStage
  split
  · simp
  · rename_i t ht
    have hc := visit_replays (cs s) gs H s hn (n*s) 0 (unitBox n) t ht
    simp [hc]

theorem coverStage_succeeds_of_terminal_pass (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (hn : 0 < n) (s : Nat)
    (hall : AllTerminalPass (cs s) gs H s hn (n*s) 0 (unitBox n)) :
    ∃ t, coverStage cs gs H hn s = .success t := by
  obtain ⟨t, ht⟩ := visit_succeeds_of_terminal_pass (cs s) gs H s hn (n*s) 0 (unitBox n) hall
  have hc := visit_replays (cs s) gs H s hn (n*s) 0 (unitBox n) t ht
  exact ⟨t, by simp [coverStage, ht, hc]⟩

end Cover
