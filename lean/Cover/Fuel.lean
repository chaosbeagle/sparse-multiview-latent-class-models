import Cover.Stage

namespace Cover

/-- A finite, lazily stepped computation. Each `step` is one explicitly modelled
    rational arithmetic, finite-data, or control operation; physical bit/CPU costs
    are deliberately not identified with this discrete counter. -/
inductive FinTask (α : Type) where
  | done : α → FinTask α
  | step : (Unit → FinTask α) → FinTask α

namespace FinTask

def result : FinTask α → α
  | .done a => a
  | .step next => result (next ())

def steps : FinTask α → Nat
  | .done _ => 0
  | .step next => steps (next ()) + 1

def bind (p : FinTask α) (f : α → FinTask β) : FinTask β :=
  match p with
  | .done a => f a
  | .step next => .step (fun _ => bind (next ()) f)

instance : Monad FinTask where
  pure := .done
  bind := bind

def run : Nat → FinTask α → Option α
  | _, .done a => some a
  | 0, .step _ => none
  | fuel+1, .step next => run fuel (next ())

@[simp] theorem result_done (a : α) : result (.done a) = a := rfl
@[simp] theorem result_step (next : Unit → FinTask α) : result (.step next) = result (next ()) := rfl
@[simp] theorem result_bind (p : FinTask α) (f : α → FinTask β) :
    result (bind p f) = result (f (result p)) := by
  induction p with
  | done a => rfl
  | step next ih => exact ih ()

@[simp] theorem result_pure (a : α) : result (pure a : FinTask α) = a := rfl

@[simp] theorem result_bindM (p : FinTask α) (f : α → FinTask β) :
    result (p >>= f) = result (f (result p)) := result_bind p f

theorem run_sound (fuel : Nat) (p : FinTask α) (a : α) (h : run fuel p = some a) : result p = a := by
  induction fuel generalizing p with
  | zero => cases p with
    | done b => exact Option.some.inj h
    | step _ => contradiction
  | succ fuel ih => cases p with
    | done b => exact Option.some.inj h
    | step next => exact ih (next ()) h

theorem run_sufficient (p : FinTask α) (fuel : Nat) (h : p.steps ≤ fuel) :
    run fuel p = some p.result := by
  induction p generalizing fuel with
  | done a => cases fuel <;> rfl
  | step next ih =>
    cases fuel with
    | zero => simp [steps] at h
    | succ fuel =>
      apply ih () fuel
      simpa [steps] using h

theorem run_prefix (p : FinTask α) (f g : Nat) (hfg : f ≤ g) (a : α)
    (h : run f p = some a) : run g p = some a := by
  induction f generalizing p g with
  | zero => cases p with
    | done b => simpa only [run] using h
    | step _ => contradiction
  | succ f ih =>
    cases p with
    | done b => simpa only [run] using h
    | step next =>
      cases g with
      | zero => omega
      | succ g => exact ih (next ()) g (by omega) h
end FinTask

/-- The interval grammar executes on finite rational data only. -/
def intervalTask (cs : Fin a → QInterval) (B : QBox n) : PolyExpr n a → FinTask QInterval
  | .rat q => .step fun _ => .done (.singleton q)
  | .scalar i => .step fun _ => .done (cs i)
  | .var i => .step fun _ => .done (B i)
  | .add p q => .step fun _ => do
    let I ← intervalTask cs B p
    let J ← intervalTask cs B q
    .step fun _ => .done (.add I J)
  | .neg p => .step fun _ => do
    let I ← intervalTask cs B p
    .step fun _ => .done (.neg I)
  | .mul p q => .step fun _ => do
    let I ← intervalTask cs B p
    let J ← intervalTask cs B q
    .step fun _ => .done (.mul I J)

theorem intervalTask_result (cs : Fin a → QInterval) (B : QBox n) (p : PolyExpr n a) :
    (intervalTask cs B p).result = p.interval cs B := by
  induction p <;> simp_all [intervalTask, PolyExpr.interval]

def firstExcludeTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (B : QBox n) : List (Fin j) → FinTask (Option (Fin j))
  | [] => .done none
  | i::is => do
    let I ← intervalTask cs B (gs i)
    .step fun _ => if I.upper < 0 then .done (some i) else firstExcludeTask cs gs B is

theorem firstExcludeTask_result (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (B : QBox n) (is : List (Fin j)) :
    (firstExcludeTask cs gs B is).result =
      is.find? (fun i => decide (((gs i).interval cs B).upper < 0)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    by_cases h : ((gs i).interval cs B).upper < 0
    · simp [firstExcludeTask, intervalTask_result, h, List.find?_cons]
    · simp [firstExcludeTask, intervalTask_result, h, List.find?_cons, ih]

def chooseLeafTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) : FinTask (Option (CoverLeaf j)) := do
  let idx ← firstExcludeTask cs gs B (List.finRange j)
  match idx with
  | some i => .done (some (.exclude i))
  | none => do
    let I ← intervalTask cs B H
    .step fun _ => if dyadic (2*k) ≤ I.lower then .done (some .gap) else .done none

theorem chooseLeafTask_result (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) :
    (chooseLeafTask cs gs H k B).result = chooseLeaf cs gs H k B := by
  simp only [chooseLeafTask, FinTask.result_bindM, firstExcludeTask_result, chooseLeaf, firstExclude]
  split
  · simp_all
  · simp_all only
    simp only [FinTask.result_bindM, intervalTask_result, FinTask.result_step]
    split <;> rfl

def checkLeafTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) : CoverLeaf j → FinTask Bool
  | .exclude i => do
    let I ← intervalTask cs B (gs i)
    .step fun _ => .done (decide (I.upper < 0))
  | .gap => do
    let I ← intervalTask cs B H
    .step fun _ => .done (decide (dyadic (2*k) ≤ I.lower))

theorem checkLeafTask_result (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) (label : CoverLeaf j) :
    (checkLeafTask cs gs H k B label).result = checkLeaf cs gs H k B label := by
  cases label <;> simp [checkLeafTask, intervalTask_result, checkLeaf]

def checkTreeTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) : CoverTree n j → FinTask Bool
  | .leaf label => checkLeafTask cs gs H k B label
  | .split i l r => .step fun _ => do
    let hl ← checkTreeTask cs gs H k (splitBox B i false) l
    if hl then checkTreeTask cs gs H k (splitBox B i true) r else .done false

theorem checkTreeTask_result (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) (t : CoverTree n j) :
    (checkTreeTask cs gs H k B t).result = checkTree cs gs H k B t := by
  induction t generalizing B with
  | leaf label => exact checkLeafTask_result _ _ _ _ _ _
  | split i l r ihl ihr =>
    simp only [checkTreeTask, FinTask.result_step, FinTask.result_bindM, ihl, checkTree]
    split <;> simp_all

def visitTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0 < n) : Nat → Nat → QBox n → FinTask (Option (CoverTree n j))
  | 0, _, B => do
    let leaf ← chooseLeafTask cs gs H k B
    .step fun _ => .done (leaf.map .leaf)
  | remaining+1, depth, B => do
    let leaf ← chooseLeafTask cs gs H k B
    .step fun _ => match leaf with
      | some label => .done (some (.leaf label))
      | none => do
        let i : Fin n := ⟨depth%n, Nat.mod_lt _ hn⟩
        let lt ← visitTask cs gs H k hn remaining (depth+1) (splitBox B i false)
        match lt with
        | none => .done none
        | some lt => do
          let rt ← visitTask cs gs H k hn remaining (depth+1) (splitBox B i true)
          .done (rt.map (.split i lt))

theorem visitTask_result (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0 < n) (remaining depth : Nat) (B : QBox n) :
    (visitTask cs gs H k hn remaining depth B).result = (visit cs gs H k hn remaining depth B).2 := by
  induction remaining generalizing depth B with
  | zero =>
    simp only [visitTask, FinTask.result_bindM, chooseLeafTask_result, FinTask.result_step, visit]
    split <;> simp_all
  | succ remaining ih =>
    simp only [visitTask, FinTask.result_bindM, chooseLeafTask_result, FinTask.result_step, visit]
    split
    · simp_all
    · simp_all only
      simp only [FinTask.result_bindM, ih]
      split
      · simp_all
      · simp_all only
        simp only [FinTask.result_bindM, ih]
        split <;> simp_all

def stageTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (hn : 0 < n) (s : Nat) : FinTask (StageResult n j) := do
  let tree ← visitTask cs gs H s hn (n*s) 0 (unitBox n)
  match tree with
  | none => .done .inconclusive
  | some t => do
    let checked ← checkTreeTask cs gs H s (unitBox n) t
    .step fun _ => .done (if checked then .success t else .implementationError)

theorem stageTask_result (cs : Nat → Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (hn : 0 < n) (s : Nat) :
    (stageTask (cs s) gs H hn s).result = coverStage cs gs H hn s := by
  simp only [stageTask, FinTask.result_bindM, visitTask_result, coverStage]
  split
  · simp_all
  · simp_all [FinTask.result_bindM, checkTreeTask_result, FinTask.result_step, FinTask.result_done]

end Cover
