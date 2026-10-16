import Cover.FiniteTasks
import Cover.AlgebraicPrimitiveTasks

namespace Cover
open FinTask

/-- Final capped boxes have only two representations: the constant unit root or
    a materialized finite array. Nested split-history closures are unrepresentable. -/
inductive StoredBox (n : Nat) where
  | unit
  | array (values : Array QInterval) (size_eq : values.size = n)

 def StoredBox.view : StoredBox n → QBox n
  | .unit => unitBox n
  | .array values h => fun i => values[i.val]'(by rw [h]; exact i.isLt)

/-- Coordinate scanning is internally stepped. The final list-to-native-array
    operation is a named representation primitive with no physical allocation bound. -/
def splitStoredTask (B : StoredBox n) (i : Fin n) (right : Bool) :
    FinTask {C : StoredBox n // C.view = splitBox B.view i right} := do
  let coords ← (finRangeTask n).attach
  let values ← (mapTask (fun j => primitive (fun _ => splitBox B.view i right j)) coords.val).attach
  let array ← (primitive (fun _ => values.val.toArray)).attach
  have hcoords : coords.val = List.finRange n := coords.property.trans (finRangeTask_result n)
  have hvalues : values.val = (List.finRange n).map (splitBox B.view i right) := by
    rw [values.property,mapTask_result,hcoords]
    rfl
  have harray : array.val = ((List.finRange n).map (splitBox B.view i right)).toArray := by
    rw [array.property,primitive_result,hvalues]
  have hsize : array.val.size = n := by simp [harray]
  let C : StoredBox n := .array array.val hsize
  have hview : C.view = splitBox B.view i right := by
    funext k
    simp [C,StoredBox.view,harray]
  .done ⟨C,hview⟩

 theorem splitStoredTask_result (B : StoredBox n) (i : Fin n) (right : Bool) :
    (splitStoredTask B i right).result.val.view = splitBox B.view i right :=
  (splitStoredTask B i right).result.property

 def checkTreeStoredTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : StoredBox n) : CoverTree n j → FinTask Bool
  | .leaf label => checkLeafTask cs gs H k B.view label
  | .split i left right => .step fun _ => do
      let lb ← splitStoredTask B i false
      let hl ← checkTreeStoredTask cs gs H k lb.val left
      if hl then do
        let rb ← splitStoredTask B i true
        checkTreeStoredTask cs gs H k rb.val right
      else .done false

 theorem checkTreeStoredTask_result (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : StoredBox n) (tree : CoverTree n j) :
    (checkTreeStoredTask cs gs H k B tree).result = checkTree cs gs H k B.view tree := by
  induction tree generalizing B with
  | leaf label => exact checkLeafTask_result _ _ _ _ _ _
  | split i left right ihl ihr =>
    simp only [checkTreeStoredTask,FinTask.result_step,FinTask.result_bindM,ihl,
      splitStoredTask_result,checkTree]
    split <;> simp_all [ihr,splitStoredTask_result]

/-- The constraint index list is generated under fuel, rather than eagerly by List.finRange. -/
def chooseLeafStoredTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) : FinTask (Option (CoverLeaf j)) := do
  let indices ← finRangeTask j
  let idx ← firstExcludeTask cs gs B indices
  match idx with
  | some i => .done (some (.exclude i))
  | none => do
      let I ← intervalTask cs B H
      .step fun _ => if dyadic (2*k) ≤ I.lower then .done (some .gap) else .done none

theorem chooseLeafStoredTask_result (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (B : QBox n) :
    (chooseLeafStoredTask cs gs H k B).result = chooseLeaf cs gs H k B := by
  simp only [chooseLeafStoredTask,FinTask.result_bindM,finRangeTask_result,
    firstExcludeTask_result,chooseLeaf,firstExclude]
  split
  · simp_all
  · simp_all only
    simp only [FinTask.result_bindM,intervalTask_result,FinTask.result_step]
    split <;> rfl

 def visitStoredTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0<n) : Nat → Nat → StoredBox n → FinTask (Option (CoverTree n j))
  | 0, _, B => do
      let leaf ← chooseLeafStoredTask cs gs H k B.view
      .step fun _ => .done (leaf.map .leaf)
  | remaining+1, depth, B => do
      let leaf ← chooseLeafStoredTask cs gs H k B.view
      .step fun _ => match leaf with
        | some label => .done (some (.leaf label))
        | none => do
            let i : Fin n := ⟨depth%n,Nat.mod_lt _ hn⟩
            let lb ← splitStoredTask B i false
            let left ← visitStoredTask cs gs H k hn remaining (depth+1) lb.val
            match left with
            | none => .done none
            | some left => do
                let rb ← splitStoredTask B i true
                let right ← visitStoredTask cs gs H k hn remaining (depth+1) rb.val
                .step fun _ => .done (right.map (.split i left))

 theorem visitStoredTask_result (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (k : Nat) (hn : 0<n) (remaining depth : Nat) (B : StoredBox n) :
    (visitStoredTask cs gs H k hn remaining depth B).result =
      (visit cs gs H k hn remaining depth B.view).2 := by
  induction remaining generalizing depth B with
  | zero =>
    simp only [visitStoredTask,FinTask.result_bindM,chooseLeafStoredTask_result,FinTask.result_step,visit]
    split <;> simp_all
  | succ remaining ih =>
    simp only [visitStoredTask,FinTask.result_bindM,chooseLeafStoredTask_result,FinTask.result_step,visit]
    split
    · simp_all
    · simp_all only
      simp only [FinTask.result_bindM,ih,splitStoredTask_result]
      split
      · simp_all
      · simp_all only
        simp only [FinTask.result_bindM,ih,splitStoredTask_result,FinTask.result_step]
        split <;> simp_all

 def stageStoredTask (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (hn : 0<n) (s : Nat) : FinTask (StageResult n j) := do
  let tree ← visitStoredTask cs gs H s hn (n*s) 0 .unit
  match tree with
  | none => .done .inconclusive
  | some t => do
      let checked ← checkTreeStoredTask cs gs H s .unit t
      .step fun _ => .done (if checked then .success t else .implementationError)

 theorem stageStoredTask_result_eq (cs : Fin a → QInterval) (gs : Fin j → PolyExpr n a)
    (H : PolyExpr n a) (hn : 0<n) (s : Nat) :
    (stageStoredTask cs gs H hn s).result = (stageTask cs gs H hn s).result := by
  simp only [stageStoredTask,stageTask,FinTask.result_bindM,visitStoredTask_result,
    visitTask_result,StoredBox.view]
  split
  · simp_all
  · simp_all [checkTreeStoredTask_result,checkTreeTask_result,StoredBox.view]

end Cover
