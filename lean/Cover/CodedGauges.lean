import Cover.CodedPermutations

namespace Cover
open Gen.ModelEncoding.Ordered

/-- Native array row in exactly the supplied component enumeration order. -/
structure GaugeRow (count r : ℕ) where
  codes : Array (PermCode (Fin r))
  size_eq : codes.size=count

namespace GaugeRow

def getCode (row : GaugeRow count r) (i : Fin count) : PermCode (Fin r) :=
  row.codes[i.val]'(by rw [row.size_eq];exact i.isLt)

/-- Mathematical denotation only. Executable application uses the stepped index
callback below and never evaluates this pure indexEquiv lookup. -/
noncomputable def denote {C : Type} [DecidableEq C] (components : Enumeration C)
    (row : GaugeRow components.values.length r) : C → Equiv.Perm (Fin r) :=
  fun c => (row.getCode ((FiniteEnumeration.indexEquiv components).symm c)).eval

end GaugeRow

/-- Locate a component with the supplied stepped equality algorithm, read its code
from the native array, then interpret every permutation-code node explicitly. -/
def gaugeApplyTask {C : Type} [DecidableEq C] (components : Enumeration C)
    (row : GaugeRow components.values.length r) (c : C) (z : Fin r)
    (eqTask : C → C → FinTask Bool) (heq : ∀ a b,(eqTask a b).result=decide (a=b)) :
    FinTask (Fin r) := .step fun _ => do
  let index ← FiniteEnumeration.indexTaskWith components c eqTask heq
  let code ← FinTask.primitive (fun _ => row.getCode index)
  code.appTask z

@[simp] theorem gaugeApplyTask_result {C : Type} [DecidableEq C] (components : Enumeration C)
    (row : GaugeRow components.values.length r) (c : C) (z : Fin r)
    (eqTask : C → C → FinTask Bool) (heq : ∀ a b,(eqTask a b).result=decide (a=b)) :
    (gaugeApplyTask components row c z eqTask heq).result=row.denote components c z := by
  simp [gaugeApplyTask,GaugeRow.denote]

theorem gaugeApplyTask_zero_unknown {C : Type} [DecidableEq C] (components : Enumeration C)
    (row : GaugeRow components.values.length r) (c : C) (z : Fin r)
    (eqTask : C → C → FinTask Bool) (heq : ∀ a b,(eqTask a b).result=decide (a=b)) :
    FinTask.run 0 (gaugeApplyTask components row c z eqTask heq) = none := rfl

end Cover

namespace Cover.FinTask

def listToArrayAccTask {α : Type} (acc : Array α) : List α → FinTask (Array α)
  | [] => .step fun _ => .done acc
  | a::as => .step fun _ => do
      let next ← primitive (fun _ => acc.push a)
      listToArrayAccTask next as

theorem listToArrayAccTask_toList {α : Type} (acc : Array α) (xs : List α) :
    (listToArrayAccTask acc xs).result.toList = acc.toList ++ xs := by
  induction xs generalizing acc with
  | nil => simp [listToArrayAccTask]
  | cons a as ih => simp [listToArrayAccTask,ih,List.append_assoc]

def listToArrayTask {α : Type} (xs : List α) : FinTask (Array α) := listToArrayAccTask #[] xs
@[simp] theorem listToArrayTask_toList {α : Type} (xs : List α) : (listToArrayTask xs).result.toList=xs := by
  simp [listToArrayTask,listToArrayAccTask_toList]

end Cover.FinTask

namespace Cover.GaugeRow
open Gen.ModelEncoding.Ordered

def fromListTask (xs : List (PermCode (Fin r))) (h : xs.length=count) : FinTask (GaugeRow count r) := do
  let a ← (FinTask.listToArrayTask xs).attach
  .step fun _ => .done ⟨a.val,by
    have he : a.val.toList=xs := by
      rw [a.property]
      exact FinTask.listToArrayTask_toList xs
    have hl := congrArg List.length he
    simpa only [Array.length_toList,h] using hl⟩

@[simp] theorem fromListTask_toList (xs : List (PermCode (Fin r))) (h : xs.length=count) :
    (fromListTask xs h).result.codes.toList=xs := by
  simp [fromListTask]

end Cover.GaugeRow

namespace Cover
open Gen.ModelEncoding.Ordered

/-- Ordinary list specification for component-ordered Cartesian rows. -/
def gaugeCodeLists {C : Type} (perms : List (CodedPerm (Fin r))) : List C → List (List (PermCode (Fin r)))
  | [] => [[]]
  | _::cs => perms.flatMap (fun p => (gaugeCodeLists perms cs).map (fun xs => p.code::xs))

/-- Cartesian enumeration in the same head-choice/tail-row order as List.pi. -/
def gaugeCodeListsTask {C : Type} (perms : List (CodedPerm (Fin r))) : List C → FinTask (List (List (PermCode (Fin r))))
  | [] => .step fun _ => .done [[]]
  | _::cs => .step fun _ => do
      let tails ← gaugeCodeListsTask perms cs
      FinTask.flatMapTask (fun p => FinTask.mapTask
        (fun xs => FinTask.primitive (fun _ => p.code::xs)) tails) perms

@[simp] theorem gaugeCodeListsTask_result {C : Type} (perms : List (CodedPerm (Fin r))) (cs : List C) :
    (gaugeCodeListsTask perms cs).result=gaugeCodeLists perms cs := by
  induction cs <;> simp_all [gaugeCodeListsTask,gaugeCodeLists]

theorem gaugeCodeLists_length {C : Type} (perms : List (CodedPerm (Fin r))) (cs : List C)
    (xs : List (PermCode (Fin r))) (h : xs∈gaugeCodeLists perms cs) : xs.length=cs.length := by
  induction cs generalizing xs with
  | nil => simpa [gaugeCodeLists] using h
  | cons c cs ih =>
      obtain ⟨p,hp,hx⟩ := List.mem_flatMap.mp h
      obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
      simp only [List.length_cons]
      exact congrArg (·+1) (ih ys hy)

/-- Native array construction occurs through one push per generated code. -/
def gaugeRowsTask {C : Type} (components : Enumeration C) (perms : List (CodedPerm (Fin r))) :
    FinTask (List (GaugeRow components.values.length r)) := .step fun _ => do
  let raw ← (gaugeCodeListsTask perms components.values).attach
  let marked ← FinTask.attachWithTask (fun xs : List (PermCode (Fin r)) => xs.length=components.values.length)
    raw.val (by
      intro xs hx
      rw [raw.property,gaugeCodeListsTask_result] at hx
      exact gaugeCodeLists_length perms components.values xs hx)
  FinTask.mapTask (fun xs => GaugeRow.fromListTask xs.val xs.property) marked

@[simp] theorem gaugeRowsTask_toLists {C : Type} (components : Enumeration C)
    (perms : List (CodedPerm (Fin r))) :
    (gaugeRowsTask components perms).result.map (fun row => row.codes.toList)=gaugeCodeLists perms components.values := by
  simp [gaugeRowsTask,List.map_map]

end Cover

namespace Cover.GaugeSemantics
open Gen.ModelEncoding.Ordered

/-- Proof-only interpretation of an ordered code row. -/
noncomputable def listDenote {C : Type} [DecidableEq C] :
    List C → List (PermCode (Fin r)) → C → Equiv.Perm (Fin r)
  | c::cs,p::ps,x => if x=c then p.eval else listDenote cs ps x
  | _,_,_ => 1

noncomputable def extendPi {C : Type} [DecidableEq C] (cs : List C)
    (f : ∀ c,c∈cs → Equiv.Perm (Fin r)) : C → Equiv.Perm (Fin r) :=
  fun c => if hc : c∈cs then f c hc else 1

theorem extendPi_cons {C : Type} [DecidableEq C] (c : C) (cs : List C)
    (p : Equiv.Perm (Fin r)) (f : ∀ c,c∈cs → Equiv.Perm (Fin r)) :
    extendPi (c::cs) (List.Pi.cons c cs p f) = fun x => if x=c then p else extendPi cs f x := by
  funext x
  by_cases h : x=c
  · subst x;simp [extendPi,List.Pi.cons_def]
  · by_cases hx : x∈cs <;> simp [extendPi,List.Pi.cons_def,h,hx]

noncomputable def valueRows {C : Type} [DecidableEq C] (perms : List (Equiv.Perm (Fin r))) :
    List C → List (C → Equiv.Perm (Fin r))
  | [] => [fun _ => 1]
  | c::cs => perms.flatMap (fun p => (valueRows perms cs).map (fun f x => if x=c then p else f x))

theorem valueRows_eq_pi {C : Type} [DecidableEq C] (perms : List (Equiv.Perm (Fin r))) (cs : List C) :
    valueRows perms cs = (List.pi cs (fun _ => perms)).map (extendPi cs) := by
  induction cs with
  | nil =>
      simp only [valueRows,List.pi_nil,List.map_singleton]
      congr 1
  | cons c cs ih =>
      simp only [valueRows,List.pi_cons,List.map_flatMap,List.map_map]
      apply congrArg (List.flatMap · perms)
      funext p
      rw [ih]
      simp only [List.map_map]
      apply List.map_congr_left
      intro f hf
      exact (extendPi_cons c cs p f).symm

theorem gaugeCodeLists_denote {C : Type} [DecidableEq C]
    (perms : List (CodedPerm (Fin r))) (cs : List C) :
    (gaugeCodeLists perms cs).map (listDenote cs) = valueRows (perms.map CodedPerm.legacy) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [gaugeCodeLists,valueRows,List.map_flatMap,List.map_map,List.flatMap_map]
      apply congrArg (List.flatMap · perms)
      funext p
      rw [←ih]
      simp only [List.map_map]
      apply List.map_congr_left
      intro row hrow
      funext x
      simp only [Function.comp_def,listDenote,p.correct]

theorem listDenote_get {C : Type} [DecidableEq C] (cs : List C)
    (codes : List (PermCode (Fin r))) (hlen : codes.length=cs.length) (hnd : cs.Nodup)
    (j : ℕ) (hj : j<cs.length) :
    listDenote cs codes cs[j] = (codes[j]'(by omega)).eval := by
  induction cs generalizing codes j with
  | nil => simp at hj
  | cons c cs ih =>
      cases codes with
      | nil => simp at hlen
      | cons p ps =>
          have ht : ps.length=cs.length := by simpa using hlen
          cases j with
          | zero => simp [listDenote]
          | succ j =>
              have hj' : j<cs.length := by simpa using hj
              have hne : cs[j]≠c := by
                intro he
                have hm : cs[j]∈cs := List.get_mem cs ⟨j,hj'⟩
                rw [he] at hm
                exact (List.nodup_cons.mp hnd).1 hm
              simp only [List.getElem_cons_succ,listDenote,if_neg hne]
              exact ih ps ht (List.nodup_cons.mp hnd).2 j hj'

end Cover.GaugeSemantics

namespace Cover.GaugeRow
open Gen.ModelEncoding.Ordered

theorem denote_eq_listDenote {C : Type} [DecidableEq C] (components : Enumeration C)
    (row : GaugeRow components.values.length r) :
    row.denote components = GaugeSemantics.listDenote components.values row.codes.toList := by
  funext c
  let k := (FiniteEnumeration.indexEquiv components).symm c
  have hk : components.values[k.val]=c := (FiniteEnumeration.indexEquiv components).apply_symm_apply c
  have hlen : row.codes.toList.length=components.values.length := by simp [row.size_eq]
  have h := GaugeSemantics.listDenote_get components.values row.codes.toList hlen components.nodup k.val k.isLt
  rw [hk] at h
  change (row.codes[k.val]'(by rw [row.size_eq];exact k.isLt)).eval = _
  simpa only [Array.getElem_toList] using h.symm

end Cover.GaugeRow

namespace Cover
open Gen.ModelEncoding.Ordered

theorem gaugeRowsTask_denote {C : Type} [Fintype C] [DecidableEq C]
    (components : Enumeration C) (perms : List (CodedPerm (Fin r)))
    (legacy : Enumeration (Equiv.Perm (Fin r))) (hperms : perms.map CodedPerm.legacy=legacy.values) :
    (gaugeRowsTask components perms).result.map (GaugeRow.denote components) =
      (FiniteEnumeration.pi components (fun _ => legacy)).values := by
  calc
    _ = ((gaugeRowsTask components perms).result.map (fun row => row.codes.toList)).map
        (GaugeSemantics.listDenote components.values) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro row hrow
      exact GaugeRow.denote_eq_listDenote components row
    _ = (gaugeCodeLists perms components.values).map (GaugeSemantics.listDenote components.values) := by
      rw [gaugeRowsTask_toLists]
    _ = GaugeSemantics.valueRows legacy.values components.values := by
      rw [GaugeSemantics.gaugeCodeLists_denote,hperms]
    _ = (FiniteEnumeration.pi components (fun _ => legacy)).values := by
      rw [GaugeSemantics.valueRows_eq_pi,FiniteEnumeration.pi_values]
      apply List.map_congr_left
      intro f hf
      funext c
      simp [GaugeSemantics.extendPi,components.complete c]

/-- End-to-end coded row generation; no supplied correctness premise is needed
when the per-component choices come from the concrete coded permutation task. -/
def codedGaugeRowsTask {C : Type} (components : Enumeration C) (latent : Enumeration (Fin r)) :
    FinTask (List (GaugeRow components.values.length r)) := do
  let perms ← FiniteEnumeration.codedPermutationsTask latent
  gaugeRowsTask components perms

@[simp] theorem codedGaugeRowsTask_denote {C : Type} [Fintype C] [DecidableEq C]
    (components : Enumeration C) (latent : Enumeration (Fin r)) :
    (codedGaugeRowsTask components latent).result.map (GaugeRow.denote components) =
      (FiniteEnumeration.pi components (fun _ => FiniteEnumeration.permutations latent)).values := by
  simp only [codedGaugeRowsTask,FinTask.result_bindM]
  exact gaugeRowsTask_denote components _ _ (FiniteEnumeration.codedPermutationsTask_legacy latent)

end Cover
