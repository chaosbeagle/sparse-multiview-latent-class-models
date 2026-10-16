import Cover.Fuel

namespace Cover.FinTask
variable {α β : Type}

/-- One explicitly declared finite primitive; its internal physical cost is not counted. -/
def primitive (f : Unit → α) : FinTask α := .step (fun _ => .done (f ()))
@[simp] theorem primitive_result (f : Unit → α) : (primitive f).result = f () := rfl

/-- List construction and element computations are interleaved with resumable steps. -/
def mapTask (f : α → FinTask β) : List α → FinTask (List β)
  | [] => .step fun _ => .done []
  | a::as => .step fun _ => do
      let b ← f a
      let bs ← mapTask f as
      .step fun _ => .done (b::bs)
@[simp] theorem mapTask_result (f : α → FinTask β) (as : List α) :
    (mapTask f as).result = as.map (fun a => (f a).result) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [mapTask,ih]

def appendTask : List α → List α → FinTask (List α)
  | [], bs => .step fun _ => .done bs
  | a::as, bs => .step fun _ => do
      let cs ← appendTask as bs
      .step fun _ => .done (a::cs)
@[simp] theorem appendTask_result (as bs : List α) :
    (appendTask as bs).result = as ++ bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [appendTask,ih]

def flatMapTask (f : α → FinTask (List β)) : List α → FinTask (List β)
  | [] => .step fun _ => .done []
  | a::as => .step fun _ => do
      let bs ← f a
      let cs ← flatMapTask f as
      appendTask bs cs
@[simp] theorem flatMapTask_result (f : α → FinTask (List β)) (as : List α) :
    (flatMapTask f as).result = as.flatMap (fun a => (f a).result) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [flatMapTask,ih]

def filterTask (p : α → Bool) : List α → FinTask (List α)
  | [] => .step fun _ => .done []
  | a::as => .step fun _ => do
      let bs ← filterTask p as
      .step fun _ => .done (if p a then a::bs else bs)
@[simp] theorem filterTask_result (p : α → Bool) (as : List α) :
    (filterTask p as).result = as.filter p := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [filterTask,ih,List.filter_cons]

/-- Token splitting consumes one resumable transition per token. -/
def takeTask : ℕ → List α → FinTask (Option (List α × List α))
  | 0, xs => .step fun _ => .done (some ([],xs))
  | n+1, [] => .step fun _ => .done none
  | n+1, x::xs => .step fun _ => do
      let p ← takeTask n xs
      .step fun _ => .done (p.map (fun q => (x::q.1,q.2)))

theorem takeTask_result (n : ℕ) (xs : List α) :
    (takeTask n xs).result = if n ≤ xs.length then some (xs.take n,xs.drop n) else none := by
  induction n generalizing xs with
  | zero => simp [takeTask]
  | succ n ih =>
    cases xs with
    | nil => simp [takeTask]
    | cons x xs =>
      by_cases hn : n ≤ xs.length
      · simp [takeTask,ih,hn]
      · simp [takeTask,ih,hn]
end Cover.FinTask

namespace Cover.FinTask
variable {α : Type}
def allTask (f : α → FinTask Bool) : List α → FinTask Bool
  | [] => .step fun _ => .done true
  | a::as => .step fun _ => do
      let b ← f a
      if b then allTask f as else .done false
@[simp] theorem allTask_result (f : α → FinTask Bool) (as : List α) :
    (allTask f as).result = as.all (fun a => (f a).result) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [allTask,ih]; split <;> simp_all

def anyTask (f : α → FinTask Bool) : List α → FinTask Bool
  | [] => .step fun _ => .done false
  | a::as => .step fun _ => do
      let b ← f a
      if b then .done true else anyTask f as
@[simp] theorem anyTask_result (f : α → FinTask Bool) (as : List α) :
    (anyTask f as).result = as.any (fun a => (f a).result) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [anyTask,ih]; split <;> simp_all

def nodupTask [DecidableEq α] : List α → FinTask Bool
  | [] => .step fun _ => .done true
  | a::as => .step fun _ => do
      let seen ← anyTask (fun b => primitive (fun _ => decide (a = b))) as
      if seen then .done false else nodupTask as
@[simp] theorem nodupTask_result [DecidableEq α] (as : List α) :
    (nodupTask as).result = decide as.Nodup := by
  induction as with
  | nil => simp [nodupTask]
  | cons a as ih =>
    by_cases ha : a ∈ as
    · simp [nodupTask,ih,ha]
    · simp [nodupTask,ih,ha]
end Cover.FinTask

namespace Cover.FinTask
/-- Attach the existing exact result specification without evaluating it eagerly.
The proof component is erased; execution is exactly the original transition tree. -/
def certify {α : Type} : (p : FinTask α) → FinTask {a : α // a = p.result}
  | .done a => .done ⟨a,rfl⟩
  | .step next => .step (fun _ => certify (next ()))
@[simp] theorem certify_result_val {α : Type} (p : FinTask α) :
    (certify p).result.val = p.result := (certify p).result.property
end Cover.FinTask

namespace Cover.FinTask
@[simp] theorem certify_result {α : Type} (p : FinTask α) :
    (certify p).result = ⟨p.result,rfl⟩ := Subtype.ext (certify_result_val p)

def finRangeTask : (n : ℕ) → FinTask (List (Fin n))
  | 0 => .step fun _ => .done []
  | n+1 => .step fun _ => do
      let xs ← finRangeTask n
      let ys ← mapTask (fun i => primitive (fun _ => i.succ)) xs
      .step fun _ => .done (0::ys)
@[simp] theorem finRangeTask_result (n : ℕ) : (finRangeTask n).result = List.finRange n := by
  induction n <;> simp_all [finRangeTask,List.finRange_succ]
end Cover.FinTask
