import Cover.Fuel
import Cover.Certificate

namespace Cover

def appendTokensTask : List CoverToken → List CoverToken → FinTask (List CoverToken)
  | [], right => .done right
  | t::ts, right => .step fun _ => do
      let rest ← appendTokensTask ts right
      .step fun _ => .done (t::rest)

theorem appendTokensTask_result (left right : List CoverToken) :
    (appendTokensTask left right).result = left ++ right := by
  induction left with
  | nil => rfl
  | cons t ts ih => simp [appendTokensTask, ih]

def serializeTreeTask : CoverTree n j → FinTask (List CoverToken)
  | .leaf .gap => .step fun _ => .done [.gap]
  | .leaf (.exclude i) => .step fun _ => .done [.exclude i.val]
  | .split i l r => .step fun _ => do
      let left ← serializeTreeTask l
      let right ← serializeTreeTask r
      let tail ← appendTokensTask left right
      .step fun _ => .done (.split i.val :: tail)

theorem serializeTreeTask_result (t : CoverTree n j) :
    (serializeTreeTask t).result = serializeTree t := by
  induction t with
  | leaf label => cases label <;> rfl
  | split i l r ihl ihr => simp [serializeTreeTask, appendTokensTask_result, ihl, ihr, serializeTree]

def serializeCertificateTask (c : CoverCertificate n j) : FinTask (List CoverToken) := do
  let tail ← serializeTreeTask c.tree
  .step fun _ => .done (.header c.formatVersion c.generatorVersion c.k c.precision c.input :: tail)

theorem serializeCertificateTask_result (c : CoverCertificate n j) :
    (serializeCertificateTask c).result = serializeCertificate c := by
  simp [serializeCertificateTask, serializeTreeTask_result, serializeCertificate]

def parseTreeTask (n j : Nat) : Nat → List CoverToken → FinTask (Option (CoverTree n j × List CoverToken))
  | 0, _ => .done none
  | fuel+1, tokens => .step fun _ => match tokens with
    | .gap :: rest => .done (some (.leaf .gap, rest))
    | .exclude i :: rest => .done (if hi : i < j then some (.leaf (.exclude ⟨i, hi⟩), rest) else none)
    | .split i :: rest => if hi : i < n then do
        let left ← parseTreeTask n j fuel rest
        match left with
        | none => .done none
        | some (l, rest) => do
          let right ← parseTreeTask n j fuel rest
          .step fun _ => .done (right.map (fun (r, rest) => (.split ⟨i, hi⟩ l r, rest)))
      else .done none
    | _ => .done none

theorem parseTreeTask_result (n j fuel : Nat) (tokens : List CoverToken) :
    (parseTreeTask n j fuel tokens).result = parseTree n j fuel tokens := by
  induction fuel generalizing tokens with
  | zero => rfl
  | succ fuel ih =>
    cases tokens with
    | nil => rfl
    | cons token tokens =>
      cases token with
      | header fmt gen k prec input => rfl
      | gap => rfl
      | exclude i => rfl
      | unknown tag => rfl
      | split i =>
        simp only [parseTreeTask, FinTask.result_step, parseTree]
        split
        · simp only [FinTask.result_bindM, ih]
          split
          · simp_all
          · simp_all only
            simp only [FinTask.result_bindM, ih, FinTask.result_step, FinTask.result_done]
            cases h : parseTree n j fuel _ <;> simp_all
        · simp_all

def tokenLengthTask : List CoverToken → FinTask Nat
  | [] => .step fun _ => .done 0
  | _::tokens => .step fun _ => do
      let n ← tokenLengthTask tokens
      .step fun _ => .done (n+1)

theorem tokenLengthTask_result (tokens : List CoverToken) :
    (tokenLengthTask tokens).result = tokens.length := by
  induction tokens <;> simp_all [tokenLengthTask]

def parseCertificateTask (n j : Nat) (tokens : List CoverToken) : FinTask (Option (CoverCertificate n j)) :=
  .step fun _ => match tokens with
  | .header fmt gen k prec input :: rest => do
      let len ← tokenLengthTask rest
      let parsed ← parseTreeTask n j len rest
      .step fun _ => .done (do
        let (tree, trailing) ← parsed
        if trailing = [] then some ⟨fmt, gen, input, k, prec, tree⟩ else none)
  | _ => .done none

theorem parseCertificateTask_result (n j : Nat) (tokens : List CoverToken) :
    (parseCertificateTask n j tokens).result = parseCertificate n j tokens := by
  cases tokens with
  | nil => rfl
  | cons token rest => cases token <;> simp [parseCertificateTask, tokenLengthTask_result, parseTreeTask_result, parseCertificate]

end Cover
