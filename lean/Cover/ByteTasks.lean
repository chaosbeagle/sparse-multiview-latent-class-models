import Cover.ByteCodec
import Cover.TokenTasks

namespace Cover.FinTask

def byteListLengthTask : List α → FinTask Nat
  | [] => .done 0
  | _::xs => .step fun _ => do
      let n ← byteListLengthTask xs
      .step fun _ => .done (n+1)

theorem byteListLengthTask_result (xs : List α) : (byteListLengthTask xs).result = xs.length := by
  induction xs <;> simp_all [byteListLengthTask]

def appendListTask : List α → List α → FinTask (List α)
  | [], ys => .done ys
  | x::xs, ys => .step fun _ => do
      let zs ← appendListTask xs ys
      .step fun _ => .done (x::zs)

theorem appendListTask_result (xs ys : List α) : (appendListTask xs ys).result = xs ++ ys := by
  induction xs <;> simp_all [appendListTask]

def mapListTask (f : α → β) : List α → FinTask (List β)
  | [] => .done []
  | x::xs => .step fun _ => do
      let ys ← mapListTask f xs
      .step fun _ => .done (f x::ys)

theorem mapListTask_result (f : α → β) (xs : List α) : (mapListTask f xs).result = xs.map f := by
  induction xs <;> simp_all [mapListTask]

def takeDropTask : Nat → List α → FinTask (List α × List α)
  | 0, xs => .done ([], xs)
  | _+1, [] => .done ([], [])
  | n+1, x::xs => .step fun _ => do
      let (front, back) ← takeDropTask n xs
      .step fun _ => .done (x::front, back)

theorem takeDropTask_result (n : Nat) (xs : List α) :
    (takeDropTask n xs).result = (xs.take n, xs.drop n) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp [takeDropTask, ih]

def equalListTask [DecidableEq α] : List α → List α → FinTask Bool
  | [], [] => .done true
  | [], _::_ => .done false
  | _::_, [] => .done false
  | x::xs, y::ys => .step fun _ => if x=y then equalListTask xs ys else .done false

theorem equalListTask_result [DecidableEq α] (xs ys : List α) :
    (equalListTask xs ys).result = decide (xs=ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys => by_cases h : x=y <;> simp [equalListTask, h, ih]
end Cover.FinTask

namespace Cover.Bytes
open FinTask

def encodeNatTask : Nat → FinTask Stream
  | 0 => .step fun _ => .done [0]
  | n+1 => .step fun _ => do
      let tail ← encodeNatTask n
      .step fun _ => .done (1::tail)

theorem encodeNatTask_result (n : Nat) : (encodeNatTask n).result = encodeNat n := by
  induction n <;> simp_all [encodeNatTask, encodeNat, List.replicate_succ]

def decodeNatTask : Stream → FinTask (Option (Nat × Stream))
  | [] => .done none
  | b::bs => .step fun _ =>
      if b=0 then .done (some (0,bs)) else if b=1 then do
        let parsed ← decodeNatTask bs
        .step fun _ => .done (parsed.map (fun (n, rest) => (n+1,rest)))
      else .done none

theorem decodeNatTask_result (bytes : Stream) : (decodeNatTask bytes).result = decodeNat bytes := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    simp only [decodeNatTask, FinTask.result_step, decodeNat]
    split <;> simp_all
    split <;> simp_all
    cases decodeNat bs <;> rfl

def flatEncodeTask (encode : α → FinTask Stream) : List α → FinTask Stream
  | [] => .done []
  | x::xs => .step fun _ => do
      let head ← encode x
      let tail ← flatEncodeTask encode xs
      appendListTask head tail

theorem flatEncodeTask_result (encode : α → FinTask Stream) (xs : List α) :
    (flatEncodeTask encode xs).result = xs.flatMap (fun x => (encode x).result) := by
  induction xs <;> simp_all [flatEncodeTask, appendListTask_result]

def encodeListTask (encode : α → FinTask Stream) (xs : List α) : FinTask Stream := do
  let n ← byteListLengthTask xs
  let head ← encodeNatTask n
  let tail ← flatEncodeTask encode xs
  appendListTask head tail

theorem encodeListTask_result (encode : α → FinTask Stream) (xs : List α) :
    (encodeListTask encode xs).result = encodeList (fun x => (encode x).result) xs := by
  simp [encodeListTask, byteListLengthTask_result, encodeNatTask_result, flatEncodeTask_result,
    appendListTask_result, encodeList]

def decodeManyTask (decode : Stream → FinTask (Option (α × Stream))) : Nat → Stream → FinTask (Option (List α × Stream))
  | 0, bytes => .done (some ([],bytes))
  | n+1, bytes => .step fun _ => do
      let head ← decode bytes
      match head with
      | none => .done none
      | some (x, rest) => do
          let tail ← decodeManyTask decode n rest
          .step fun _ => .done (tail.map (fun (xs, rest) => (x::xs,rest)))

theorem decodeManyTask_result (decode : Stream → FinTask (Option (α × Stream))) (n : Nat) (bytes : Stream) :
    (decodeManyTask decode n bytes).result = decodeMany (fun bytes => (decode bytes).result) n bytes := by
  induction n generalizing bytes with
  | zero => rfl
  | succ n ih =>
    simp only [decodeManyTask, FinTask.result_step, FinTask.result_bindM, decodeMany]
    split
    · simp_all
    · simp_all only
      simp only [FinTask.result_bindM, ih, FinTask.result_step, FinTask.result_done]
      dsimp only [Bind.bind, Option.bind]
      cases he : decodeMany (fun bs => (decode bs).result) n _ <;> simp_all

def decodeListTask (decode : Stream → FinTask (Option (α × Stream))) (bytes : Stream) : FinTask (Option (List α × Stream)) := do
  let head ← decodeNatTask bytes
  match head with
  | none => .done none
  | some (n, rest) => decodeManyTask decode n rest

theorem decodeListTask_result (decode : Stream → FinTask (Option (α × Stream))) (bytes : Stream) :
    (decodeListTask decode bytes).result = decodeList (fun bytes => (decode bytes).result) bytes := by
  simp only [decodeListTask, FinTask.result_bindM, decodeNatTask_result, decodeList]
  split <;> simp_all [decodeManyTask_result]

def encodeNatsTask := encodeListTask encodeNatTask
def decodeNatsTask := decodeListTask decodeNatTask

theorem encodeNatsTask_result (xs : List Nat) : (encodeNatsTask xs).result = encodeNats xs := by
  simp [encodeNatsTask, encodeListTask_result, encodeNatTask_result, encodeNats]

theorem decodeNatsTask_result (bytes : Stream) : (decodeNatsTask bytes).result = decodeNats bytes := by
  simp [decodeNatsTask, decodeListTask_result, decodeNatTask_result, decodeNats]

def evidenceFieldsTask : EvidenceToken → FinTask (List Nat)
  | .refinements weight sigma => .step fun _ => do
      let n ← byteListLengthTask weight
      let tail ← appendListTask weight sigma
      .done (0::n::tail)
  | .base token => .step fun _ => .done (1::coverFields token)
  | .unknown tag => .step fun _ => .done [2,tag]

theorem evidenceFieldsTask_result (token : EvidenceToken) :
    (evidenceFieldsTask token).result = evidenceFields token := by
  cases token <;> simp [evidenceFieldsTask, evidenceFields, byteListLengthTask_result, appendListTask_result]

def parseEvidenceFieldsTask (fields : List Nat) : FinTask (Option EvidenceToken) :=
  .step fun _ => match fields with
    | 0::len::rest => do
        let size ← byteListLengthTask rest
        if len≤size then do
          let (front, back) ← takeDropTask len rest
          .done (some (.refinements front back))
        else .done none
    | 1::rest => .done ((parseCoverFields rest).map .base)
    | [2,tag] => .done (some (.unknown tag))
    | _ => .done none

theorem parseEvidenceFieldsTask_result (fields : List Nat) :
    (parseEvidenceFieldsTask fields).result = parseEvidenceFields fields := by
  simp only [parseEvidenceFieldsTask, FinTask.result_step, parseEvidenceFields]
  split
  · simp_all only [byteListLengthTask_result, FinTask.result_bindM]
    split <;> simp_all [takeDropTask_result]
  · simp_all
  · simp_all
  · simp_all

def encodeEvidenceTokenTask (token : EvidenceToken) : FinTask Stream := do
  let fields ← evidenceFieldsTask token
  encodeNatsTask fields

theorem encodeEvidenceTokenTask_result (token : EvidenceToken) :
    (encodeEvidenceTokenTask token).result = encodeEvidenceToken token := by
  simp [encodeEvidenceTokenTask, evidenceFieldsTask_result, encodeNatsTask_result, encodeEvidenceToken, encodeFields]

def decodeEvidenceTokenTask (bytes : Stream) : FinTask (Option (EvidenceToken × Stream)) := do
  let fields ← decodeNatsTask bytes
  match fields with
  | none => .done none
  | some (fields, rest) => do
      let token ← parseEvidenceFieldsTask fields
      .done (token.map (·,rest))

theorem decodeEvidenceTokenTask_result (bytes : Stream) :
    (decodeEvidenceTokenTask bytes).result = decodeEvidenceToken bytes := by
  simp only [decodeEvidenceTokenTask, FinTask.result_bindM, decodeNatsTask_result, decodeEvidenceToken, decodeFields]
  split
  · simp_all
  · simp_all only
    simp only [FinTask.result_bindM, parseEvidenceFieldsTask_result, FinTask.result_done]
    dsimp only [Bind.bind, Option.bind]
    cases he : parseEvidenceFields _ <;> simp_all

end Cover.Bytes

namespace Cover.Bytes
open FinTask

def serializeEvidenceTokensTask (c : EvidenceCertificate n j) : FinTask (List EvidenceToken) := do
  let base ← serializeCertificateTask c.base
  let tokens ← mapListTask EvidenceToken.base base
  .step fun _ => .done (.refinements c.weightRefinement c.sigmaRefinement :: tokens)

theorem serializeEvidenceTokensTask_result (c : EvidenceCertificate n j) :
    (serializeEvidenceTokensTask c).result = serializeEvidenceCertificate c := by
  simp [serializeEvidenceTokensTask, serializeCertificateTask_result, mapListTask_result, serializeEvidenceCertificate]

def unwrapBaseTokensTask : List EvidenceToken → FinTask (Option (List CoverToken))
  | [] => .done (some [])
  | token::tokens => .step fun _ => match token with
    | .base t => do
        let rest ← unwrapBaseTokensTask tokens
        .step fun _ => .done (rest.map (t::·))
    | _ => .done none

theorem unwrapBaseTokensTask_result (tokens : List EvidenceToken) :
    (unwrapBaseTokensTask tokens).result = unwrapBaseTokens tokens := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih => cases token <;> simp [unwrapBaseTokensTask, unwrapBaseTokens, ih]

/-- The input token length scan itself is stepped before finite tree parsing. -/
def parseBaseCertificateTask (n j : Nat) (tokens : List CoverToken) : FinTask (Option (CoverCertificate n j)) :=
  .step fun _ => match tokens with
  | .header fmt gen k prec input :: rest => do
      let len ← byteListLengthTask rest
      let parsed ← parseTreeTask n j len rest
      .step fun _ => .done (do
        let (tree, trailing) ← parsed
        if trailing = [] then some ⟨fmt,gen,input,k,prec,tree⟩ else none)
  | _ => .done none

theorem parseBaseCertificateTask_result (n j : Nat) (tokens : List CoverToken) :
    (parseBaseCertificateTask n j tokens).result = parseCertificate n j tokens := by
  cases tokens with
  | nil => rfl
  | cons token rest => cases token <;> simp [parseBaseCertificateTask, byteListLengthTask_result, parseTreeTask_result, parseCertificate]

def parseEvidenceTokensTask (n j : Nat) (tokens : List EvidenceToken) : FinTask (Option (EvidenceCertificate n j)) :=
  .step fun _ => match tokens with
  | .refinements weight sigma :: rest => do
      let base ← unwrapBaseTokensTask rest
      match base with
      | none => .done none
      | some base => do
          let parsed ← parseBaseCertificateTask n j base
          .done (parsed.map (fun c => ⟨c,weight,sigma⟩))
  | _ => .done none

theorem parseEvidenceTokensTask_result (n j : Nat) (tokens : List EvidenceToken) :
    (parseEvidenceTokensTask n j tokens).result = parseEvidenceCertificate n j tokens := by
  cases tokens with
  | nil => rfl
  | cons token rest =>
    cases token with
    | base t => rfl
    | unknown t => rfl
    | refinements weight sigma =>
      simp only [parseEvidenceTokensTask, FinTask.result_step, FinTask.result_bindM,
        unwrapBaseTokensTask_result, parseEvidenceCertificate]
      split
      · simp_all
      · simp_all only
        simp only [FinTask.result_bindM, parseBaseCertificateTask_result, FinTask.result_done]
        dsimp only [Bind.bind, Option.bind]
        cases he : parseCertificate n j _ <;> simp_all

def serializeEvidenceBytesTask (c : EvidenceCertificate n j) : FinTask Stream := do
  let tokens ← serializeEvidenceTokensTask c
  encodeListTask encodeEvidenceTokenTask tokens

theorem serializeEvidenceBytesTask_result (c : EvidenceCertificate n j) :
    (serializeEvidenceBytesTask c).result = serializeEvidenceBytes c := by
  simp [serializeEvidenceBytesTask, serializeEvidenceTokensTask_result, encodeListTask_result,
    encodeEvidenceTokenTask_result, serializeEvidenceBytes]

def parseEvidenceBytesTask (n j : Nat) (bytes : Stream) : FinTask (Option (EvidenceCertificate n j)) := do
  let parsed ← decodeListTask decodeEvidenceTokenTask bytes
  match parsed with
  | none => .done none
  | some (tokens, rest) => .step fun _ =>
      if rest = [] then parseEvidenceTokensTask n j tokens else .done none

theorem parseEvidenceBytesTask_result (n j : Nat) (bytes : Stream) :
    (parseEvidenceBytesTask n j bytes).result = parseEvidenceBytes n j bytes := by
  simp only [parseEvidenceBytesTask, FinTask.result_bindM, decodeListTask_result,
    decodeEvidenceTokenTask_result, parseEvidenceBytes]
  split
  · simp_all
  · simp_all only
    simp only [FinTask.result_step]
    dsimp only [Bind.bind, Option.bind]
    split <;> simp_all [parseEvidenceTokensTask_result]

end Cover.Bytes
