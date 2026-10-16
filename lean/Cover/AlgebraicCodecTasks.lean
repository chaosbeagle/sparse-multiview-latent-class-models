import Cover.AlgebraicCodec
import Cover.AlgebraicStepped

namespace Cover.AlgCodec

 def encodeIntTask (z : ℤ) : FinTask ℕ :=
  .step fun _ => match z with
  | .ofNat n => .step fun _ => .done (2*n)
  | .negSucc n => do
    let v ← FinTask.step fun _ => .done (2*n)
    .step fun _ => .done (v+1)

 theorem encodeIntTask_result (z : ℤ) : (encodeIntTask z).result = encodeInt z := by
  cases z <;> simp [encodeIntTask, encodeInt]

 def decodeIntTask (n : ℕ) : FinTask ℤ := do
  let r ← FinTask.step fun _ => .done (n%2)
  let q ← FinTask.step fun _ => .done (n/2)
  .step fun _ => .done (if r=0 then .ofNat q else .negSucc q)

 theorem decodeIntTask_result (n : ℕ) : (decodeIntTask n).result = decodeInt n := by
  simp [decodeIntTask, decodeInt]

 def natLengthTask : List ℕ → FinTask ℕ
  | [] => .done 0
  | _::ts => .step fun _ => do
    let n ← natLengthTask ts
    .step fun _ => .done (n+1)

 theorem natLengthTask_result (xs : List ℕ) : (natLengthTask xs).result = xs.length := by
  induction xs <;> simp_all [natLengthTask]

 def natEqualTask : List ℕ → List ℕ → FinTask Bool
  | [], [] => .done true
  | [], _::_ => .done false
  | _::_, [] => .done false
  | a::as, b::bs => .step fun _ => if a=b then natEqualTask as bs else .done false

 theorem natEqualTask_result (xs ys : List ℕ) : (natEqualTask xs ys).result = decide (xs=ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a as ih => cases ys with
    | nil => rfl
    | cons b bs => by_cases h : a=b <;> simp [natEqualTask, h, ih]

 def appendTask : List ℕ → List ℕ → FinTask (List ℕ)
  | [], ys => .done ys
  | x::xs, ys => .step fun _ => do
    let zs ← appendTask xs ys
    .step fun _ => .done (x::zs)

 theorem appendTask_result (xs ys : List ℕ) : (appendTask xs ys).result = xs++ys := by
  induction xs <;> simp_all [appendTask]

 def encodeListTask : List ℤ → FinTask (List ℕ)
  | [] => .done []
  | z::zs => .step fun _ => do
    let a ← encodeIntTask z
    let ts ← encodeListTask zs
    .step fun _ => .done (a::ts)

 theorem encodeListTask_result (zs : List ℤ) : (encodeListTask zs).result = zs.map encodeInt := by
  induction zs <;> simp_all [encodeListTask, encodeIntTask_result]

 def decodeListTask : List ℕ → FinTask (List ℤ)
  | [] => .done []
  | z::zs => .step fun _ => do
    let a ← decodeIntTask z
    let ts ← decodeListTask zs
    .step fun _ => .done (a::ts)

 theorem decodeListTask_result (zs : List ℕ) : (decodeListTask zs).result = zs.map decodeInt := by
  induction zs <;> simp_all [decodeListTask, decodeIntTask_result]

 def splitTask : ℕ → List ℕ → FinTask (List ℕ × List ℕ)
  | 0, xs => .done ([],xs)
  | _+1, [] => .done ([],[])
  | n+1, x::xs => .step fun _ => do
    let (ys,zs) ← splitTask n xs
    .step fun _ => .done (x::ys,zs)

 theorem splitTask_result (n : ℕ) (xs : List ℕ) :
    (splitTask n xs).result = (xs.take n,xs.drop n) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp_all [splitTask, FinTask.result_bindM]

 def parseRatTask (a d : ℕ) : FinTask (Option ℚ) :=
  .step fun _ => if 0<d then do
    let z ← decodeIntTask a
    let num ← FinTask.step fun _ => .done (z : ℚ)
    let den ← FinTask.step fun _ => .done (d : ℚ)
    let q ← FinTask.step fun _ => .done (num/den)
    let hn ← FinTask.step fun _ => .done (decide (q.num=z))
    let hd ← FinTask.step fun _ => .done (decide (q.den=d))
    .done (if hn && hd then some q else none)
  else .done none

 theorem parseRatTask_result (a d : ℕ) : (parseRatTask a d).result = parseRat a d := by
  by_cases h : 0<d <;> simp [parseRatTask, parseRat, h, decodeIntTask_result, Bool.and_eq_true]

 def serializeCoeffsTask (p : IntPolynomial.Coeffs) : FinTask IntPolynomial.Coeffs := do
  let ts ← IntPolynomial.trimTask p
  .step fun _ => .done (if ts=[] then [0] else ts)

 theorem serializeCoeffsTask_result (p : IntPolynomial.Coeffs) :
    (serializeCoeffsTask p).result = IntPolynomial.serializeCoeffs p := by
  simp [serializeCoeffsTask, IntPolynomial.trimTask_result, IntPolynomial.serializeCoeffs]

 def parseCoeffsTask (raw : IntPolynomial.Coeffs) : FinTask (Option IntPolynomial.Coeffs) := do
  let zero ← IntPolynomial.equalTask raw [0]
  .step fun _ => if zero then .done (some []) else
    if raw=[] then .done none else do
      let ts ← IntPolynomial.trimTask raw
      let eq ← IntPolynomial.equalTask ts raw
      .done (if eq then some raw else none)

 theorem parseCoeffsTask_result (raw : IntPolynomial.Coeffs) :
    (parseCoeffsTask raw).result = IntPolynomial.parseCoeffs raw := by
  by_cases h0 : raw=[0] <;> by_cases he : raw=[] <;>
    simp [parseCoeffsTask, IntPolynomial.equalTask_result, IntPolynomial.trimTask_result,
      IntPolynomial.parseCoeffs, IntPolynomial.canonical, h0, he]

 def serializeTask (c : AlgCode) : FinTask (List ℕ) :=
  .step fun _ => match c with
  | .rat q => do
    let a ← encodeIntTask q.num
    .done [0,a,q.den]
  | .root p I => do
    let cs ← serializeCoeffsTask p
    let n ← IntPolynomial.lengthTask cs
    let ts ← encodeListTask cs
    let la ← encodeIntTask I.lower.num
    let ua ← encodeIntTask I.upper.num
    let body ← appendTask ts [la,I.lower.den,ua,I.upper.den]
    .done (1::n::body)

 theorem serializeTask_result (c : AlgCode) : (serializeTask c).result = serialize c := by
  cases c <;> simp [serializeTask, serializeCoeffsTask_result, IntPolynomial.lengthTask_result,
    encodeListTask_result, encodeIntTask_result, appendTask_result, serialize]

 def parseRootTask (n : ℕ) (tokens : List ℕ) : FinTask (Option AlgCode) := do
  let len ← natLengthTask tokens
  .step fun _ => if n≤len then do
    let (pre,suf) ← splitTask n tokens
    let raw ← decodeListTask pre
    let poly ← parseCoeffsTask raw
    match poly with
    | none => .done none
    | some p => .step fun _ => match suf with
      | [la,ld,ua,ud] => do
        let l ← parseRatTask la ld
        match l with
        | none => .done none
        | some l => do
          let u ← parseRatTask ua ud
          .done (u.map fun u => AlgCode.root p ⟨l,u⟩)
      | _ => .done none
  else .done none

 theorem parseRootTask_result (n : ℕ) (tokens : List ℕ) :
    (parseRootTask n tokens).result =
      (if n≤tokens.length then do
        let p ← IntPolynomial.parseCoeffs ((tokens.take n).map decodeInt)
        match tokens.drop n with
        | [la,ld,ua,ud] => do
          let l ← parseRat la ld
          let u ← parseRat ua ud
          return AlgCode.root p ⟨l,u⟩
        | _ => none
      else none) := by
  simp only [parseRootTask, FinTask.result_bindM, natLengthTask_result, FinTask.result_step]
  split_ifs
  · simp only [FinTask.result_bindM, splitTask_result, decodeListTask_result, parseCoeffsTask_result]
    cases hp : IntPolynomial.parseCoeffs ((tokens.take n).map decodeInt) with
    | none => simp [hp]
    | some p =>
      simp only [hp]
      split
      · rename_i la ld ua ud htail
        simp only [FinTask.result_step, FinTask.result_bindM, parseRatTask_result, FinTask.result_done]
        cases hl : parseRat la ld with
        | none => simp [hp, htail, hl]
        | some l =>
          cases hu : parseRat ua ud <;> simp [hp, htail, hl, hu, parseRatTask_result]
      · simp_all
  · rfl

 def parseTask (raw : List ℕ) : FinTask (Option AlgCode) :=
  .step fun _ => match raw with
  | [0,a,d] => do
    let q ← parseRatTask a d
    .done (q.map AlgCode.rat)
  | 1::n::tokens => parseRootTask n tokens
  | _ => .done none

 theorem parseTask_result (raw : List ℕ) : (parseTask raw).result = parse raw := by
  simp only [parseTask, FinTask.result_step, parse]
  split <;> simp_all [parseRatTask_result, parseRootTask_result] <;> rfl

 def parseCanonicalTask (raw : List ℕ) : FinTask (Option AlgCode) := do
  let candidate ← parseTask raw
  match candidate with
  | none => .done none
  | some c => do
    let bytes ← serializeTask c
    let eq ← natEqualTask bytes raw
    .done (if eq then some c else none)

 theorem parseCanonicalTask_result (raw : List ℕ) :
    (parseCanonicalTask raw).result = parseCanonical raw := by
  simp only [parseCanonicalTask, FinTask.result_bindM, parseTask_result, parseCanonical]
  split <;> simp_all [serializeTask_result, natEqualTask_result]

end Cover.AlgCodec
namespace Cover.AlgCode

 def refinementEvidenceTask (original candidate : AlgCode) : FinTask Bool :=
  .step fun _ => match original,candidate with
  | .rat q, .rat q' => .step fun _ => .done (decide (q=q'))
  | .rat _, .root _ _ => .done false
  | .root p I, .rat q => do
    let left ← FinTask.step fun _ => .done (decide (I.lower<q))
    let right ← FinTask.step fun _ => .done (decide (q<I.upper))
    let v ← IntPolynomial.hornerTask p q
    let root ← FinTask.step fun _ => .done (decide (v=0))
    .done (left && right && root)
  | .root p I, .root p' J => do
    let same ← IntPolynomial.equalTask p' p
    let left ← FinTask.step fun _ => .done (decide (I.lower≤J.lower))
    let right ← FinTask.step fun _ => .done (decide (J.upper≤I.upper))
    let ordered ← FinTask.step fun _ => .done (decide (J.lower<J.upper))
    let l ← IntPolynomial.hornerTask p J.lower
    let u ← IntPolynomial.hornerTask p J.upper
    let prod ← FinTask.step fun _ => .done (l*u)
    let changes ← FinTask.step fun _ => .done (decide (prod<0))
    .done (same && (left && right) && ordered && changes)

 theorem refinementEvidenceTask_result (original candidate : AlgCode) :
    (refinementEvidenceTask original candidate).result = decide (refinementEvidence original candidate) := by
  cases original <;> cases candidate <;> simp [refinementEvidenceTask, refinementEvidence,
    IntPolynomial.hornerTask_result, IntPolynomial.equalTask_result, QInterval.subset, Bool.and_assoc] <;> rfl

 def verifyRefinementTask (original candidate : AlgCode) (h : ℚ) (positive : Bool) : FinTask Bool := do
  let valid ← validateAlgTask original
  let evidence ← refinementEvidenceTask original candidate
  let width ← FinTask.step fun _ => .done (candidate.interval.upper-candidate.interval.lower)
  let precise ← FinTask.step fun _ => .done (decide (width≤h))
  let pos ← FinTask.step fun _ => .done (decide (0<candidate.interval.lower))
  .done (valid && evidence && precise && (!positive || pos))

 theorem verifyRefinementTask_result (original candidate : AlgCode) (h : ℚ) (positive : Bool) :
    (verifyRefinementTask original candidate h positive).result = verifyRefinement original candidate h positive := by
  cases positive <;> simp [verifyRefinementTask, validateAlgTask_result, refinementEvidenceTask_result,
    verifyRefinement, validate, QInterval.width, Bool.and_assoc]

 theorem verifyRefinementTask_run_sound {original candidate : AlgCode} {h : ℚ} {positive : Bool}
    {fuel : ℕ} {x : ℝ} (hx : original.denotes x)
    (hr : FinTask.run fuel (verifyRefinementTask original candidate h positive) = some true) :
    original.valid ∧ candidate.valid ∧ candidate.denotes x ∧ candidate.interval.width≤h ∧
      (positive=true → 0<candidate.interval.lower) := by
  have hv := FinTask.run_sound fuel _ _ hr
  rw [verifyRefinementTask_result] at hv
  exact verifyRefinement_sound hx hv

end Cover.AlgCode
