import Cover.AlgebraicRegression

namespace Cover.AlgCodec

/-- Even tokens encode nonnegative integers; odd tokens encode negative successors. -/
def encodeInt : ℤ → ℕ
  | .ofNat n => 2*n
  | .negSucc n => 2*n+1

def decodeInt (n : ℕ) : ℤ :=
  if n % 2 = 0 then .ofNat (n/2) else .negSucc (n/2)

 theorem decode_encodeInt (z : ℤ) : decodeInt (encodeInt z) = z := by
  cases z with
  | ofNat n => simp [encodeInt, decodeInt]
  | negSucc n => simp [encodeInt, decodeInt, Nat.add_div]

 theorem encode_decodeInt (n : ℕ) : encodeInt (decodeInt n) = n := by
  unfold decodeInt
  split_ifs with h
  · simp only [encodeInt]; omega
  · simp only [encodeInt]; omega

/-- Positive reduced denominator and canonical numerator are rechecked exactly. -/
def parseRat (a d : ℕ) : Option ℚ :=
  if 0 < d then
    let q : ℚ := (decodeInt a : ℚ)/(d : ℚ)
    if q.num = decodeInt a ∧ q.den = d then some q else none
  else none

 theorem parseRat_roundtrip (q : ℚ) : parseRat (encodeInt q.num) q.den = some q := by
  simp [parseRat, decode_encodeInt, q.den_pos, Rat.num_div_den]

 theorem parseRat_canonical {a d : ℕ} {q : ℚ} (h : parseRat a d = some q) :
    0 < d ∧ encodeInt q.num = a ∧ q.den = d := by
  by_cases hd : 0 < d
  · simp only [parseRat, if_pos hd] at h
    split_ifs at h with hc
    cases h
    exact ⟨hd, by rw [hc.1, encode_decodeInt], hc.2⟩
  · simp [parseRat, hd] at h

 theorem parseRat_zero_den (a : ℕ) : parseRat a 0 = none := by simp [parseRat]

/-- Natural-token scalar format 1: tag 0 for Rat, tag 1 then polynomial length for Root. -/
def serialize : AlgCode → List ℕ
  | .rat q => [0, encodeInt q.num, q.den]
  | .root p I =>
    let cs := IntPolynomial.serializeCoeffs p
    [1, cs.length] ++ cs.map encodeInt ++
      [encodeInt I.lower.num, I.lower.den, encodeInt I.upper.num, I.upper.den]

def parse : List ℕ → Option AlgCode
  | [0, a, d] => (parseRat a d).map AlgCode.rat
  | 1 :: n :: tokens =>
    if n ≤ tokens.length then do
      let p ← IntPolynomial.parseCoeffs ((tokens.take n).map decodeInt)
      match tokens.drop n with
      | [la, ld, ua, ud] =>
        let l ← parseRat la ld
        let u ← parseRat ua ud
        return AlgCode.root p ⟨l,u⟩
      | _ => none
    else none
  | _ => none

def normalize : AlgCode → AlgCode
  | .rat q => .rat q
  | .root p I => .root (IntPolynomial.trim p) I

 theorem parse_serialize (c : AlgCode) : parse (serialize c) = some (normalize c) := by
  cases c with
  | rat q => simp [serialize, parse, parseRat_roundtrip, normalize]
  | root p I =>
    simp only [serialize, List.cons_append, List.nil_append]
    simp only [parse]
    have hlen : (IntPolynomial.serializeCoeffs p).length ≤
        ((IntPolynomial.serializeCoeffs p).map encodeInt ++
          [encodeInt I.lower.num, I.lower.den, encodeInt I.upper.num, I.upper.den]).length := by
      simp
    rw [if_pos hlen]
    have htake : List.take (IntPolynomial.serializeCoeffs p).length
        ((IntPolynomial.serializeCoeffs p).map encodeInt ++
          [encodeInt I.lower.num, I.lower.den, encodeInt I.upper.num, I.upper.den]) =
          (IntPolynomial.serializeCoeffs p).map encodeInt := by
      simpa only [List.length_map] using
        (List.take_left (l₁ := (IntPolynomial.serializeCoeffs p).map encodeInt)
          (l₂ := [encodeInt I.lower.num, I.lower.den, encodeInt I.upper.num, I.upper.den]))
    have hdrop : List.drop (IntPolynomial.serializeCoeffs p).length
        ((IntPolynomial.serializeCoeffs p).map encodeInt ++
          [encodeInt I.lower.num, I.lower.den, encodeInt I.upper.num, I.upper.den]) =
          [encodeInt I.lower.num, I.lower.den, encodeInt I.upper.num, I.upper.den] := by
      simpa only [List.length_map] using
        (List.drop_left (l₁ := (IntPolynomial.serializeCoeffs p).map encodeInt)
          (l₂ := [encodeInt I.lower.num, I.lower.den, encodeInt I.upper.num, I.upper.den]))
    rw [htake, hdrop]
    simp [List.map_map, Function.comp_def, decode_encodeInt, IntPolynomial.parse_serialize,
      parseRat_roundtrip, normalize]

 theorem parse_serialize_valid {c : AlgCode} (h : c.valid) : parse (serialize c) = some c := by
  rw [parse_serialize]
  cases c with
  | rat q => rfl
  | root p I =>
    have ht : IntPolynomial.trim p = p := h.1
    simp only [normalize, ht]

 theorem parse_nil : parse [] = none := rfl
 theorem parse_bad_tag (n : ℕ) (h0 : n ≠ 0) (h1 : n ≠ 1) (rest : List ℕ) :
    parse (n :: rest) = none := by
  cases n with
  | zero => contradiction
  | succ n => cases n with
    | zero => contradiction
    | succ n => rfl

/-- Canonical-byte acceptance additionally requires an exact serializer replay. -/
def parseCanonical (raw : List ℕ) : Option AlgCode := do
  let c ← parse raw
  if serialize c = raw then some c else none

 theorem parseCanonical_roundtrip {c : AlgCode} (hc : c.valid) :
    parseCanonical (serialize c) = some c := by
  simp [parseCanonical, parse_serialize_valid hc]

 theorem parseCanonical_sound {raw : List ℕ} {c : AlgCode}
    (h : parseCanonical raw = some c) : parse raw = some c ∧ serialize c = raw := by
  unfold parseCanonical at h
  cases hp : parse raw with
  | none => simp [hp] at h
  | some a =>
    rw [hp] at h
    change (if serialize a = raw then some a else none) = some c at h
    split_ifs at h with ha
    cases h
    exact ⟨rfl, ha⟩

 theorem parseCanonical_injective {raw₁ raw₂ : List ℕ} {c : AlgCode}
    (h₁ : parseCanonical raw₁ = some c) (h₂ : parseCanonical raw₂ = some c) : raw₁ = raw₂ :=
  (parseCanonical_sound h₁).2.symm.trans (parseCanonical_sound h₂).2

end Cover.AlgCodec
