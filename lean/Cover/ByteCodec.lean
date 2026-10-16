import Cover.EvidenceCertificate

namespace Cover
namespace Bytes

abbrev Byte := UInt8
abbrev Stream := List Byte

/-- Canonical self-delimiting unary byte encoding. This intentionally simple codec
    has no compactness or bit-allocation claim: n is n bytes of value 1 followed by 0. -/
def encodeNat (n : Nat) : Stream := List.replicate n 1 ++ [0]

def decodeNat : Stream → Option (Nat × Stream)
  | [] => none
  | b::bs => if b = 0 then some (0, bs)
      else if b = 1 then do
        let (n, rest) ← decodeNat bs
        some (n+1, rest)
      else none

theorem decodeNat_encodeNat (n : Nat) (rest : Stream) :
    decodeNat (encodeNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [encodeNat, decodeNat]
  | succ n ih =>
    simp only [encodeNat, List.replicate_succ, List.cons_append, List.append_assoc, decodeNat]
    norm_num
    simp [encodeNat] at ih
    rw [ih]
    rfl

theorem decodeNat_sound (bytes : Stream) (n : Nat) (rest : Stream)
    (h : decodeNat bytes = some (n, rest)) : encodeNat n ++ rest = bytes := by
  induction bytes generalizing n rest with
  | nil => contradiction
  | cons b bs ih =>
    unfold decodeNat at h
    split at h
    · rename_i hb
      subst b
      cases h
      simp [encodeNat]
    · split at h
      · rename_i hb
        subst b
        cases hd : decodeNat bs with
        | none => simp [hd] at h
        | some pair =>
          rcases pair with ⟨m, tail⟩
          rw [hd] at h
          dsimp only [Bind.bind, Option.bind] at h
          cases h
          have he := ih m rest hd
          simpa [encodeNat, List.replicate_succ, List.append_assoc] using congrArg (List.cons (1:Byte)) he
      · contradiction

/-- Decode an exact finite number of elements. Every accepted element decoder
    returns the remaining suffix, so no length claim is trusted as a parse result. -/
def decodeMany (decode : Stream → Option (α × Stream)) : Nat → Stream → Option (List α × Stream)
  | 0, bytes => some ([], bytes)
  | n+1, bytes => do
      let (x, rest) ← decode bytes
      let (xs, rest) ← decodeMany decode n rest
      some (x::xs, rest)

def encodeList (encode : α → Stream) (xs : List α) : Stream :=
  encodeNat xs.length ++ xs.flatMap encode

def decodeList (decode : Stream → Option (α × Stream)) (bytes : Stream) : Option (List α × Stream) := do
  let (n, rest) ← decodeNat bytes
  decodeMany decode n rest

theorem decodeMany_encode (encode : α → Stream) (decode : Stream → Option (α × Stream))
    (hcodec : ∀ x rest, decode (encode x ++ rest) = some (x, rest))
    (xs : List α) (rest : Stream) :
    decodeMany decode xs.length (xs.flatMap encode ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeMany, hcodec]
    dsimp only [Bind.bind, Option.bind]
    rw [ih]

theorem decodeList_encode (encode : α → Stream) (decode : Stream → Option (α × Stream))
    (hcodec : ∀ x rest, decode (encode x ++ rest) = some (x, rest))
    (xs : List α) (rest : Stream) :
    decodeList decode (encodeList encode xs ++ rest) = some (xs, rest) := by
  simp only [encodeList, List.append_assoc, decodeList, decodeNat_encodeNat]
  dsimp only [Bind.bind, Option.bind]
  exact decodeMany_encode encode decode hcodec xs rest

theorem decodeMany_sound (encode : α → Stream) (decode : Stream → Option (α × Stream))
    (hcodec : ∀ bytes x rest, decode bytes = some (x, rest) → encode x ++ rest = bytes)
    (len : Nat) (bytes : Stream) (xs : List α) (rest : Stream)
    (h : decodeMany decode len bytes = some (xs, rest)) :
    xs.length = len ∧ xs.flatMap encode ++ rest = bytes := by
  induction len generalizing bytes xs rest with
  | zero => cases h; exact ⟨rfl, rfl⟩
  | succ len ih =>
    simp only [decodeMany] at h
    cases hd : decode bytes with
    | none => simp [hd] at h
    | some pair =>
      rcases pair with ⟨x, middle⟩
      rw [hd] at h
      dsimp only [Bind.bind, Option.bind] at h
      cases hs : decodeMany decode len middle with
      | none => simp [hs] at h
      | some pair =>
        rcases pair with ⟨tail, final⟩
        rw [hs] at h
        dsimp only [Bind.bind, Option.bind] at h
        cases h
        obtain ⟨hlen, htail⟩ := ih middle tail rest hs
        refine ⟨by simp [hlen], ?_⟩
        simpa only [List.flatMap_cons, List.append_assoc, htail] using hcodec bytes x middle hd

theorem decodeList_sound (encode : α → Stream) (decode : Stream → Option (α × Stream))
    (hcodec : ∀ bytes x rest, decode bytes = some (x, rest) → encode x ++ rest = bytes)
    (bytes : Stream) (xs : List α) (rest : Stream)
    (h : decodeList decode bytes = some (xs, rest)) : encodeList encode xs ++ rest = bytes := by
  unfold decodeList at h
  cases hn : decodeNat bytes with
  | none => simp [hn] at h
  | some pair =>
    rcases pair with ⟨len, middle⟩
    rw [hn] at h
    dsimp only [Bind.bind, Option.bind] at h
    obtain ⟨hlen, htail⟩ := decodeMany_sound encode decode hcodec len middle xs rest h
    have hhead := decodeNat_sound bytes len middle hn
    simp only [encodeList, List.append_assoc, hlen, htail]
    exact hhead

def encodeNats := encodeList encodeNat
def decodeNats := decodeList decodeNat

theorem decodeNats_encodeNats (xs : List Nat) (rest : Stream) :
    decodeNats (encodeNats xs ++ rest) = some (xs, rest) :=
  decodeList_encode encodeNat decodeNat decodeNat_encodeNat xs rest

theorem decodeNats_sound (bytes : Stream) (xs : List Nat) (rest : Stream)
    (h : decodeNats bytes = some (xs, rest)) : encodeNats xs ++ rest = bytes :=
  decodeList_sound encodeNat decodeNat decodeNat_sound bytes xs rest h


/-- Lift a canonical finite natural-field format into actual bytes. -/
def encodeFields (fields : α → List Nat) (x : α) : Stream := encodeNats (fields x)
def decodeFields (parse : List Nat → Option α) (bytes : Stream) : Option (α × Stream) := do
  let (fields, rest) ← decodeNats bytes
  let x ← parse fields
  some (x, rest)

theorem decodeFields_encode (fields : α → List Nat) (parse : List Nat → Option α)
    (hcodec : ∀ x, parse (fields x) = some x) (x : α) (rest : Stream) :
    decodeFields parse (encodeFields fields x ++ rest) = some (x, rest) := by
  simp [decodeFields, encodeFields, decodeNats_encodeNats, hcodec]

theorem decodeFields_sound (fields : α → List Nat) (parse : List Nat → Option α)
    (hcodec : ∀ fs x, parse fs = some x → fields x = fs)
    (bytes : Stream) (x : α) (rest : Stream)
    (h : decodeFields parse bytes = some (x, rest)) : encodeFields fields x ++ rest = bytes := by
  unfold decodeFields at h
  cases hd : decodeNats bytes with
  | none => simp [hd] at h
  | some pair =>
    rcases pair with ⟨fs, tail⟩
    rw [hd] at h
    dsimp only [Bind.bind, Option.bind] at h
    cases hp : parse fs with
    | none => simp [hp] at h
    | some y =>
      rw [hp] at h
      dsimp only [Bind.bind, Option.bind] at h
      cases h
      simpa [encodeFields, hcodec fs x hp] using decodeNats_sound bytes fs rest hd

def coverFields : CoverToken → List Nat
  | .header fmt gen k prec input => 0 :: fmt :: gen :: k :: prec :: input
  | .gap => [1]
  | .exclude i => [2, i]
  | .split i => [3, i]
  | .unknown tag => [4, tag]

def parseCoverFields : List Nat → Option CoverToken
  | 0 :: fmt :: gen :: k :: prec :: input => some (.header fmt gen k prec input)
  | [1] => some .gap
  | [2, i] => some (.exclude i)
  | [3, i] => some (.split i)
  | [4, tag] => some (.unknown tag)
  | _ => none

theorem parseCoverFields_encode (token : CoverToken) : parseCoverFields (coverFields token) = some token := by
  cases token <;> rfl

theorem parseCoverFields_sound (fields : List Nat) (token : CoverToken)
    (h : parseCoverFields fields = some token) : coverFields token = fields := by
  unfold parseCoverFields at h
  split at h <;> cases h <;> rfl

def evidenceFields : EvidenceToken → List Nat
  | .refinements weight sigma => 0 :: weight.length :: (weight ++ sigma)
  | .base token => 1 :: coverFields token
  | .unknown tag => [2, tag]

def parseEvidenceFields : List Nat → Option EvidenceToken
  | 0 :: len :: rest => if len ≤ rest.length then some (.refinements (rest.take len) (rest.drop len)) else none
  | 1 :: rest => (parseCoverFields rest).map .base
  | [2, tag] => some (.unknown tag)
  | _ => none

theorem parseEvidenceFields_encode (token : EvidenceToken) :
    parseEvidenceFields (evidenceFields token) = some token := by
  cases token with
  | refinements weight sigma => simp [evidenceFields, parseEvidenceFields]
  | base token => simp [evidenceFields, parseEvidenceFields, parseCoverFields_encode]
  | unknown tag => rfl

theorem parseEvidenceFields_sound (fields : List Nat) (token : EvidenceToken)
    (h : parseEvidenceFields fields = some token) : evidenceFields token = fields := by
  unfold parseEvidenceFields at h
  split at h
  · rename_i len rest
    split at h
    · rename_i hlen
      cases h
      simp [evidenceFields, List.length_take, Nat.min_eq_left hlen]
    · contradiction
  · rename_i rest
    cases hp : parseCoverFields rest with
    | none => simp [hp] at h
    | some t =>
      simp only [hp, Option.map_some, Option.some.injEq] at h
      subst token
      simp [evidenceFields, parseCoverFields_sound rest t hp]
  · cases h; rfl
  · contradiction

def encodeEvidenceToken : EvidenceToken → Stream := encodeFields evidenceFields
def decodeEvidenceToken : Stream → Option (EvidenceToken × Stream) := decodeFields parseEvidenceFields

theorem decodeEvidenceToken_encode (token : EvidenceToken) (rest : Stream) :
    decodeEvidenceToken (encodeEvidenceToken token ++ rest) = some (token, rest) :=
  decodeFields_encode evidenceFields parseEvidenceFields parseEvidenceFields_encode token rest

theorem decodeEvidenceToken_sound (bytes : Stream) (token : EvidenceToken) (rest : Stream)
    (h : decodeEvidenceToken bytes = some (token, rest)) : encodeEvidenceToken token ++ rest = bytes :=
  decodeFields_sound evidenceFields parseEvidenceFields parseEvidenceFields_sound bytes token rest h

/-- A certificate byte stream is a length-prefixed list of tagged evidence tokens.
    Each tag/payload is itself length-framed, and every scalar/design Nat is embedded exactly. -/
def serializeEvidenceBytes (c : EvidenceCertificate n j) : Stream :=
  encodeList encodeEvidenceToken (serializeEvidenceCertificate c)

def parseEvidenceBytes (n j : Nat) (bytes : Stream) : Option (EvidenceCertificate n j) := do
  let (tokens, rest) ← decodeList decodeEvidenceToken bytes
  if rest = [] then parseEvidenceCertificate n j tokens else none

theorem parseEvidenceBytes_serialize (c : EvidenceCertificate n j) :
    parseEvidenceBytes n j (serializeEvidenceBytes c) = some c := by
  have h := decodeList_encode encodeEvidenceToken decodeEvidenceToken decodeEvidenceToken_encode
    (serializeEvidenceCertificate c) []
  simp only [List.append_nil] at h
  simp [parseEvidenceBytes, serializeEvidenceBytes, h, parseEvidenceCertificate_serialize]

/-- Acceptance requires the byte parser to consume the entire original stream. -/
theorem parseEvidenceBytes_consumed (bytes : Stream) (c : EvidenceCertificate n j)
    (h : parseEvidenceBytes n j bytes = some c) :
    ∃ tokens, decodeList decodeEvidenceToken bytes = some (tokens, []) ∧
      parseEvidenceCertificate n j tokens = some c := by
  unfold parseEvidenceBytes at h
  cases hd : decodeList decodeEvidenceToken bytes with
  | none => simp [hd] at h
  | some pair =>
    rcases pair with ⟨tokens, rest⟩
    rw [hd] at h
    dsimp only [Bind.bind, Option.bind] at h
    split at h
    · rename_i hr
      subst rest
      exact ⟨tokens, rfl, h⟩
    · contradiction

/-- Accepted bytes are exactly the canonical serialization of the parsed certificate.
    This excludes unconsumed garbage, alternate framing, and unfinished syntax. -/
theorem parseEvidenceBytes_sound (bytes : Stream) (c : EvidenceCertificate n j)
    (h : parseEvidenceBytes n j bytes = some c) : serializeEvidenceBytes c = bytes := by
  obtain ⟨tokens, hd, hp⟩ := parseEvidenceBytes_consumed bytes c h
  have hs := decodeList_sound encodeEvidenceToken decodeEvidenceToken decodeEvidenceToken_sound bytes tokens [] hd
  have he := parseEvidenceCertificate_sound tokens c hp
  simpa [serializeEvidenceBytes, he] using hs

theorem parseEvidenceBytes_iff (bytes : Stream) (c : EvidenceCertificate n j) :
    parseEvidenceBytes n j bytes = some c ↔ serializeEvidenceBytes c = bytes := by
  constructor
  · exact parseEvidenceBytes_sound bytes c
  · intro h
    rw [← h]
    exact parseEvidenceBytes_serialize c


theorem decode_serialized_suffix (c : EvidenceCertificate n j) (tail : Stream) :
    decodeList decodeEvidenceToken (serializeEvidenceBytes c ++ tail) =
      some (serializeEvidenceCertificate c, tail) :=
  decodeList_encode encodeEvidenceToken decodeEvidenceToken decodeEvidenceToken_encode
    (serializeEvidenceCertificate c) tail

theorem parseEvidenceBytes_trailing_rejected (c : EvidenceCertificate n j) (tail : Stream)
    (h : tail ≠ []) : parseEvidenceBytes n j (serializeEvidenceBytes c ++ tail) = none := by
  simp [parseEvidenceBytes, decode_serialized_suffix, h]

theorem serializeEvidenceBytes_prefix_free (c d : EvidenceCertificate n j) (tail : Stream)
    (h : serializeEvidenceBytes c ++ tail = serializeEvidenceBytes d) : tail = [] ∧ c = d := by
  have hc := decode_serialized_suffix c tail
  have hd := decode_serialized_suffix d []
  simp only [List.append_nil] at hd
  rw [h, hd] at hc
  have he := Option.some.inj hc
  have htail : tail = [] := (congrArg Prod.snd he).symm
  subst tail
  simp only [List.append_nil] at h
  have hp := parseEvidenceBytes_serialize c
  rw [h, parseEvidenceBytes_serialize] at hp
  exact ⟨rfl, (Option.some.inj hp).symm⟩

/-- Any genuine truncation of a serialized certificate is rejected, even if the
    cut occurs in a natural, a length prefix, a field list, or a tree token. -/
theorem parseEvidenceBytes_truncation_rejected (c : EvidenceCertificate n j)
    (front missing : Stream) (hfull : front ++ missing = serializeEvidenceBytes c)
    (hmissing : missing ≠ []) : parseEvidenceBytes n j front = none := by
  cases hp : parseEvidenceBytes n j front with
  | none => rfl
  | some d =>
    have hd := parseEvidenceBytes_sound front d hp
    have hf : serializeEvidenceBytes d ++ missing = serializeEvidenceBytes c := by rw [hd]; exact hfull
    exact False.elim (hmissing (serializeEvidenceBytes_prefix_free d c missing hf).1)

/-- Unknown outer token tags are rejected after ordinary raw-byte decoding. -/
theorem unknown_evidence_tag_rejected (tag : Nat) (htag : 3 ≤ tag) (tail : Stream) :
    decodeEvidenceToken (encodeNats [tag] ++ tail) = none := by
  have h0 : tag ≠ 0 := by omega
  have h1 : tag ≠ 1 := by omega
  have h2 : tag ≠ 2 := by omega
  simp [decodeEvidenceToken, decodeFields, decodeNats_encodeNats, parseEvidenceFields, h0, h1, h2]

/-- Native ByteArray surface: raw byte data is parsed, not trusted as typed tokens. -/
def serializeEvidenceByteArray (c : EvidenceCertificate n j) : ByteArray :=
  ⟨(serializeEvidenceBytes c).toArray⟩

def parseEvidenceByteArray (n j : Nat) (bytes : ByteArray) : Option (EvidenceCertificate n j) :=
  parseEvidenceBytes n j bytes.data.toList

theorem parseEvidenceByteArray_serialize (c : EvidenceCertificate n j) :
    parseEvidenceByteArray n j (serializeEvidenceByteArray c) = some c := by
  simpa [parseEvidenceByteArray, serializeEvidenceByteArray] using parseEvidenceBytes_serialize c

theorem parseEvidenceByteArray_consumed (bytes : ByteArray) (c : EvidenceCertificate n j)
    (h : parseEvidenceByteArray n j bytes = some c) :
    ∃ tokens, decodeList decodeEvidenceToken bytes.data.toList = some (tokens, []) ∧
      parseEvidenceCertificate n j tokens = some c :=
  parseEvidenceBytes_consumed bytes.data.toList c h

end Bytes
end Cover
