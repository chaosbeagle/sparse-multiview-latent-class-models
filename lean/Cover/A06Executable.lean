import Cover.A06Certificate
import Cover.ByteCodec

namespace Cover.A06

def serializeInputBytes (I : Input) : ByteArray :=
  ⟨(Bytes.encodeList Bytes.encodeNat (A06InputCodec.serialize I)).toArray⟩

def parseInputBytes (raw : ByteArray) : Option Input := do
  let (tokens,rest) ← Bytes.decodeList Bytes.decodeNat raw.data.toList
  if rest = [] then A06InputCodec.parse tokens else none

theorem parseInputBytes_roundtrip (I : Input) (h : Valid I) :
    parseInputBytes (serializeInputBytes I) = some I := by
  have hh := Bytes.decodeList_encode Bytes.encodeNat Bytes.decodeNat Bytes.decodeNat_encodeNat
    (A06InputCodec.serialize I) []
  simp only [List.append_nil] at hh
  simp [parseInputBytes,serializeInputBytes,hh,A06InputCodec.parse_serialize I h]

theorem parseInputBytes_valid {raw : ByteArray} {I : Input} (hp : parseInputBytes raw = some I) : Valid I := by
  unfold parseInputBytes at hp
  cases hd : Bytes.decodeList Bytes.decodeNat raw.data.toList with
  | none => simp [hd] at hp
  | some pair =>
    rcases pair with ⟨tokens,rest⟩
    simp only [hd,Bind.bind,Option.bind] at hp
    split at hp
    · exact A06InputCodec.parse_valid hp
    · contradiction

/-- Raw input parsing preserves the entire canonical byte vector. -/
theorem parseInputBytes_exact {raw : ByteArray} {I : Input} (hp : parseInputBytes raw = some I) :
    serializeInputBytes I = raw := by
  unfold parseInputBytes at hp
  cases hd : Bytes.decodeList Bytes.decodeNat raw.data.toList with
  | none => simp [hd] at hp
  | some pair =>
    rcases pair with ⟨tokens,rest⟩
    simp only [hd,Bind.bind,Option.bind] at hp
    split at hp
    · rename_i hrest
      subst rest
      have he := Bytes.decodeList_sound Bytes.encodeNat Bytes.decodeNat Bytes.decodeNat_sound
        raw.data.toList tokens [] hd
      have ht := (A06InputCodec.parse_sound hp).2
      simp only [List.append_nil] at he
      apply ByteArray.ext
      simp only [serializeInputBytes]
      rw [ht, he]
    · contradiction

def verifyCertificateBytes (I : Input) (h : Valid I) (raw : ByteArray) : Bool :=
  match Bytes.parseEvidenceByteArray (pairDimension I h) (constraintCount I h) raw with
  | none => false
  | some c => verifyCertificate I h c

theorem verifyCertificateBytes_sound (I : Input) (h : Valid I) (raw : ByteArray)
    (hv : verifyCertificateBytes I h raw = true) :
    ∃ c : Certificate I h,
      Bytes.parseEvidenceByteArray (pairDimension I h) (constraintCount I h) raw = some c ∧
      verifyCertificate I h c = true := by
  unfold verifyCertificateBytes at hv
  split at hv
  · contradiction
  · exact ⟨_,by assumption,hv⟩

/-- Every byte, including both root refinements, is serialized before return. -/
def computedCertificateBytes (I : Input) (h : Valid I) : ByteArray :=
  Bytes.serializeEvidenceByteArray (computedCertificate I h)

theorem computedCertificateBytes_verified (I : Input) (h : Valid I) :
    verifyCertificateBytes I h (computedCertificateBytes I h) = true := by
  simp [verifyCertificateBytes,computedCertificateBytes,
    Bytes.parseEvidenceByteArray_serialize,computedCertificate_verified]

inductive UnboundedOutcome where
  | invalidInput
  | implementationError
  | certificate : ByteArray → UnboundedOutcome

/-- The complete unbounded executable: finite byte parsing/validation, actual
rational stage enumeration, original-polynomial evidence, and a fully serialized
certificate. No real input, gap oracle, minimizer or certificate choice appears. -/
def runCover (raw : ByteArray) : UnboundedOutcome :=
  match hp : parseInputBytes raw with
  | none => .invalidInput
  | some I =>
    let h := parseInputBytes_valid hp
    let bytes := computedCertificateBytes I h
    if verifyCertificateBytes I h bytes then .certificate bytes else .implementationError

theorem runCover_completes_admitted (I : Input) (h : Valid I) :
    runCover (serializeInputBytes I) = .certificate (computedCertificateBytes I h) := by
  unfold runCover
  split
  · rename_i hn
    rw [parseInputBytes_roundtrip I h] at hn
    contradiction
  · rename_i J hp
    have he : I = J := Option.some.inj ((parseInputBytes_roundtrip I h).symm.trans hp)
    subst J
    simp [computedCertificateBytes_verified]

theorem runCover_success_fully_checked (raw bytes : ByteArray)
    (hr : runCover raw = .certificate bytes) :
    ∃ I : Input, ∃ h : Valid I,
      parseInputBytes raw = some I ∧ serializeInputBytes I = raw ∧
      verifyCertificateBytes I h bytes = true := by
  unfold runCover at hr
  split at hr
  · contradiction
  · rename_i I hp
    dsimp only at hr
    split at hr
    · cases hr
      exact ⟨I,parseInputBytes_valid hp,hp,parseInputBytes_exact hp,computedCertificateBytes_verified I _⟩
    · contradiction

/-- Standalone untrusted-byte verification, independent of the generator/search. -/
def verifyRawCertificate (inputBytes certificateBytes : ByteArray) : Bool :=
  match hp : parseInputBytes inputBytes with
  | none => false
  | some I => verifyCertificateBytes I (parseInputBytes_valid hp) certificateBytes

theorem verifyRawCertificate_sound (inputBytes certificateBytes : ByteArray)
    (hc : verifyRawCertificate inputBytes certificateBytes = true) :
    ∃ I : Input, ∃ h : Valid I, parseInputBytes inputBytes = some I ∧
      serializeInputBytes I = inputBytes ∧ verifyCertificateBytes I h certificateBytes = true := by
  unfold verifyRawCertificate at hc
  split at hc
  · contradiction
  · rename_i I hp
    exact ⟨I,parseInputBytes_valid hp,hp,parseInputBytes_exact hp,hc⟩

end Cover.A06
