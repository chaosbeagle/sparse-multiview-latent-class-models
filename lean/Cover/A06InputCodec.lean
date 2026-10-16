import Cover.A06Input
import Cover.DesignCodecSoundness
import Cover.AlgebraicCodec

namespace Cover.A06InputCodec
open Cover.A06 Cover.DesignCodec

/-- Exact versioned input binding, using three count-framed finite token vectors. -/
def serialize (I : Input) : List ℕ :=
  1 :: (writeBlock (DesignCodec.serialize I.design) ++
    writeBlock (AlgCodec.serialize I.weight) ++ writeBlock (AlgCodec.serialize I.sigma))

/-- Frame parsing preserves payload boundaries and rejects all trailing tokens. -/
def readFrames : List ℕ → Option (List ℕ × List ℕ × List ℕ)
  | 1 :: xs => match readBlock xs with
    | none => none
    | some (design,rest) => match readBlock rest with
      | none => none
      | some (weight,tail) => match readBlock tail with
        | none => none
        | some (sigma,[]) => some (design,weight,sigma)
        | some (_, _ :: _) => none
  | _ => none

theorem readFrames_serialize (I : Input) :
    readFrames (serialize I) = some (DesignCodec.serialize I.design,
      AlgCodec.serialize I.weight,AlgCodec.serialize I.sigma) := by
  simp only [serialize,List.append_assoc,readFrames,readBlock_writeBlock]
  have hs := readBlock_writeBlock (AlgCodec.serialize I.sigma) []
  simp only [List.append_nil] at hs
  rw [hs]

/-- Codes are parsed canonically; neither root polynomials nor rational spellings are silently changed. -/
def parseParts (d w s : List ℕ) : Option Input :=
  match DesignCodec.parse d with
  | none => none
  | some design => match AlgCodec.parseCanonical w with
    | none => none
    | some weight => match AlgCodec.parseCanonical s with
      | none => none
      | some sigma => some ⟨design,weight,sigma⟩

theorem parseParts_serialize (I : Input) (h : Valid I) :
    parseParts (DesignCodec.serialize I.design) (AlgCodec.serialize I.weight)
      (AlgCodec.serialize I.sigma) = some I := by
  unfold parseParts
  rw [DesignCodec.parse_serialize I.design h.1,
    AlgCodec.parseCanonical_roundtrip (Margins.valid_codes h.2).1,
    AlgCodec.parseCanonical_roundtrip (Margins.valid_codes h.2).2]

def parseRaw (raw : List ℕ) : Option Input :=
  match readFrames raw with
  | none => none
  | some (d,w,s) => parseParts d w s

/-- Completed exact validation and byte-for-byte serializer replay are both mandatory. -/
def parse (raw : List ℕ) : Option Input :=
  match parseRaw raw with
  | none => none
  | some I => if Valid I ∧ serialize I = raw then some I else none

theorem parse_serialize (I : Input) (h : Valid I) : parse (serialize I) = some I := by
  simp only [parse,parseRaw,readFrames_serialize,parseParts_serialize I h,
    h,true_and,ite_true]

theorem parse_sound {raw : List ℕ} {I : Input} (hp : parse raw = some I) :
    Valid I ∧ serialize I = raw := by
  unfold parse at hp
  cases hr : parseRaw raw with
  | none => simp only [hr] at hp; cases hp
  | some J =>
    rw [hr] at hp
    change (if Valid J ∧ serialize J = raw then some J else none) = some I at hp
    by_cases hj : Valid J ∧ serialize J = raw
    · rw [if_pos hj] at hp
      cases hp
      exact hj
    · rw [if_neg hj] at hp
      cases hp

theorem serialize_injective_on_valid {I J : Input} (hI : Valid I) (hJ : Valid J)
    (h : serialize I = serialize J) : I = J := by
  have hh := congrArg parse h
  rw [parse_serialize I hI,parse_serialize J hJ] at hh
  exact Option.some.inj hh

/-- Distinct complete token vectors cannot both be accepted as the same input. -/
theorem accepted_tokens_unique {xs ys : List ℕ} {I : Input}
    (hx : parse xs = some I) (hy : parse ys = some I) : xs = ys :=
  (parse_sound hx).2.symm.trans (parse_sound hy).2

/-- A success is always a completed valid input, never an interrupted validation. -/
theorem parse_valid {xs : List ℕ} {I : Input} (h : parse xs = some I) : Valid I :=
  (parse_sound h).1
end Cover.A06InputCodec
