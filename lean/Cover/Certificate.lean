import Cover.Stage

namespace Cover

/-- The exact finite input tokens are embedded, never replaced by an unproved hash. -/
structure CoverCertificate (n j : Nat) where
  formatVersion : Nat
  generatorVersion : Nat
  input : List Nat
  k : Nat
  precision : Nat
  tree : CoverTree n j
  deriving DecidableEq, Repr

/-- This implementation recognizes these two exact version tags. -/
def formatVersion : Nat := 1
def generatorVersion : Nat := 1

def makeCertificate (input : List Nat) (s : Nat) (t : CoverTree n j) : CoverCertificate n j :=
  ⟨formatVersion, generatorVersion, input, s, s, t⟩

/-- The checker recomputes all boxes and interval evaluations from the supplied,
    input-derived compilation and precision-indexed scalar evaluator. No submitted
    box, scalar endpoint, sampled value, or generator success flag is trusted. -/
def verifyCoverCertificate (input : List Nat) (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (cert : CoverCertificate n j) : Bool :=
  decide (cert.input = input ∧ cert.formatVersion = formatVersion ∧
    cert.generatorVersion = generatorVersion) &&
    checkTree (cs cert.precision) gs H cert.k (unitBox n) cert.tree

theorem verifyCoverCertificate_binding (input : List Nat) (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (cert : CoverCertificate n j)
    (h : verifyCoverCertificate input cs gs H cert = true) :
    cert.input = input ∧ cert.formatVersion = formatVersion ∧ cert.generatorVersion = generatorVersion := by
  simp only [verifyCoverCertificate, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

 theorem verifyCoverCertificate_checked (input : List Nat) (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (cert : CoverCertificate n j)
    (h : verifyCoverCertificate input cs gs H cert = true) :
    checkTree (cs cert.precision) gs H cert.k (unitBox n) cert.tree = true := by
  simp only [verifyCoverCertificate, Bool.and_eq_true] at h
  exact h.2

theorem verifyCoverCertificate_sound (input : List Nat) (cs : Nat → Fin a → QInterval)
    (values : Fin a → ℝ) (gs : Fin j → PolyExpr n a) (H : PolyExpr n a)
    (cert : CoverCertificate n j) (hcs : ∀ s i, (cs s i).contains (values i))
    (h : verifyCoverCertificate input cs gs H cert = true)
    (x : Fin n → ℝ) (hx : (unitBox n).Contains x)
    (hfeas : ∀ i, 0 ≤ (gs i).eval values x) :
    (0 < dyadic cert.k) ∧ (dyadic (2*cert.k) : ℝ) ≤ H.eval values x := by
  refine ⟨dyadic_pos _, ?_⟩
  exact verifyCoverTree_sound (cs cert.precision) values gs H cert.k (hcs cert.precision)
    cert.tree (verifyCoverCertificate_checked input cs gs H cert h) x hx hfeas

/-- A finite token format. Unknown tags, invalid indices, missing children,
    repeated/misplaced headers, and trailing tokens are all representable and rejected. -/
inductive CoverToken where
  | header (format generator k precision : Nat) (input : List Nat)
  | gap
  | exclude (index : Nat)
  | split (index : Nat)
  | unknown (tag : Nat)
  deriving DecidableEq, Repr

def serializeTree : CoverTree n j → List CoverToken
  | .leaf .gap => [.gap]
  | .leaf (.exclude i) => [.exclude i.val]
  | .split i l r => .split i.val :: (serializeTree l ++ serializeTree r)

def parseTree (n j : Nat) : Nat → List CoverToken → Option (CoverTree n j × List CoverToken)
  | 0, _ => none
  | fuel+1, .gap :: rest => some (.leaf .gap, rest)
  | fuel+1, .exclude i :: rest => if hi : i < j then some (.leaf (.exclude ⟨i, hi⟩), rest) else none
  | fuel+1, .split i :: rest => if hi : i < n then do
      let (left, rest) ← parseTree n j fuel rest
      let (right, rest) ← parseTree n j fuel rest
      some (.split ⟨i, hi⟩ left right, rest)
    else none
  | _+1, _ => none

theorem parseTree_serialize (t : CoverTree n j) (rest : List CoverToken) (fuel : Nat)
    (hf : t.nodes ≤ fuel) : parseTree n j fuel (serializeTree t ++ rest) = some (t, rest) := by
  induction t generalizing rest fuel with
  | leaf label =>
    cases fuel with
    | zero => simp [CoverTree.nodes] at hf
    | succ fuel => cases label <;> simp [serializeTree, parseTree]
  | split i l r ihl ihr =>
    cases fuel with
    | zero => simp [CoverTree.nodes] at hf
    | succ fuel =>
      have hl : l.nodes ≤ fuel := by simp only [CoverTree.nodes] at hf; omega
      have hr : r.nodes ≤ fuel := by simp only [CoverTree.nodes] at hf; omega
      simp only [serializeTree, List.cons_append, List.append_assoc, parseTree, i.isLt, ↓reduceDIte]
      rw [ihl _ _ hl]
      dsimp only [Bind.bind, Option.bind]
      rw [ihr _ _ hr]

theorem nodes_le_serialized_length (t : CoverTree n j) : t.nodes ≤ (serializeTree t).length := by
  induction t with
  | leaf label => cases label <;> simp [CoverTree.nodes, serializeTree]
  | split i l r ihl ihr => simp only [CoverTree.nodes, serializeTree, List.length_cons, List.length_append]; omega

def serializeCertificate (c : CoverCertificate n j) : List CoverToken :=
  .header c.formatVersion c.generatorVersion c.k c.precision c.input :: serializeTree c.tree

def parseCertificate (n j : Nat) : List CoverToken → Option (CoverCertificate n j)
  | .header fmt gen k prec input :: rest => do
    let (tree, trailing) ← parseTree n j rest.length rest
    if trailing = [] then some ⟨fmt, gen, input, k, prec, tree⟩ else none
  | _ => none

theorem parseCertificate_serialize (c : CoverCertificate n j) :
    parseCertificate n j (serializeCertificate c) = some c := by
  have h := parseTree_serialize c.tree [] (serializeTree c.tree).length (nodes_le_serialized_length c.tree)
  simp only [List.append_nil] at h
  simp [serializeCertificate, parseCertificate, h]

def verifySerializedCertificate (input : List Nat) (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (tokens : List CoverToken) : Bool :=
  match parseCertificate n j tokens with
  | none => false
  | some c => verifyCoverCertificate input cs gs H c

theorem verifySerializedCertificate_sound (input : List Nat) (cs : Nat → Fin a → QInterval)
    (gs : Fin j → PolyExpr n a) (H : PolyExpr n a) (tokens : List CoverToken)
    (h : verifySerializedCertificate input cs gs H tokens = true) :
    ∃ c, parseCertificate n j tokens = some c ∧ verifyCoverCertificate input cs gs H c = true := by
  unfold verifySerializedCertificate at h
  split at h
  · contradiction
  · exact ⟨_, by assumption, h⟩

end Cover

namespace Cover

theorem parseTree_sound (n j fuel : Nat) (tokens : List CoverToken)
    (t : CoverTree n j) (rest : List CoverToken)
    (h : parseTree n j fuel tokens = some (t, rest)) : serializeTree t ++ rest = tokens := by
  induction fuel generalizing tokens t rest with
  | zero => contradiction
  | succ fuel ih =>
    cases tokens with
    | nil => contradiction
    | cons token tokens =>
      cases token with
      | header fmt gen k prec input => contradiction
      | unknown tag => contradiction
      | gap => cases h; rfl
      | exclude i =>
        by_cases hi : i < j
        · simp only [parseTree, hi, ↓reduceDIte] at h
          cases h
          rfl
        · simp [parseTree, hi] at h
      | split i =>
        by_cases hi : i < n
        · simp only [parseTree, hi, ↓reduceDIte] at h
          cases hl : parseTree n j fuel tokens with
          | none => simp [hl] at h
          | some pair =>
            rcases pair with ⟨left, middle⟩
            rw [hl] at h
            dsimp only [Bind.bind, Option.bind] at h
            cases hr : parseTree n j fuel middle with
            | none => simp [hr] at h
            | some pair =>
              rcases pair with ⟨right, final⟩
              rw [hr] at h
              dsimp only [Bind.bind, Option.bind] at h
              cases h
              have hleft := ih tokens left middle hl
              have hright := ih middle right rest hr
              simp only [serializeTree, List.cons_append, List.append_assoc, hright, hleft]
        · simp [parseTree, hi] at h

theorem parseCertificate_sound (n j : Nat) (tokens : List CoverToken)
    (c : CoverCertificate n j) (h : parseCertificate n j tokens = some c) :
    serializeCertificate c = tokens := by
  cases tokens with
  | nil => contradiction
  | cons token tokens =>
    cases token with
    | gap => contradiction
    | exclude i => contradiction
    | split i => contradiction
    | unknown tag => contradiction
    | header fmt gen k prec input =>
      simp only [parseCertificate] at h
      cases hp : parseTree n j tokens.length tokens with
      | none => simp [hp] at h
      | some pair =>
        rcases pair with ⟨tree, trailing⟩
        rw [hp] at h
        dsimp only [Bind.bind, Option.bind] at h
        split at h
        · rename_i ht
          subst trailing
          cases h
          have hs := parseTree_sound n j tokens.length tokens tree [] hp
          simpa [serializeCertificate] using congrArg
            (fun tail => CoverToken.header fmt gen k prec input :: tail) hs
        · contradiction

end Cover
