import Cover.FiniteDesign

namespace Cover.DesignCodec
open Cover.FiniteDesign

/-- Counted finite Nat-token block. -/
def writeBlock (xs : List ℕ) : List ℕ := xs.length :: xs

def readBlock : List ℕ → Option (List ℕ × List ℕ)
  | [] => none
  | n :: xs => if n ≤ xs.length then some (xs.take n, xs.drop n) else none

theorem readBlock_writeBlock (xs rest : List ℕ) :
    readBlock (writeBlock xs ++ rest) = some (xs,rest) := by
  simp [readBlock,writeBlock,List.take_left,List.drop_left]

/-- Bounds are checked before constructing a Fin index. -/
def readIndices (g : ℕ) : List ℕ → Option (List (Fin g))
  | [] => some []
  | i :: is => if hi : i < g then (readIndices g is).map (fun js => ⟨i,hi⟩ :: js) else none

theorem readIndices_write (g : ℕ) (xs : List (Fin g)) :
    readIndices g (xs.map Fin.val) = some xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [readIndices,i.isLt,ih]

/-- An edge is serialized by its sorted three indices and an explicit list length. -/
def writeEdge {g : ℕ} (e : Finset (Fin g)) : List ℕ := writeBlock ((e.sort (· ≤ ·)).map Fin.val)

def readEdge (g : ℕ) (xs : List ℕ) : Option (Finset (Fin g) × List ℕ) :=
  match readBlock xs with
  | none => none
  | some (ys,rest) => match readIndices g ys with
    | none => none
    | some zs => if zs.length = 3 ∧ zs.Nodup ∧ zs.Pairwise (· ≤ ·) then
        some (zs.toFinset,rest) else none

theorem readEdge_writeEdge {g : ℕ} (e : Finset (Fin g)) (he : e.card = 3) (rest : List ℕ) :
    readEdge g (writeEdge e ++ rest) = some (e,rest) := by
  simp only [readEdge,writeEdge,readBlock_writeBlock,
    readIndices_write]
  simp [he,Finset.sort_nodup,Finset.pairwise_sort,Finset.sort_toFinset]

def writeEdges {g : ℕ} (es : List (Finset (Fin g))) : List ℕ := es.flatMap writeEdge

def readEdges (g : ℕ) : ℕ → List ℕ → Option (List (Finset (Fin g)) × List ℕ)
  | 0, xs => some ([],xs)
  | n+1, xs => match readEdge g xs with
    | none => none
    | some (e,rest) => match readEdges g n rest with
      | none => none
      | some (es,tail) => some (e::es,tail)

theorem readEdges_writeEdges {g : ℕ} (es : List (Finset (Fin g)))
    (he : ∀ e ∈ es, e.card = 3) (rest : List ℕ) :
    readEdges g es.length (writeEdges es ++ rest) = some (es,rest) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.length_cons,writeEdges,List.flatMap_cons,List.append_assoc,readEdges]
    rw [readEdge_writeEdge e (he e (by simp))]
    change (match readEdges g es.length (writeEdges es ++ rest) with
      | none => none
      | some (fs,tail) => some (e::fs,tail)) = some (e::es,rest)
    rw [ih (fun f hf => he f (by simp [hf]))]

/-- Version, number of groups, latent rank predecessor, counted output-size predecessors,
then the number of edges and their counted sorted index lists. -/
def serialize (I : Syntax) : List ℕ :=
  [1,I.groups,I.rankPred] ++ writeBlock (List.ofFn I.outputPred) ++
    I.edges.length :: writeEdges I.edges

/-- Parsing is total, validates all finite structure, and rejects trailing tokens. -/
def parse : List ℕ → Option Syntax
  | 1 :: g :: r :: xs => match readBlock xs with
    | none => none
    | some (ns,rest) =>
      if hn : ns.length = g then
        let outputs : Fin g → ℕ := fun i => ns.get ⟨i.val, by omega⟩
        match rest with
        | [] => none
        | m :: tail => match readEdges g m tail with
          | none => none
          | some (es,leftover) =>
            if leftover = [] then
              let I : Syntax := ⟨g,r,outputs,es⟩
              if Valid I then some I else none
            else none
      else none
  | _ => none

/-- Exact input recovery, including the original outer-edge order. -/
theorem parse_serialize (I : Syntax) (h : Valid I) : parse (serialize I) = some I := by
  cases I with
  | mk g r ns es =>
    simp only [serialize,List.cons_append,List.nil_append,List.append_assoc,parse]
    rw [readBlock_writeBlock]
    simp only [List.length_ofFn,dite_true]
    have hed := readEdges_writeEdges es h.2.2.2.2.1 []
    simp only [List.append_nil] at hed
    rw [hed]
    simp only [ite_true]
    have hn : (fun i : Fin g => (List.ofFn ns).get ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩) = ns := by
      funext i; simp [List.get_ofFn]
    simpa only [hn,if_pos h] using (rfl : (some (Syntax.mk g r ns es) : Option Syntax) = some (Syntax.mk g r ns es))

/-- Therefore two admitted inputs cannot share the same serialized binding. -/
theorem serialize_injective_on_valid {I J : Syntax} (hI : Valid I) (hJ : Valid J)
    (h : serialize I = serialize J) : I = J := by
  have he := congrArg parse h
  rw [parse_serialize I hI,parse_serialize J hJ] at he
  exact Option.some.inj he
end Cover.DesignCodec
