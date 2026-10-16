import Cover.FiniteDesign
import Cover.MarginValidation

namespace Cover.A06

/-- The whole finite mathematical input, before exact validation. -/
structure Input where
  design : FiniteDesign.Syntax
  weight : AlgCode
  sigma : AlgCode

def Valid (I : Input) : Prop := FiniteDesign.Valid I.design ∧
  Margins.Valid (I.design.rankPred+1) I.weight I.sigma
instance (I : Input) : Decidable (Valid I) := inferInstanceAs (Decidable (_ ∧ _))

def validateCoverInput (I : Input) : Bool := decide (Valid I)
@[simp] theorem validateCoverInput_iff (I : Input) : validateCoverInput I = true ↔ Valid I := by
  simp [validateCoverInput]

def alphabetSizes (I : Input) : Fin I.design.groups → Nat := fun g => I.design.outputPred g + 1

def edgeLists (I : Input) : List (List (Fin I.design.groups)) :=
  I.design.edges.map (fun e => e.sort (· ≤ ·))

lemma alphabetSizes_pos (I : Input) (g : Fin I.design.groups) : 0 < alphabetSizes I g := Nat.succ_pos _
lemma edgeLists_nonempty (I : Input) (h : Valid I) : edgeLists I ≠ [] := by
  simpa [edgeLists] using h.1.2.2.1


end Cover.A06
