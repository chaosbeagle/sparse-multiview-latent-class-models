import Cover.A06Executable
import Cover.A06Statistics
import Cover.ScalarTasks

namespace Cover.A06ModelRegression

def input : A06.Input where
  design := { groups := 3, rankPred := 1, outputPred := fun _ => 1, edges := [Finset.univ] }
  weight := .rat (1/2)
  sigma := .rat 1

theorem input_valid : A06.Valid input := by
  constructor
  · decide
  · apply Margins.valid_iff.mpr
    refine ⟨trivial,trivial,(1/2 : ℝ),1,?_,?_,?_,?_,?_,?_⟩ <;>
      norm_num [input,AlgCode.denotes]

def bogusGap : A06.Certificate input input_valid := A06.certificateAt input input_valid 0 (.leaf .gap)

def wrongVersion : A06.Certificate input input_valid :=
  { bogusGap with base := { bogusGap.base with formatVersion := 99 } }

def wrongInput : A06.Certificate input input_valid :=
  { bogusGap with base := { bogusGap.base with input := [999] } }

def wrongRefinement : A06.Certificate input input_valid :=
  { bogusGap with weightRefinement := AlgCodec.serialize (.rat 1) }

def checks : List (String × Bool) :=
  [ ("actual input validator", A06.validateCoverInput input),
    ("actual components", (ConcreteCompiler.modelOrdering input.design input_valid.1).components.values.length == 1),
    ("actual gauges", (ConcreteCompiler.modelOrdering input.design input_valid.1).gauges.values.length == 2),
    ("actual constraints", A06.constraintCount input input_valid == 48),
    ("false root GAP rejects", !(A06.verifyCertificate input input_valid bogusGap)),
    ("unrecognized format rejects", !(A06.verifyCertificate input input_valid wrongVersion)),
    ("wrong input rejects", !(A06.verifyCertificate input input_valid wrongInput)),
    ("false scalar refinement rejects", !(A06.verifyCertificate input input_valid wrongRefinement)),
    ("root GAP raw bytes reject", !(A06.verifyCertificateBytes input input_valid (Bytes.serializeEvidenceByteArray bogusGap))),
    ("input byte roundtrip", (A06.parseInputBytes (A06.serializeInputBytes input)).isSome),
    ("zero sqrt", DyadicSqrt.bounds 0 (.singleton 0) == .singleton 0),
    ("exact square sqrt", DyadicSqrt.bounds 0 (.singleton 4) == .singleton 2),
    ("stepped scalar zero fuel is unknown", (FinTask.run 0 (validatedScalarCoefficientsTask
      (A06.alphabetSizes input) (A06.edgeLists input) 2 input.weight input.sigma input_valid.2 0)).isNone) ]

#eval do
  for (label, ok) in checks do
    if ok = true then IO.println ("PASS " ++ label)
    else throw (IO.userError ("FAILED " ++ label))

/-- This file deliberately never evaluates an A06 unbounded/full-stage search.
These are bounded compiler/evaluator/checker regressions, not a numerical cover pilot. -/
theorem regression_scope : True := True.intro

end Cover.A06ModelRegression
