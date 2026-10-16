import Gen
import Ext
import Cover
import lean.RegressionTests
import lean.ConfidenceSmoke
import lean.CountInterfaceRegression
import lean.SemanticCrosswalk
import lean.GeneralizationRegression
import lean.CoverRegression
import lean.CompilerFuelRegression
import lean.CoverSemanticCrosswalk
import Lean.Compiler.NoncomputableAttr

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[``Cover.A06.validateCoverInput, ``Cover.A06.stage, ``Cover.A06.firstSuccessfulStage, ``Cover.A06.returnedTree, ``Cover.A06.verifyCertificate, ``Cover.A06.verifyRawCertificate, ``Cover.A06.runCover, ``Cover.A06InputCodec.parse, ``Cover.ConcreteCompiler.constraints, ``Cover.ConcreteCompiler.objective, ``Cover.validatedScalarCoefficients, ``Cover.AlgCode.compareTotal, ``Cover.AlgCode.positiveTotal, ``Cover.AlgCode.refinePrecisely, ``Cover.AlgCode.verifyRefinement, ``Cover.DyadicSqrt.bounds, ``Cover.ScalarExpr.bounds, ``Cover.checkTree, ``Cover.coverStage, ``Cover.Bytes.parseEvidenceByteArray, ``Cover.Bytes.serializeEvidenceByteArray, ``Cover.A06.runCoverCapped, ``Cover.A06.rawByteStageJob, ``Cover.A06.admittedStageJob, ``Cover.CompilerTasks.compileTask, ``Cover.InputTasks.parseRawTask, ``Cover.InputTasks.serializeInputTask, ``Cover.A06.Runtime.stageCoreTask, ``Cover.A06.Runtime.verifyTask, ``Cover.A06.Runtime.packageTask, ``Cover.stageStoredTask, ``Cover.checkTreeStoredTask, ``Cover.Bytes.serializeEvidenceBytesTask, ``Cover.Bytes.parseEvidenceBytesTask, ``Cover.Regression.runPhaseRegressions, ``Cover.A06.CappedRegression.runMalformedInputRegressions, ``Cover.A06ModelRegression.runCompilerFuelRegression]
  for name in roots do
    if isNoncomputable env name then throwError m!"NONCOMPUTABLE_ROOT {name}"
    logInfo m!"COMPUTABLE_ROOT {name}"

#print axioms Cover.A06.validateCoverInput
#print axioms Cover.A06.stage
#print axioms Cover.A06.firstSuccessfulStage
#print axioms Cover.A06.returnedTree
#print axioms Cover.A06.verifyCertificate
#print axioms Cover.A06.verifyRawCertificate
#print axioms Cover.A06.runCover
#print axioms Cover.A06InputCodec.parse
#print axioms Cover.ConcreteCompiler.constraints
#print axioms Cover.ConcreteCompiler.objective
#print axioms Cover.validatedScalarCoefficients
#print axioms Cover.AlgCode.compareTotal
#print axioms Cover.AlgCode.positiveTotal
#print axioms Cover.AlgCode.refinePrecisely
#print axioms Cover.AlgCode.verifyRefinement
#print axioms Cover.DyadicSqrt.bounds
#print axioms Cover.ScalarExpr.bounds
#print axioms Cover.checkTree
#print axioms Cover.coverStage
#print axioms Cover.Bytes.parseEvidenceByteArray
#print axioms Cover.Bytes.serializeEvidenceByteArray
#print axioms Cover.A06.runCoverCapped
#print axioms Cover.A06.rawByteStageJob
#print axioms Cover.A06.admittedStageJob
#print axioms Cover.CompilerTasks.compileTask
#print axioms Cover.InputTasks.parseRawTask
#print axioms Cover.InputTasks.serializeInputTask
#print axioms Cover.A06.Runtime.stageCoreTask
#print axioms Cover.A06.Runtime.verifyTask
#print axioms Cover.A06.Runtime.packageTask
#print axioms Cover.stageStoredTask
#print axioms Cover.checkTreeStoredTask
#print axioms Cover.Bytes.serializeEvidenceBytesTask
#print axioms Cover.Bytes.parseEvidenceBytesTask
#print axioms Cover.Regression.runPhaseRegressions
#print axioms Cover.A06.CappedRegression.runMalformedInputRegressions
#print axioms Cover.A06ModelRegression.runCompilerFuelRegression
