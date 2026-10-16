import Cover.CompilerTaskInterfaces
import Cover.PolynomialDegree

namespace Cover.CompilerTasks

theorem compileTask_objective_variableDegree_le_eight (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    (compileTask I h).result.objective.variableDegree ≤ 8 := by
  rw [compileTask_result]
  exact ConcreteCompiler.objective_variableDegree_le_eight I h

theorem compiled_objective_variableDegree_le_eight (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    (fuel : ℕ) (c : CompiledData) (hc : FinTask.run fuel (compileTask I h) = some c) :
    c.objective.variableDegree ≤ 8 := by
  rw [compileTask_run_sound I h fuel c hc]
  exact ConcreteCompiler.objective_variableDegree_le_eight I h

theorem compiled_dimension_pos (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    (fuel : ℕ) (c : CompiledData) (hc : FinTask.run fuel (compileTask I h) = some c) : 0 < c.n := by
  rw [compileTask_run_sound I h fuel c hc]
  exact ConcreteCompiler.pairDimension_pos I h
end Cover.CompilerTasks
