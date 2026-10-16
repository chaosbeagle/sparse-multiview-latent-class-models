import Cover.CompilerTasks
import Cover.InputSerializationTasks

namespace Cover.CompilerTasks

/-- Uses the stored count proof; it never regenerates compiler syntax or recomputes its length. -/
def CompiledData.constraint (c : CompiledData) (i : Fin c.constraintCount) : PolyExpr c.n 3 :=
  c.constraints.get ⟨i.val, by rw [← c.count_eq]; exact i.isLt⟩

theorem compileTask_run_sound (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I)
    (fuel : ℕ) (c : CompiledData) (hc : FinTask.run fuel (compileTask I h) = some c) :
    c = canonicalData I h :=
  (FinTask.run_sound fuel (compileTask I h) c hc).symm.trans (compileTask_result I h)

theorem compileTask_exists_fuel (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    ∃ fuel, FinTask.run fuel (compileTask I h) = some (canonicalData I h) := by
  refine ⟨(compileTask I h).steps, ?_⟩
  rw [← compileTask_result I h]
  exact FinTask.run_sufficient _ _ le_rfl

/-- Exhausting zero fuel stops before any compiler initialization is executed. -/
theorem compileTask_zero_fuel (I : FiniteDesign.Syntax) (h : FiniteDesign.Valid I) :
    FinTask.run 0 (compileTask I h) = none := rfl
end Cover.CompilerTasks

namespace Cover.InputTasks

theorem parseDesignTask_run_sound (raw : List ℕ) (fuel : ℕ) (out : Option FiniteDesign.Syntax)
    (h : FinTask.run fuel (parseDesignTask raw) = some out) : DesignCodec.parse raw = out :=
  (parseDesignTask_result raw).symm.trans (FinTask.run_sound _ _ _ h)

theorem parseRawTask_run_sound (raw : List ℕ) (fuel : ℕ) (out : Option A06.Input)
    (h : FinTask.run fuel (parseRawTask raw) = some out) : A06InputCodec.parseRaw raw = out :=
  (parseRawTask_result raw).symm.trans (FinTask.run_sound _ _ _ h)

theorem serializeInputTask_run_sound (I : A06.Input) (fuel : ℕ) (out : List ℕ)
    (h : FinTask.run fuel (serializeInputTask I) = some out) : A06InputCodec.serialize I = out :=
  (serializeInputTask_result I).symm.trans (FinTask.run_sound _ _ _ h)
end Cover.InputTasks
