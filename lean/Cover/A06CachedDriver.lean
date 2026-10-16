import Cover.A06CachedReplay

namespace Cover.A06.Runtime

 def alignArray (I : Input) (h : Valid I) {n j : Nat}
    (hn : n = pairDimension I h) (hj : j = constraintCount I h)
    (gs : Fin j → PolyExpr n 3) : ConstraintArray I h := cast (by rw [hn,hj]) gs

 def alignObjective (I : Input) (h : Valid I) {n : Nat}
    (hn : n = pairDimension I h) (H : PolyExpr n 3) : Objective I h := cast (by rw [hn]) H

 theorem stageCoreTask_result (I : Input) (h : Valid I) (raw : List Nat)
    (hraw : raw = A06InputCodec.serialize I) (n j : Nat)
    (hn : n = pairDimension I h) (hj : j = constraintCount I h)
    (gs : Fin j → PolyExpr n 3) (H : PolyExpr n 3)
    (hgs : alignArray I h hn hj gs = ProjectSemantics.constraintArray I.design h.1)
    (hH : alignObjective I h hn H = ConcreteCompiler.objective I.design h.1) (s : Nat) :
    (stageCoreTask I h raw n j hn hj gs H s).result = stageAction I h s := by
  subst n; subst j
  simp only [alignArray, alignObjective, cast_eq] at hgs hH
  rw [stageCoreTask_actual]
  exact admittedStageCoreTask_result I h raw hraw gs H hgs hH s

/-- The inner admitted driver reuses already computed dimensions and polynomial
    syntax. The final raw driver constructs these through the concrete compiler task. -/
def runCachedFuel (I : Input) (h : Valid I) (raw : List Nat) (n j : Nat)
    (hn : n = pairDimension I h) (hj : j = constraintCount I h)
    (gs : Fin j → PolyExpr n 3) (H : PolyExpr n 3) (fuel : Nat) : CappedResult :=
  Capped.execute (stageCoreTask I h raw n j hn hj gs H) fuel (stageCoreTask I h raw n j hn hj gs H 0)

 theorem runCachedFuel_prefix (I : Input) (h : Valid I) (raw : List Nat) (n j : Nat)
    (hn : n = pairDimension I h) (hj : j = constraintCount I h)
    (gs : Fin j → PolyExpr n 3) (H : PolyExpr n 3) (f g : Nat) (hfg : f≤g)
    (hresult : runCachedFuel I h raw n j hn hj gs H f ≠ .unknownResource) :
    runCachedFuel I h raw n j hn hj gs H g = runCachedFuel I h raw n j hn hj gs H f :=
  Capped.fuel_prefix _ f g hfg _ hresult

 theorem runCachedFuel_checked (I : Input) (h : Valid I) (raw : List Nat)
    (hraw : raw = A06InputCodec.serialize I) (n j : Nat)
    (hn : n = pairDimension I h) (hj : j = constraintCount I h)
    (gs : Fin j → PolyExpr n 3) (H : PolyExpr n 3)
    (hgs : alignArray I h hn hj gs = ProjectSemantics.constraintArray I.design h.1)
    (hH : alignObjective I h hn H = ConcreteCompiler.objective I.design h.1) (fuel : Nat) :
    Capped.Checked Returned.Checked (runCachedFuel I h raw n j hn hj gs H fuel) := by
  have hs s : Capped.ActionChecked Returned.Checked (stageCoreTask I h raw n j hn hj gs H s).result := by
    rw [stageCoreTask_result I h raw hraw n j hn hj gs H hgs hH s]
    exact stageAction_checked I h s
  exact Capped.checked _ _ hs fuel _ (hs 0)

 theorem runCachedFuel_eventual (I : Input) (h : Valid I) (raw : List Nat)
    (hraw : raw = A06InputCodec.serialize I) (n j : Nat)
    (hn : n = pairDimension I h) (hj : j = constraintCount I h)
    (gs : Fin j → PolyExpr n 3) (H : PolyExpr n 3)
    (hgs : alignArray I h hn hj gs = ProjectSemantics.constraintArray I.design h.1)
    (hH : alignObjective I h hn H = ConcreteCompiler.objective I.design h.1) :
    ∃ fuel result, runCachedFuel I h raw n j hn hj gs H fuel = .certificate result := by
  let next := stageCoreTask I h raw n j hn hj gs H
  have hshape s : (next s).result = .again (s+1) ∨ ∃ value, (next s).result = .stop (.certificate value) := by
    dsimp only [next]
    rw [stageCoreTask_result I h raw hraw n j hn hj gs H hgs hH s]
    exact stageAction_shape I h s
  obtain ⟨s0,hs0⟩ := coverStage_eventually_succeeds I h
  obtain ⟨t,ht⟩ := hs0 s0 le_rfl
  have hs : (next (0+s0)).result = .stop (.certificate
      ⟨I,h,certificateAt I h s0 t,Bytes.serializeEvidenceByteArray (certificateAt I h s0 t)⟩) := by
    simp only [Nat.zero_add, next, stageCoreTask_result I h raw hraw n j hn hj gs H hgs hH,
      stageAction,ht]
  exact Capped.eventual next hshape s0 0 _ hs

end Cover.A06.Runtime
