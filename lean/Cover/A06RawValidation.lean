import Cover.A06RawInputFacts

namespace Cover.A06
open FinTask

/-- Control wrapper for the concrete raw parser/serializer tasks. Its only proof
    parameters identify their exact finite-data results; mathematical margin
    validation itself uses the actual stepped algebraic comparison loops. -/
def validateTokenTask (raw : List Nat) (parser : FinTask (Option Input))
    (hpresult : parser.result = A06InputCodec.parseRaw raw)
    (serializer : Input → FinTask (List Nat))
    (hsresult : ∀ I, (serializer I).result = A06InputCodec.serialize I) :
    FinTask (Option (AdmittedTokens raw)) := do
  let parsed ← parser.attach
  match hp : parsed.val with
  | none => .done none
  | some I =>
      have hd : FiniteDesign.Valid I.design := parseRaw_design_valid
        ((parsed.property.trans hpresult).symm.trans hp)
      do
        let validated ← (AlgCode.validateMarginsSteppedTask (I.design.rankPred+1) I.weight I.sigma).attach
        if hm : validated.val = true then
          have hmargin : Margins.Valid (I.design.rankPred+1) I.weight I.sigma :=
            (validated.property.trans (AlgCode.validateMarginsSteppedTask_result _ _ _)).symm.trans hm
          let hI : Valid I := ⟨hd,hmargin⟩
          do
            let serialized ← (serializer I).attach
            let equal ← (equalListTask serialized.val raw).attach
            if he : equal.val = true then
              have hdec : decide (serialized.val=raw) = true :=
                (equal.property.trans (equalListTask_result _ _)).symm.trans he
              have hbinding : A06InputCodec.serialize I = raw :=
                (serialized.property.trans (hsresult I)).symm.trans (of_decide_eq_true hdec)
              .done (some ⟨I,hI,hbinding⟩)
            else .done none
        else .done none

 theorem validateTokenTask_result (raw : List Nat) (parser : FinTask (Option Input))
    (hpresult : parser.result = A06InputCodec.parseRaw raw)
    (serializer : Input → FinTask (List Nat))
    (hsresult : ∀ I, (serializer I).result = A06InputCodec.serialize I) :
    ((validateTokenTask raw parser hpresult serializer hsresult).result).map AdmittedTokens.input =
      A06InputCodec.parse raw := by
  simp only [validateTokenTask,FinTask.result_bindM]
  generalize hz : parser.attach.result = parsed
  rcases parsed with ⟨p,hp⟩
  have hparse : p = A06InputCodec.parseRaw raw := hp.trans hpresult
  cases p with
  | none => simp [A06InputCodec.parse,←hparse]
  | some I =>
    have hd := parseRaw_design_valid hparse.symm
    simp only [FinTask.result_bindM]
    generalize hzv : (AlgCode.validateMarginsSteppedTask (I.design.rankPred+1) I.weight I.sigma).attach.result = validated
    rcases validated with ⟨b,hb⟩
    have hmargin : b = AlgCode.validateMargins (I.design.rankPred+1) I.weight I.sigma :=
      hb.trans (AlgCode.validateMarginsSteppedTask_result _ _ _)
    cases b with
    | false => simp [A06InputCodec.parse,←hparse,Valid,hd,Margins.Valid,←hmargin]
    | true =>
      simp only [dite_true,FinTask.result_bindM]
      generalize hzs : (serializer I).attach.result = serialized
      rcases serialized with ⟨tokens,htokens⟩
      have hser : tokens = A06InputCodec.serialize I := htokens.trans (hsresult I)
      simp only [FinTask.result_bindM]
      generalize hze : (equalListTask tokens raw).attach.result = compared
      rcases compared with ⟨eq,heq⟩
      have heqb : eq = decide (tokens=raw) := heq.trans (equalListTask_result _ _)
      cases eq with
      | false =>
        have hn : tokens ≠ raw := of_decide_eq_false heqb.symm
        have hn' : A06InputCodec.serialize I ≠ raw := by simpa [hser] using hn
        simp [A06InputCodec.parse,←hparse,Valid,hd,Margins.Valid,←hmargin,hn']
      | true =>
        have he : tokens = raw := of_decide_eq_true heqb.symm
        have he' : A06InputCodec.serialize I = raw := hser.symm.trans he
        simp [A06InputCodec.parse,←hparse,Valid,hd,Margins.Valid,←hmargin,he']

end Cover.A06
