import Cover.DesignCodec

namespace Cover.DesignCodec

theorem parse_some_valid {xs : List ℕ} {I : FiniteDesign.Syntax} (hp : parse xs = some I) :
    FiniteDesign.Valid I := by
  unfold parse at hp
  split at hp
  · split at hp
    · cases hp
    · split at hp
      · split at hp
        · cases hp
        · split at hp
          · cases hp
          · split at hp
            · dsimp only at hp
              split at hp
              · cases hp
                assumption
              · cases hp
            · cases hp
      · cases hp
  · cases hp

/-- No completed rejection is guessed: success supplies the actual finite validator fact. -/
theorem parse_rejects_invalid {xs : List ℕ} {I : FiniteDesign.Syntax}
    (hI : ¬ FiniteDesign.Valid I) : parse xs ≠ some I := by
  intro hp; exact hI (parse_some_valid hp)
end Cover.DesignCodec
