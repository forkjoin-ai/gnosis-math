import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 16. -/

structure DivineUndivine where
  divineTraitsLeadLiberation : Bool := true
  undivineTraitsLeadBondage : Bool := true
  fearlessnessPurityTruthNonHarm : Bool := true
  hypocrisyPrideWrathHarshnessIgnorance : Bool := true
  noLawNoLordOnlyLustAntitheorem : Bool := true
  insatiableDesireBinds : Bool := true
  wealthPowerSelfhoodDelusion : Bool := true
  threeHellGatesLustWrathAvarice : Bool := true
  scriptureRuleGuardsAction : Bool := true
deriving Repr, DecidableEq

def divineUndivine : DivineUndivine := {}

theorem gita_divine_undivine_witness :
    divineUndivine.divineTraitsLeadLiberation = true ∧
      divineUndivine.undivineTraitsLeadBondage = true ∧
      divineUndivine.fearlessnessPurityTruthNonHarm = true ∧
      divineUndivine.hypocrisyPrideWrathHarshnessIgnorance = true ∧
      divineUndivine.noLawNoLordOnlyLustAntitheorem = true ∧
      divineUndivine.threeHellGatesLustWrathAvarice = true ∧
      divineUndivine.scriptureRuleGuardsAction = true := by
  simp [divineUndivine]

end Gnosis.Witnesses.Hindu
