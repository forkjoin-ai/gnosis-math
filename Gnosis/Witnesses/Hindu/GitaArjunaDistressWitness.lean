import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 1. -/

structure BattlefieldDistress where
  armiesDrawnBetweenKin : Bool := true
  arjunaAsksToSeeOpponents : Bool := true
  kinshipSeenOnBothSides : Bool := true
  bodyFailsAtViolence : Bool := true
  victoryWealthRuleRejected : Bool := true
  socialOrderCollapseFeared : Bool := true
  weaponlessDeathPreferred : Bool := true
  bowDropped : Bool := true
deriving Repr, DecidableEq

def battlefieldDistress : BattlefieldDistress := {}

theorem gita_arjuna_distress_witness :
    battlefieldDistress.armiesDrawnBetweenKin = true ∧
      battlefieldDistress.arjunaAsksToSeeOpponents = true ∧
      battlefieldDistress.kinshipSeenOnBothSides = true ∧
      battlefieldDistress.bodyFailsAtViolence = true ∧
      battlefieldDistress.victoryWealthRuleRejected = true ∧
      battlefieldDistress.socialOrderCollapseFeared = true ∧
      battlefieldDistress.weaponlessDeathPreferred = true ∧
      battlefieldDistress.bowDropped = true := by
  simp [battlefieldDistress]

end Gnosis.Witnesses.Hindu
