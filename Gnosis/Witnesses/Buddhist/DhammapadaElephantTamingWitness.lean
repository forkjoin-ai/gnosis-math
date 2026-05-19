import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Buddhist

/-! Witness ledger for Dhammapada chapter 23, "The Elephant". -/

structure ElephantTaming where
  endureAbuseLikeBattleElephant : Bool := true
  tamedBestAmongMen : Bool := true
  selfTamedBetterThanTamedAnimals : Bool := true
  tamedSelfReachesUntroddenCountry : Bool := true
  wanderingMindNowHeldLikeFuriousElephant : Bool := true
  drawSelfFromEvilWayLikeElephantFromMud : Bool := true
  prudentCompanionPreferred : Bool := true
  aloneBetterThanFoolCompany : Bool := true
  virtueLastingToOldAgePleasant : Bool := true
deriving Repr, DecidableEq

def elephantTaming : ElephantTaming := {}

theorem dhammapada_elephant_taming_witness :
    elephantTaming.endureAbuseLikeBattleElephant = true ∧
      elephantTaming.tamedBestAmongMen = true ∧
      elephantTaming.selfTamedBetterThanTamedAnimals = true ∧
      elephantTaming.tamedSelfReachesUntroddenCountry = true ∧
      elephantTaming.wanderingMindNowHeldLikeFuriousElephant = true ∧
      elephantTaming.drawSelfFromEvilWayLikeElephantFromMud = true ∧
      elephantTaming.aloneBetterThanFoolCompany = true ∧
      elephantTaming.virtueLastingToOldAgePleasant = true := by
  simp [elephantTaming]

end Gnosis.Witnesses.Buddhist
