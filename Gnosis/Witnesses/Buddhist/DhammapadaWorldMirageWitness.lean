import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Buddhist

/-! Witness ledger for Dhammapada chapter 13, "The World". -/

structure WorldMirage where
  worldBubble : Bool := true
  worldMirage : Bool := true
  deathDoesNotSee : Bool := true
  glitteringWorldImmersesFools : Bool := true
  wiseDoNotTouch : Bool := true
  soberBrightensWorld : Bool := true
  lyingAfterTransgressionAllowsAllEvil : Bool := true
  firstHolinessOutranksWorldLordship : Bool := true
deriving Repr, DecidableEq

def worldMirage : WorldMirage := {}

theorem dhammapada_world_mirage_witness :
    worldMirage.worldBubble = true ∧
      worldMirage.worldMirage = true ∧
      worldMirage.deathDoesNotSee = true ∧
      worldMirage.wiseDoNotTouch = true ∧
      worldMirage.soberBrightensWorld = true ∧
      worldMirage.lyingAfterTransgressionAllowsAllEvil = true ∧
      worldMirage.firstHolinessOutranksWorldLordship = true := by
  simp [worldMirage]

end Gnosis.Witnesses.Buddhist
