import Gnosis.Witnesses.Hindu.GitaFieldKnowerWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 14. -/

structure QualitiesSeparation where
  sattvaIlluminatesAndBindsByJoyKnowledge : Bool := true
  rajasBindsByActionDesire : Bool := true
  tamasBindsBySlothDarkness : Bool := true
  gunasActNotSelf : Bool := true
  beyondGunasNoBirthDeathAgePain : Bool := true
  equalInLightActivityDarkness : Bool := true
  clodStoneGoldAlike : Bool := true
  praiseBlameFriendFoeEqual : Bool := true
  devotionCrossesQualities : Bool := true
deriving Repr, DecidableEq

def qualitiesSeparation : QualitiesSeparation := {}

theorem gita_qualities_separation_witness :
    qualitiesSeparation.sattvaIlluminatesAndBindsByJoyKnowledge = true ∧
      qualitiesSeparation.rajasBindsByActionDesire = true ∧
      qualitiesSeparation.tamasBindsBySlothDarkness = true ∧
      qualitiesSeparation.gunasActNotSelf = true ∧
      qualitiesSeparation.beyondGunasNoBirthDeathAgePain = true ∧
      qualitiesSeparation.clodStoneGoldAlike = true ∧
      qualitiesSeparation.devotionCrossesQualities = true := by
  simp [qualitiesSeparation]

end Gnosis.Witnesses.Hindu
