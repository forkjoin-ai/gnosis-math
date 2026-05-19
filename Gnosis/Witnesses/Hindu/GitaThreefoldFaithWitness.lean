import Gnosis.Witnesses.Hindu.GitaQualitiesSeparationWitness

namespace Gnosis.Witnesses.Hindu

/-! Witness ledger for `bhagavad-gita-arnold.txt`, chapter 17. -/

structure ThreefoldFaith where
  faithConformsToNature : Bool := true
  foodClassifiedByGuna : Bool := true
  sacrificeClassifiedByMotive : Bool := true
  bodySpeechMindAusterity : Bool := true
  sattvicAusterityWithoutFruit : Bool := true
  rajasicDisplayReligionUnstable : Bool := true
  tamasicViolentPenanceRejected : Bool := true
  giftsClassifiedByRecipientTimeMotive : Bool := true
  omTatSatGuardsRite : Bool := true
  faithlessRiteAsat : Bool := true
deriving Repr, DecidableEq

def threefoldFaith : ThreefoldFaith := {}

theorem gita_threefold_faith_witness :
    threefoldFaith.faithConformsToNature = true ∧
      threefoldFaith.sacrificeClassifiedByMotive = true ∧
      threefoldFaith.bodySpeechMindAusterity = true ∧
      threefoldFaith.rajasicDisplayReligionUnstable = true ∧
      threefoldFaith.tamasicViolentPenanceRejected = true ∧
      threefoldFaith.giftsClassifiedByRecipientTimeMotive = true ∧
      threefoldFaith.faithlessRiteAsat = true := by
  simp [threefoldFaith]

end Gnosis.Witnesses.Hindu
