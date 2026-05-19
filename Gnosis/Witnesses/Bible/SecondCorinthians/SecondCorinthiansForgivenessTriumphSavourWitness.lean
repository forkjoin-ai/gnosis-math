import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansForgivenessTriumphSavourWitness

/-! # 2 Corinthians 2 -- Forgiveness, Triumph, and Savour
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92879-92927`. -/

structure ForgivenessTriumphSavour where
  notComeAgainInHeaviness : Bool
  tearsShowAbundantLove : Bool
  punishmentSufficient : Bool
  forgiveComfortConfirmLove : Bool
  obedienceProved : Bool
  forgiveInPersonOfChrist : Bool
  notIgnorantSatanDevices : Bool
  troasDoorOpenedNoRestWithoutTitus : Bool
  godCausesTriumphInChrist : Bool
  savourOfChristLifeAndDeath : Bool
  sincerityInSightOfGodSpeakInChrist : Bool
deriving DecidableEq, Repr

def forgivenessTriumphSavour : ForgivenessTriumphSavour where
  notComeAgainInHeaviness := true
  tearsShowAbundantLove := true
  punishmentSufficient := true
  forgiveComfortConfirmLove := true
  obedienceProved := true
  forgiveInPersonOfChrist := true
  notIgnorantSatanDevices := true
  troasDoorOpenedNoRestWithoutTitus := true
  godCausesTriumphInChrist := true
  savourOfChristLifeAndDeath := true
  sincerityInSightOfGodSpeakInChrist := true

theorem second_corinthians_forgiveness_triumph_savour_witness :
    forgivenessTriumphSavour.notComeAgainInHeaviness = true
    ∧ forgivenessTriumphSavour.tearsShowAbundantLove = true
    ∧ forgivenessTriumphSavour.punishmentSufficient = true
    ∧ forgivenessTriumphSavour.forgiveComfortConfirmLove = true
    ∧ forgivenessTriumphSavour.obedienceProved = true
    ∧ forgivenessTriumphSavour.forgiveInPersonOfChrist = true
    ∧ forgivenessTriumphSavour.notIgnorantSatanDevices = true
    ∧ forgivenessTriumphSavour.troasDoorOpenedNoRestWithoutTitus = true
    ∧ forgivenessTriumphSavour.godCausesTriumphInChrist = true
    ∧ forgivenessTriumphSavour.savourOfChristLifeAndDeath = true
    ∧ forgivenessTriumphSavour.sincerityInSightOfGodSpeakInChrist = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansForgivenessTriumphSavourWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
