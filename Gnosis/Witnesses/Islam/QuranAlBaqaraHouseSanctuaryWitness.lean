import Init

namespace Gnosis.Witnesses.Islam
namespace QuranAlBaqaraHouseSanctuaryWitness

/-!
# Quran 2:125-126, Al-Baqara -- House, Sanctuary, Security, Provision

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:1358-1367`.

This bounded witness tracks the House and Abraham's prayer:

  * the House is made a resort and sanctuary for people;
  * Abraham's standing-place is made a place of prayer;
  * Abraham and Ishmael are commanded to purify the House;
  * purification serves circling, staying, bowing, and prostrating worshippers;
  * Abraham asks for secure land and produce for believers in God and the Last Day;
  * disbelievers receive short enjoyment followed by Fire.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

inductive HouseSanctuaryMoment
  | houseResortSanctuary
  | abrahamPrayerPlace
  | purificationCommand
  | worshipperService
  | secureLandPrayer
  | provisionForBelievers
  | shortEnjoymentFire
deriving DecidableEq, Repr

def houseSanctuaryMoments : List HouseSanctuaryMoment :=
  [ HouseSanctuaryMoment.houseResortSanctuary
  , HouseSanctuaryMoment.abrahamPrayerPlace
  , HouseSanctuaryMoment.purificationCommand
  , HouseSanctuaryMoment.worshipperService
  , HouseSanctuaryMoment.secureLandPrayer
  , HouseSanctuaryMoment.provisionForBelievers
  , HouseSanctuaryMoment.shortEnjoymentFire
  ]

structure HousePurificationPattern where
  houseMadeResort : Bool
  houseMadeSanctuary : Bool
  abrahamStandingPlacePrayer : Bool
  abrahamCommanded : Bool
  ishmaelCommanded : Bool
  housePurified : Bool
  walkersRoundServed : Bool
  stayersServed : Bool
  bowProstrateWorshippersServed : Bool
deriving DecidableEq, Repr

def housePurificationPattern : HousePurificationPattern where
  houseMadeResort := true
  houseMadeSanctuary := true
  abrahamStandingPlacePrayer := true
  abrahamCommanded := true
  ishmaelCommanded := true
  housePurified := true
  walkersRoundServed := true
  stayersServed := true
  bowProstrateWorshippersServed := true

structure SecurityProvisionPattern where
  abrahamPrays : Bool
  landSecurityRequested : Bool
  produceProvisionRequested : Bool
  believersInGodBoundary : Bool
  lastDayBoundary : Bool
  disbelieversShortEnjoyment : Bool
  fireTorment : Bool
  evilDestination : Bool
deriving DecidableEq, Repr

def securityProvisionPattern : SecurityProvisionPattern where
  abrahamPrays := true
  landSecurityRequested := true
  produceProvisionRequested := true
  believersInGodBoundary := true
  lastDayBoundary := true
  disbelieversShortEnjoyment := true
  fireTorment := true
  evilDestination := true

theorem quran_al_baqara_house_sanctuary_witness :
    houseSanctuaryMoments.length = 7
    ∧ houseSanctuaryMoments.head? = some HouseSanctuaryMoment.houseResortSanctuary
    ∧ houseSanctuaryMoments.getLast? = some HouseSanctuaryMoment.shortEnjoymentFire
    ∧ housePurificationPattern.houseMadeResort = true
    ∧ housePurificationPattern.houseMadeSanctuary = true
    ∧ housePurificationPattern.abrahamStandingPlacePrayer = true
    ∧ housePurificationPattern.abrahamCommanded = true
    ∧ housePurificationPattern.ishmaelCommanded = true
    ∧ housePurificationPattern.housePurified = true
    ∧ housePurificationPattern.walkersRoundServed = true
    ∧ housePurificationPattern.bowProstrateWorshippersServed = true
    ∧ securityProvisionPattern.abrahamPrays = true
    ∧ securityProvisionPattern.landSecurityRequested = true
    ∧ securityProvisionPattern.produceProvisionRequested = true
    ∧ securityProvisionPattern.believersInGodBoundary = true
    ∧ securityProvisionPattern.lastDayBoundary = true
    ∧ securityProvisionPattern.disbelieversShortEnjoyment = true
    ∧ securityProvisionPattern.fireTorment = true
    ∧ securityProvisionPattern.evilDestination = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end QuranAlBaqaraHouseSanctuaryWitness
end Gnosis.Witnesses.Islam
