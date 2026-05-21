namespace Gnosis.Witnesses.Bible.Revelation
namespace RevelationNewJerusalemWitness

/-!
# Revelation 19-22 -- Marriage Supper, Final Judgment, and New Jerusalem

Source slice: Revelation 19:1-22:21.

Invariant: Revelation ends by replacing beast-city commerce with bride-city
communion. Babylon's smoke rises; the Lamb's marriage supper opens; the Word
rides out; beast, false prophet, dragon, death, and hell are disposed; then the
city descends as measured hospitality with gates open and lying excluded.

Counterproof: do not worship the messenger. Twice the angel refuses John's
worship. The apocalypse is not angel-cult, image-cult, beast-cult, or city-cult:
testimony routes to God, and the testimony of Jesus is the spirit of prophecy.

Unseen sat: the final city has no temple because God and the Lamb are its
temple; no sun because the Lamb is light; no closed day-gates because there is
no night; no curse because throne and river/tree-life are internal. The book
ends where hospitality becomes pure: Spirit and bride say Come, and the thirsty
take water freely.

No `sorry`, no new `axiom`.
-/

structure MarriageWordVictory where
  alleluiaJudgmentOfBabylon : Bool := true
  marriageSupperOfLamb : Bool := true
  angelWorshipRefused : Bool := true
  faithfulTrueRiderJudgesWar : Bool := true
  wordOfGodMouthSwordRules : Bool := true
  beastFalseProphetCastAlive : Bool := true
  birdsSupperConsumesArmies : Bool := true
deriving DecidableEq, Repr

def marriageWordVictory : MarriageWordVictory := {}

def testimonyRoutesToGod (m : MarriageWordVictory) : Prop :=
  m.alleluiaJudgmentOfBabylon = true ∧
  m.marriageSupperOfLamb = true ∧
  m.angelWorshipRefused = true ∧
  m.faithfulTrueRiderJudgesWar = true ∧
  m.wordOfGodMouthSwordRules = true ∧
  m.beastFalseProphetCastAlive = true ∧
  m.birdsSupperConsumesArmies = true

structure MillenniumJudgment where
  dragonBoundSealedThousandYears : Bool := true
  witnessesReignFirstResurrection : Bool := true
  satanLoosedAndFinallyDevoured : Bool := true
  devilLakeFireWithBeastFalseProphet : Bool := true
  greatWhiteThroneEarthHeavenFlee : Bool := true
  booksAndBookOfLifeOpened : Bool := true
  deathHellCastIntoLake : Bool := true
deriving DecidableEq, Repr

def millenniumJudgment : MillenniumJudgment := {}

def finalDeceptionDisposed (m : MillenniumJudgment) : Prop :=
  m.dragonBoundSealedThousandYears = true ∧
  m.witnessesReignFirstResurrection = true ∧
  m.satanLoosedAndFinallyDevoured = true ∧
  m.devilLakeFireWithBeastFalseProphet = true ∧
  m.greatWhiteThroneEarthHeavenFlee = true ∧
  m.booksAndBookOfLifeOpened = true ∧
  m.deathHellCastIntoLake = true

structure NewJerusalemCity where
  newHeavenEarthNoSea : Bool := true
  brideCityDescends : Bool := true
  godDwellsWithPeople : Bool := true
  tearsDeathPainPassedAway : Bool := true
  alphaOmegaWaterLifeFreely : Bool := true
  foursquareMeasuredTwelveGatesFoundations : Bool := true
  noTempleGodLambTemple : Bool := true
  noSunLambLight : Bool := true
  gatesNotShutNoNight : Bool := true
  defilementLieExcludedBookLifeEntry : Bool := true
deriving DecidableEq, Repr

def newJerusalemCity : NewJerusalemCity := {}

def measuredHospitalityCity (n : NewJerusalemCity) : Prop :=
  n.newHeavenEarthNoSea = true ∧
  n.brideCityDescends = true ∧
  n.godDwellsWithPeople = true ∧
  n.tearsDeathPainPassedAway = true ∧
  n.alphaOmegaWaterLifeFreely = true ∧
  n.foursquareMeasuredTwelveGatesFoundations = true ∧
  n.noTempleGodLambTemple = true ∧
  n.noSunLambLight = true ∧
  n.gatesNotShutNoNight = true ∧
  n.defilementLieExcludedBookLifeEntry = true

structure RiverEpilogue where
  riverFromGodAndLambThrone : Bool := true
  treeLifeTwelveFruitsHealingNations : Bool := true
  noCurseFaceSeenNameForeheads : Bool := true
  sayingsFaithfulTrue : Bool := true
  sealNotBookTimeAtHand : Bool := true
  commandDoersEnterGatesTree : Bool := true
  spiritBrideSayCome : Bool := true
  addTakeAwayBoundary : Bool := true
  surelyComeQuicklyGraceClose : Bool := true
deriving DecidableEq, Repr

def riverEpilogue : RiverEpilogue := {}

def bookClosesAsOpenInvitation (r : RiverEpilogue) : Prop :=
  r.riverFromGodAndLambThrone = true ∧
  r.treeLifeTwelveFruitsHealingNations = true ∧
  r.noCurseFaceSeenNameForeheads = true ∧
  r.sayingsFaithfulTrue = true ∧
  r.sealNotBookTimeAtHand = true ∧
  r.commandDoersEnterGatesTree = true ∧
  r.spiritBrideSayCome = true ∧
  r.addTakeAwayBoundary = true ∧
  r.surelyComeQuicklyGraceClose = true

theorem revelation_testimony_routes_to_god :
    testimonyRoutesToGod marriageWordVictory := by
  unfold testimonyRoutesToGod marriageWordVictory
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem revelation_final_deception_disposed :
    finalDeceptionDisposed millenniumJudgment := by
  unfold finalDeceptionDisposed millenniumJudgment
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem revelation_measured_hospitality_city :
    measuredHospitalityCity newJerusalemCity := by
  unfold measuredHospitalityCity newJerusalemCity
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem revelation_book_closes_open_invitation :
    bookClosesAsOpenInvitation riverEpilogue := by
  unfold bookClosesAsOpenInvitation riverEpilogue
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem revelation_new_jerusalem_witness :
    testimonyRoutesToGod marriageWordVictory ∧
    finalDeceptionDisposed millenniumJudgment ∧
    measuredHospitalityCity newJerusalemCity ∧
    bookClosesAsOpenInvitation riverEpilogue := by
  exact ⟨revelation_testimony_routes_to_god,
    revelation_final_deception_disposed,
    revelation_measured_hospitality_city,
    revelation_book_closes_open_invitation⟩

end RevelationNewJerusalemWitness
end Gnosis.Witnesses.Bible.Revelation
