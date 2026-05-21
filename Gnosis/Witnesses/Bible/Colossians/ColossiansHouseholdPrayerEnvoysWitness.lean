import Init

namespace Gnosis.Witnesses.Bible.Colossians
namespace ColossiansHouseholdPrayerEnvoysWitness

/-!
# Colossians 3:18-4:18 -- Household Order, Prayer Door, Salted Speech, Envoys

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94862-94916`.

The closing conduct ledger ties household work to the Lord Christ, then opens a
door-of-utterance protocol: prayer, watchfulness, wisdom toward outsiders,
grace-seasoned speech, envoys, circulating letters, and fulfilled ministry.

No `sorry`, no new `axiom`.
-/

structure HouseholdLordService where
  wivesFitInLord : Bool := true
  husbandsLoveNotBitter : Bool := true
  childrenPleaseLord : Bool := true
  fathersDiscourageNot : Bool := true
  servantsNotEyeservice : Bool := true
  workHeartilyToLord : Bool := true
  inheritanceRewardFromLord : Bool := true
  wrongReceivesNoRespectPersons : Bool := true
  mastersJustEqualHeavenMaster : Bool := true
deriving DecidableEq, Repr

def householdLordService : HouseholdLordService := {}

def householdLordServiceWitness (h : HouseholdLordService) : Prop :=
  h.wivesFitInLord = true ∧ h.husbandsLoveNotBitter = true ∧
  h.childrenPleaseLord = true ∧ h.fathersDiscourageNot = true ∧
  h.servantsNotEyeservice = true ∧ h.workHeartilyToLord = true ∧
  h.inheritanceRewardFromLord = true ∧ h.wrongReceivesNoRespectPersons = true ∧
  h.mastersJustEqualHeavenMaster = true

structure PrayerEnvoyClosing where
  continuePrayerWatchThanksgiving : Bool := true
  doorOfUtteranceMystery : Bool := true
  bondsForMystery : Bool := true
  walkWisdomRedeemTime : Bool := true
  speechGraceSaltAnswer : Bool := true
  tychicusOnesimusComfort : Bool := true
  fellowworkersAndEpaphrasPrayer : Bool := true
  epistleCirculatedLaodicea : Bool := true
  archippusFulfilMinistry : Bool := true
  rememberBondsGraceClosing : Bool := true
deriving DecidableEq, Repr

def prayerEnvoyClosing : PrayerEnvoyClosing := {}

def prayerEnvoyClosingWitness (p : PrayerEnvoyClosing) : Prop :=
  p.continuePrayerWatchThanksgiving = true ∧ p.doorOfUtteranceMystery = true ∧
  p.bondsForMystery = true ∧ p.walkWisdomRedeemTime = true ∧
  p.speechGraceSaltAnswer = true ∧ p.tychicusOnesimusComfort = true ∧
  p.fellowworkersAndEpaphrasPrayer = true ∧ p.epistleCirculatedLaodicea = true ∧
  p.archippusFulfilMinistry = true ∧ p.rememberBondsGraceClosing = true

theorem colossians_household_lord_service :
    householdLordServiceWitness householdLordService := by
  unfold householdLordServiceWitness householdLordService
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_prayer_envoy_closing :
    prayerEnvoyClosingWitness prayerEnvoyClosing := by
  unfold prayerEnvoyClosingWitness prayerEnvoyClosing
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_household_prayer_envoys_witness :
    householdLordServiceWitness householdLordService ∧
    prayerEnvoyClosingWitness prayerEnvoyClosing := by
  exact ⟨colossians_household_lord_service, colossians_prayer_envoy_closing⟩

end ColossiansHouseholdPrayerEnvoysWitness
end Gnosis.Witnesses.Bible.Colossians
