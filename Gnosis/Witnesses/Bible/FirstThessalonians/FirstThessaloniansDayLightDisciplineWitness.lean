import Init

namespace Gnosis.Witnesses.Bible.FirstThessalonians
namespace FirstThessaloniansDayLightDisciplineWitness

/-!
# 1 Thessalonians 5:1-28 -- Day-Light Sobriety and Communal Disciplines

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95096-95148`.

The day comes thief-like for darkness, but children of light are called to watch,
sober armor, comfort, and a dense communal discipline ledger.

No `sorry`, no new `axiom`.
-/

structure DayLightSobriety where
  timesSeasonsKnownEnough : Bool := true
  dayComesAsThief : Bool := true
  peaceSafetySuddenDestruction : Bool := true
  notInDarknessOvertaken : Bool := true
  childrenLightDay : Bool := true
  watchAndSober : Bool := true
  faithLoveBreastplate : Bool := true
  hopeSalvationHelmet : Bool := true
  appointedSalvationNotWrath : Bool := true
  wakeOrSleepLiveTogether : Bool := true
deriving DecidableEq, Repr

def dayLightSobriety : DayLightSobriety := {}

def dayLightWitness (d : DayLightSobriety) : Prop :=
  d.timesSeasonsKnownEnough = true ∧ d.dayComesAsThief = true ∧
  d.peaceSafetySuddenDestruction = true ∧ d.notInDarknessOvertaken = true ∧
  d.childrenLightDay = true ∧ d.watchAndSober = true ∧
  d.faithLoveBreastplate = true ∧ d.hopeSalvationHelmet = true ∧
  d.appointedSalvationNotWrath = true ∧ d.wakeOrSleepLiveTogether = true

structure CommunalDiscipline where
  comfortEdifyOneAnother : Bool := true
  knowEsteemLaborers : Bool := true
  peaceAmongYourselves : Bool := true
  warnComfortSupportPatient : Bool := true
  noEvilForEvilFollowGood : Bool := true
  rejoicePrayThank : Bool := true
  quenchNotDespiseNot : Bool := true
  proveHoldGoodAbstainEvil : Bool := true
  wholeSpiritSoulBodyBlameless : Bool := true
  faithfulCallerWillDoIt : Bool := true
  readEpistleAllBrethren : Bool := true
deriving DecidableEq, Repr

def communalDiscipline : CommunalDiscipline := {}

def communalDisciplineWitness (c : CommunalDiscipline) : Prop :=
  c.comfortEdifyOneAnother = true ∧ c.knowEsteemLaborers = true ∧
  c.peaceAmongYourselves = true ∧ c.warnComfortSupportPatient = true ∧
  c.noEvilForEvilFollowGood = true ∧ c.rejoicePrayThank = true ∧
  c.quenchNotDespiseNot = true ∧ c.proveHoldGoodAbstainEvil = true ∧
  c.wholeSpiritSoulBodyBlameless = true ∧ c.faithfulCallerWillDoIt = true ∧
  c.readEpistleAllBrethren = true

theorem first_thessalonians_day_light :
    dayLightWitness dayLightSobriety := by
  unfold dayLightWitness dayLightSobriety
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_communal_discipline :
    communalDisciplineWitness communalDiscipline := by
  unfold communalDisciplineWitness communalDiscipline
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_day_light_discipline_witness :
    dayLightWitness dayLightSobriety ∧
    communalDisciplineWitness communalDiscipline := by
  exact ⟨first_thessalonians_day_light, first_thessalonians_communal_discipline⟩

end FirstThessaloniansDayLightDisciplineWitness
end Gnosis.Witnesses.Bible.FirstThessalonians
