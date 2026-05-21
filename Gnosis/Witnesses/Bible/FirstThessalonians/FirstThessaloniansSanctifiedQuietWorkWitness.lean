import Init

namespace Gnosis.Witnesses.Bible.FirstThessalonians
namespace FirstThessaloniansSanctifiedQuietWorkWitness

/-!
# 1 Thessalonians 4:1-12 -- Sanctification, Brotherly Love, Quiet Work

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95032-95071`.

The will of God is mapped into embodied sanctification and non-defrauding love.
Brotherly love then becomes quiet work: own business, own hands, honest walk
toward outsiders, lack of nothing.

No `sorry`, no new `axiom`.
-/

structure SanctifiedVessel where
  aboundMorePleasingWalk : Bool := true
  commandmentsByLordKnown : Bool := true
  sanctificationWillOfGod : Bool := true
  abstainFromFornication : Bool := true
  vesselInHonor : Bool := true
  notGentileLustIgnorance : Bool := true
  brotherNotDefrauded : Bool := true
  calledToHolinessSpiritGiven : Bool := true
deriving DecidableEq, Repr

def sanctifiedVessel : SanctifiedVessel := {}

def sanctifiedVesselWitness (s : SanctifiedVessel) : Prop :=
  s.aboundMorePleasingWalk = true ∧ s.commandmentsByLordKnown = true ∧
  s.sanctificationWillOfGod = true ∧ s.abstainFromFornication = true ∧
  s.vesselInHonor = true ∧ s.notGentileLustIgnorance = true ∧
  s.brotherNotDefrauded = true ∧ s.calledToHolinessSpiritGiven = true

structure QuietWorkLove where
  taughtOfGodBrotherlyLove : Bool := true
  loveAllMacedonia : Bool := true
  increaseMoreAndMore : Bool := true
  studyToBeQuiet : Bool := true
  doOwnBusiness : Bool := true
  workOwnHands : Bool := true
  honestWalkTowardOutsiders : Bool := true
  lackOfNothing : Bool := true
deriving DecidableEq, Repr

def quietWorkLove : QuietWorkLove := {}

def quietWorkWitness (q : QuietWorkLove) : Prop :=
  q.taughtOfGodBrotherlyLove = true ∧ q.loveAllMacedonia = true ∧
  q.increaseMoreAndMore = true ∧ q.studyToBeQuiet = true ∧
  q.doOwnBusiness = true ∧ q.workOwnHands = true ∧
  q.honestWalkTowardOutsiders = true ∧ q.lackOfNothing = true

theorem first_thessalonians_sanctified_vessel :
    sanctifiedVesselWitness sanctifiedVessel := by
  unfold sanctifiedVesselWitness sanctifiedVessel
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_quiet_work :
    quietWorkWitness quietWorkLove := by
  unfold quietWorkWitness quietWorkLove
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_sanctified_quiet_work_witness :
    sanctifiedVesselWitness sanctifiedVessel ∧
    quietWorkWitness quietWorkLove := by
  exact ⟨first_thessalonians_sanctified_vessel, first_thessalonians_quiet_work⟩

end FirstThessaloniansSanctifiedQuietWorkWitness
end Gnosis.Witnesses.Bible.FirstThessalonians
