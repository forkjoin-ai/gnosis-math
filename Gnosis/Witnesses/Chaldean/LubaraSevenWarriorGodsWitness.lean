import Gnosis.Witnesses.Chaldean.SevenWickedGodsStormRuleWitness

namespace Gnosis.Witnesses.Chaldean
namespace LubaraSevenWarriorGodsWitness

/-!
# Lubara Seven Warrior Gods Witness

Source surface:
`docs/ebooks/source-texts/chaldean-account-of-genesis-smith.txt`, Chapter VIII,
"The Exploits of Lubara."

This module records the third Chaldean sevenfold agency cluster in the current
pass: Lubara/Dabara as pestilence or plague, Itak marching before him, and
seven warrior gods following in the destructive course. The same chapter also
preserves a counter-operator: when Lubara is angry, "may the seven gods turn him
aside." Seven is therefore not random decoration. It marks a high-stakes agency
carrier in destructive procession and in diversion/appeasement.

The reserve remains strict. Smith marks the tablets as fragmentary and his
reading of Lubara/Dabara as hesitant, so this witness does not identify the
seven warrior gods by name and does not assign them to FRF-VI coordinates.

No `sorry`, no new `axiom`.
-/

structure LubaraPlagueProcession where
  lubaraReadWithHesitation : Bool := true
  lubaraAsPestilenceOrPlague : Bool := true
  itakMarchesBeforeLubara : Bool := true
  sevenGodsFollowDestructiveCourse : Bool := true
  anuCommandsPestilenceDestruction : Bool := true
deriving DecidableEq, Repr

def lubaraPlagueProcession : LubaraPlagueProcession := {}

def plagueProcessionWitness (p : LubaraPlagueProcession) : Prop :=
  p.lubaraReadWithHesitation = true ∧
  p.lubaraAsPestilenceOrPlague = true ∧
  p.itakMarchesBeforeLubara = true ∧
  p.sevenGodsFollowDestructiveCourse = true ∧
  p.anuCommandsPestilenceDestruction = true

structure SyriaDestructionMarch where
  itakFacesSyria : Bool := true
  sevenWarriorGodsUnequalledMarchAfterHim : Bool := true
  warriorDestroysLand : Bool := true
  peopleRanksBroken : Bool := true
  laterSummaryRepeatsItakSevenWarriorsDestroySyria : Bool := true
deriving DecidableEq, Repr

def syriaDestructionMarch : SyriaDestructionMarch := {}

def sevenWarriorMarchWitness (s : SyriaDestructionMarch) : Prop :=
  s.itakFacesSyria = true ∧
  s.sevenWarriorGodsUnequalledMarchAfterHim = true ∧
  s.warriorDestroysLand = true ∧
  s.peopleRanksBroken = true ∧
  s.laterSummaryRepeatsItakSevenWarriorsDestroySyria = true

structure SevenfoldDiversionCounterOperator where
  songEstablishedForMemory : Bool := true
  prophetAndTabletWriterProtected : Bool := true
  lubaraAngerNamed : Bool := true
  sevenGodsTurnHimAside : Bool := true
  praisePrayerFunctionsAsPlagueArrest : Bool := true
deriving DecidableEq, Repr

def sevenfoldDiversionCounterOperator : SevenfoldDiversionCounterOperator := {}

def sevenTurnsPlagueAside (d : SevenfoldDiversionCounterOperator) : Prop :=
  d.songEstablishedForMemory = true ∧
  d.prophetAndTabletWriterProtected = true ∧
  d.lubaraAngerNamed = true ∧
  d.sevenGodsTurnHimAside = true ∧
  d.praisePrayerFunctionsAsPlagueArrest = true

structure LubaraReserve where
  noSevenNamesEnumeratedHere : Bool := true
  noFRFVIAssignmentClaimed : Bool := true
  fragmentaryTabletReserveKept : Bool := true
  recurrenceEvidenceStrengthened : Bool := true
  sevenActsAsAgencyCardinality : Bool := true
deriving DecidableEq, Repr

def lubaraReserve : LubaraReserve := {}

def boundedLubaraSevenfoldClaim (r : LubaraReserve) : Prop :=
  r.noSevenNamesEnumeratedHere = true ∧
  r.noFRFVIAssignmentClaimed = true ∧
  r.fragmentaryTabletReserveKept = true ∧
  r.recurrenceEvidenceStrengthened = true ∧
  r.sevenActsAsAgencyCardinality = true

theorem lubara_plague_procession :
    plagueProcessionWitness lubaraPlagueProcession := by
  unfold plagueProcessionWitness lubaraPlagueProcession
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lubara_seven_warrior_march :
    sevenWarriorMarchWitness syriaDestructionMarch := by
  unfold sevenWarriorMarchWitness syriaDestructionMarch
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lubara_seven_turns_plague_aside :
    sevenTurnsPlagueAside sevenfoldDiversionCounterOperator := by
  unfold sevenTurnsPlagueAside sevenfoldDiversionCounterOperator
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lubara_bounded_sevenfold_claim :
    boundedLubaraSevenfoldClaim lubaraReserve := by
  unfold boundedLubaraSevenfoldClaim lubaraReserve
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lubara_strengthens_chaldean_sevenfold_recurrence :
    SevenWickedGodsStormRuleWitness.chaldeanSevenfoldRecurrence
      SevenWickedGodsStormRuleWitness.sevenfoldRecurrenceEvidence ∧
    plagueProcessionWitness lubaraPlagueProcession ∧
    sevenWarriorMarchWitness syriaDestructionMarch ∧
    sevenTurnsPlagueAside sevenfoldDiversionCounterOperator ∧
    boundedLubaraSevenfoldClaim lubaraReserve := by
  exact ⟨SevenWickedGodsStormRuleWitness.chaldean_sevenfold_recurrence,
    lubara_plague_procession,
    lubara_seven_warrior_march,
    lubara_seven_turns_plague_aside,
    lubara_bounded_sevenfold_claim⟩

theorem lubara_seven_warrior_gods_witness :
    plagueProcessionWitness lubaraPlagueProcession ∧
    sevenWarriorMarchWitness syriaDestructionMarch ∧
    sevenTurnsPlagueAside sevenfoldDiversionCounterOperator ∧
    boundedLubaraSevenfoldClaim lubaraReserve := by
  exact ⟨lubara_plague_procession,
    lubara_seven_warrior_march,
    lubara_seven_turns_plague_aside,
    lubara_bounded_sevenfold_claim⟩

end LubaraSevenWarriorGodsWitness
end Gnosis.Witnesses.Chaldean
