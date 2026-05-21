import Init

namespace Gnosis.Witnesses.Bible.FirstThessalonians
namespace FirstThessaloniansNurseFatherMinistryWitness

/-!
# 1 Thessalonians 2:1-12 -- Non-Flattering Ministry, Nurse Gentleness, Father Charge

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94922-94957`.

The ministry is falsified against common capture mechanisms: deceit, guile,
flattery, covetous cover, glory-seeking, and chargeability. The positive images
are nurse-gentleness and fatherly exhortation toward worthy walking.

No `sorry`, no new `axiom`.
-/

structure NonFlatteringEntrance where
  entranceNotVain : Bool := true
  boldAfterPhilippiSuffering : Bool := true
  noDeceitUncleannessGuile : Bool := true
  entrustedByGodNotMenPleasing : Bool := true
  noFlatteryCovetousCloak : Bool := true
  noGlorySeeking : Bool := true
deriving DecidableEq, Repr

def nonFlatteringEntrance : NonFlatteringEntrance := {}

def nonFlatteringWitness (n : NonFlatteringEntrance) : Prop :=
  n.entranceNotVain = true ∧ n.boldAfterPhilippiSuffering = true ∧
  n.noDeceitUncleannessGuile = true ∧ n.entrustedByGodNotMenPleasing = true ∧
  n.noFlatteryCovetousCloak = true ∧ n.noGlorySeeking = true

structure NurseFatherMinistry where
  gentleAsNurse : Bool := true
  impartedGospelAndSouls : Bool := true
  laborNightDayNotChargeable : Bool := true
  holyJustUnblameableBehavior : Bool := true
  exhortedComfortedChargedAsFather : Bool := true
  walkWorthyKingdomGlory : Bool := true
deriving DecidableEq, Repr

def nurseFatherMinistry : NurseFatherMinistry := {}

def nurseFatherWitness (m : NurseFatherMinistry) : Prop :=
  m.gentleAsNurse = true ∧ m.impartedGospelAndSouls = true ∧
  m.laborNightDayNotChargeable = true ∧ m.holyJustUnblameableBehavior = true ∧
  m.exhortedComfortedChargedAsFather = true ∧ m.walkWorthyKingdomGlory = true

theorem first_thessalonians_non_flattering :
    nonFlatteringWitness nonFlatteringEntrance := by
  unfold nonFlatteringWitness nonFlatteringEntrance
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_nurse_father :
    nurseFatherWitness nurseFatherMinistry := by
  unfold nurseFatherWitness nurseFatherMinistry
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_nurse_father_ministry_witness :
    nonFlatteringWitness nonFlatteringEntrance ∧
    nurseFatherWitness nurseFatherMinistry := by
  exact ⟨first_thessalonians_non_flattering, first_thessalonians_nurse_father⟩

end FirstThessaloniansNurseFatherMinistryWitness
end Gnosis.Witnesses.Bible.FirstThessalonians
