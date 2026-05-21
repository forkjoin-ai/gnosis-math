import Init

namespace Gnosis.Witnesses.Bible.FirstThessalonians
namespace FirstThessaloniansAfflictionStandfastWitness

/-!
# 1 Thessalonians 3:1-13 -- Affliction Stabilization and Abounding Love

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94988-95031`.

Timothy is sent as a stabilization worker: establish, comfort, and test faith
under affliction. The return signal is faith, charity, remembrance, and standing
fast, then a prayer for perfected lack and abounding love.

No `sorry`, no new `axiom`.
-/

structure AfflictionStabilization where
  timothySentToEstablishComfort : Bool := true
  noManMovedByAfflictions : Bool := true
  afflictionAppointmentKnown : Bool := true
  tribulationForetoldAndCame : Bool := true
  tempterRiskAndVainLabor : Bool := true
  goodTidingsFaithCharity : Bool := true
  comfortedByTheirFaith : Bool := true
  standfastMeansLife : Bool := true
deriving DecidableEq, Repr

def afflictionStabilization : AfflictionStabilization := {}

def afflictionStandfastWitness (a : AfflictionStabilization) : Prop :=
  a.timothySentToEstablishComfort = true ∧ a.noManMovedByAfflictions = true ∧
  a.afflictionAppointmentKnown = true ∧ a.tribulationForetoldAndCame = true ∧
  a.tempterRiskAndVainLabor = true ∧ a.goodTidingsFaithCharity = true ∧
  a.comfortedByTheirFaith = true ∧ a.standfastMeansLife = true

structure PerfectingLovePrayer where
  thanksJoyBeforeGod : Bool := true
  nightDayPrayerToSeeFace : Bool := true
  perfectLackingFaith : Bool := true
  wayDirectedByFatherAndLord : Bool := true
  increaseAboundLoveAll : Bool := true
  heartsEstablishedUnblameableHoliness : Bool := true
  comingWithAllSaints : Bool := true
deriving DecidableEq, Repr

def perfectingLovePrayer : PerfectingLovePrayer := {}

def perfectingLoveWitness (p : PerfectingLovePrayer) : Prop :=
  p.thanksJoyBeforeGod = true ∧ p.nightDayPrayerToSeeFace = true ∧
  p.perfectLackingFaith = true ∧ p.wayDirectedByFatherAndLord = true ∧
  p.increaseAboundLoveAll = true ∧ p.heartsEstablishedUnblameableHoliness = true ∧
  p.comingWithAllSaints = true

theorem first_thessalonians_affliction_standfast :
    afflictionStandfastWitness afflictionStabilization := by
  unfold afflictionStandfastWitness afflictionStabilization
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_perfecting_love :
    perfectingLoveWitness perfectingLovePrayer := by
  unfold perfectingLoveWitness perfectingLovePrayer
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_thessalonians_affliction_standfast_witness :
    afflictionStandfastWitness afflictionStabilization ∧
    perfectingLoveWitness perfectingLovePrayer := by
  exact ⟨first_thessalonians_affliction_standfast, first_thessalonians_perfecting_love⟩

end FirstThessaloniansAfflictionStandfastWitness
end Gnosis.Witnesses.Bible.FirstThessalonians
