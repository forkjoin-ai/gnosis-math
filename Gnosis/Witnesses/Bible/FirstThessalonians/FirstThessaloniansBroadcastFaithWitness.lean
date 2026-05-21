import Init

namespace Gnosis.Witnesses.Bible.FirstThessalonians
namespace FirstThessaloniansBroadcastFaithWitness

/-!
# 1 Thessalonians 1:1-10 -- Broadcast Faith, Afflicted Joy, and Idol Turn

Source text: `docs/ebooks/source-texts/bible-kjv.txt:94886-94921`.

The Thessalonian witness propagates without explanation overhead: work of faith,
labor of love, patience of hope, power-and-Spirit reception, affliction with joy,
and faith sounding out everywhere.

No `sorry`, no new `axiom`.
-/

structure BroadcastFaith where
  churchInFatherAndLord : Bool := true
  workFaithLaborLovePatienceHope : Bool := true
  electionKnown : Bool := true
  gospelPowerSpiritAssurance : Bool := true
  afflictionWithHolyGhostJoy : Bool := true
  ensamplesInMacedoniaAchaia : Bool := true
  wordSoundedOutEverywhere : Bool := true
  turnedFromIdolsToLivingGod : Bool := true
  waitForRisenDeliveringSon : Bool := true
deriving DecidableEq, Repr

def broadcastFaith : BroadcastFaith := {}

def broadcastFaithWitness (b : BroadcastFaith) : Prop :=
  b.churchInFatherAndLord = true ∧ b.workFaithLaborLovePatienceHope = true ∧
  b.electionKnown = true ∧ b.gospelPowerSpiritAssurance = true ∧
  b.afflictionWithHolyGhostJoy = true ∧ b.ensamplesInMacedoniaAchaia = true ∧
  b.wordSoundedOutEverywhere = true ∧ b.turnedFromIdolsToLivingGod = true ∧
  b.waitForRisenDeliveringSon = true

theorem first_thessalonians_broadcast_faith :
    broadcastFaithWitness broadcastFaith := by
  unfold broadcastFaithWitness broadcastFaith
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstThessaloniansBroadcastFaithWitness
end Gnosis.Witnesses.Bible.FirstThessalonians
