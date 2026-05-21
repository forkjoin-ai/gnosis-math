import Gnosis.Witnesses.Bible.SecondTimothy.SecondTimothyFinalChargeCrownWitness
import Gnosis.Witnesses.Bible.SecondTimothy.SecondTimothyPerilScriptureWitness
import Gnosis.Witnesses.Bible.SecondTimothy.SecondTimothySoundMindDepositWitness
import Gnosis.Witnesses.Bible.SecondTimothy.SecondTimothyUnboundWordWorkmanWitness

namespace Gnosis.Witnesses.Bible.SecondTimothy
namespace SecondTimothySourceQualityWitness

/-!
# 2 Timothy -- Source Quality Spine

Book invariant: the deposit must be guarded and transmitted under abandonment
pressure. Fear, shame, bonds, desertion, false teaching, and death-nearness do
not interrupt the witness; they reveal whether sound words are actually held.

Primary gap/counterproof: false godliness has form without power, learning
without truth, word-strife without profit, and ear-driven teachers without sound
doctrine. The answer is not novelty but remembered faith, unbound word, approved
work, Scripture sufficiency, and final charge.

Unseen sat: the witness becomes most legible when ordinary supports vanish. At
first defense no one stands with Paul, yet the Lord stands; this is the closing
shape of guarded deposit.

No `sorry`, no new `axiom`.
-/

structure SecondTimothyInvariant where
  depositGuardedBySpirit : Bool := true
  wordUnboundUnderBonds : Bool := true
  scriptureFurnishesWorker : Bool := true
  finalChargeHoldsUnderDesertion : Bool := true
deriving DecidableEq, Repr

def secondTimothyInvariant : SecondTimothyInvariant := {}

def guardedDepositInvariant (i : SecondTimothyInvariant) : Prop :=
  i.depositGuardedBySpirit = true ∧
  i.wordUnboundUnderBonds = true ∧
  i.scriptureFurnishesWorker = true ∧
  i.finalChargeHoldsUnderDesertion = true

structure SecondTimothyCounterproof where
  fearCannotGovernGift : Bool := true
  wordStrifeCannotDivideTruthRightly : Bool := true
  formWithoutPowerCannotBeGodliness : Bool := true
  itchingEarsCannotEndureSoundDoctrine : Bool := true
  presentWorldLoveCannotFinishCourse : Bool := true
deriving DecidableEq, Repr

def secondTimothyCounterproof : SecondTimothyCounterproof := {}

def depositCounterfeitsRejected (c : SecondTimothyCounterproof) : Prop :=
  c.fearCannotGovernGift = true ∧
  c.wordStrifeCannotDivideTruthRightly = true ∧
  c.formWithoutPowerCannotBeGodliness = true ∧
  c.itchingEarsCannotEndureSoundDoctrine = true ∧
  c.presentWorldLoveCannotFinishCourse = true

theorem second_timothy_quality_invariant :
    guardedDepositInvariant secondTimothyInvariant := by
  unfold guardedDepositInvariant secondTimothyInvariant
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem second_timothy_quality_counterproof :
    depositCounterfeitsRejected secondTimothyCounterproof := by
  unfold depositCounterfeitsRejected secondTimothyCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem second_timothy_source_quality_witness :
    guardedDepositInvariant secondTimothyInvariant ∧
    depositCounterfeitsRejected secondTimothyCounterproof ∧
    SecondTimothySoundMindDepositWitness.guardedDepositWitness
      SecondTimothySoundMindDepositWitness.guardedDeposit ∧
    SecondTimothyUnboundWordWorkmanWitness.unboundWordWitness
      SecondTimothyUnboundWordWorkmanWitness.enduringTransmission ∧
    SecondTimothyPerilScriptureWitness.scriptureSufficiencyWitness
      SecondTimothyPerilScriptureWitness.scriptureSufficiency ∧
    SecondTimothyFinalChargeCrownWitness.finalChargeWitness
      SecondTimothyFinalChargeCrownWitness.finalCharge := by
  exact ⟨second_timothy_quality_invariant,
    second_timothy_quality_counterproof,
    SecondTimothySoundMindDepositWitness.second_timothy_guarded_deposit,
    SecondTimothyUnboundWordWorkmanWitness.second_timothy_unbound_word,
    SecondTimothyPerilScriptureWitness.second_timothy_scripture_sufficiency,
    SecondTimothyFinalChargeCrownWitness.second_timothy_final_charge⟩

end SecondTimothySourceQualityWitness
end Gnosis.Witnesses.Bible.SecondTimothy
