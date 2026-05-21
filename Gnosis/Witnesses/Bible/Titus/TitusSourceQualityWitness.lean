import Gnosis.Witnesses.Bible.Titus.TitusEldersVainTalkersWitness
import Gnosis.Witnesses.Bible.Titus.TitusGraceTrainingWitness
import Gnosis.Witnesses.Bible.Titus.TitusRegenerationGoodWorksWitness

namespace Gnosis.Witnesses.Bible.Titus
namespace TitusSourceQualityWitness

/-!
# Titus -- Source Quality Spine

Book invariant: sound doctrine orders a community toward profitable good works.
Titus is not just a church-order checklist; it is a Crete repair protocol where
truth after godliness appoints tested elders, stops subverting talk, trains
visible conduct by grace, and keeps believers fruitful for necessary uses.

Primary gap/counterproof: vain talk simulates doctrine while producing household
subversion, filthy-lucre teaching, fables, commandments turning from truth, and
law-strife. Works then become the test: professed knowledge of God is falsified
by reprobate works.

Unseen sat: grace trains. It does not merely pardon; it produces sober,
righteous, godly life and zeal for good works without making those works the
ground of mercy.

No `sorry`, no new `axiom`.
-/

structure TitusInvariant where
  truthAfterGodlinessOrdersCrete : Bool := true
  eldersHoldFaithfulWord : Bool := true
  graceTrainsVisibleGoodWorks : Bool := true
  mercyGroundsProfitableWorks : Bool := true
deriving DecidableEq, Repr

def titusInvariant : TitusInvariant := {}

def orderedDoctrineInvariant (i : TitusInvariant) : Prop :=
  i.truthAfterGodlinessOrdersCrete = true ∧
  i.eldersHoldFaithfulWord = true ∧
  i.graceTrainsVisibleGoodWorks = true ∧
  i.mercyGroundsProfitableWorks = true

structure TitusCounterproof where
  vainTalkCannotOrderHouseholds : Bool := true
  filthyLucreCannotTeachSoundDoctrine : Bool := true
  fablesCannotRemainTruthFacing : Bool := true
  professionWithoutWorksDeniesGod : Bool := true
  lawStrifeCannotBeProfitable : Bool := true
deriving DecidableEq, Repr

def titusCounterproof : TitusCounterproof := {}

def vainDoctrineRejected (c : TitusCounterproof) : Prop :=
  c.vainTalkCannotOrderHouseholds = true ∧
  c.filthyLucreCannotTeachSoundDoctrine = true ∧
  c.fablesCannotRemainTruthFacing = true ∧
  c.professionWithoutWorksDeniesGod = true ∧
  c.lawStrifeCannotBeProfitable = true

theorem titus_quality_invariant :
    orderedDoctrineInvariant titusInvariant := by
  unfold orderedDoctrineInvariant titusInvariant
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem titus_quality_counterproof :
    vainDoctrineRejected titusCounterproof := by
  unfold vainDoctrineRejected titusCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem titus_source_quality_witness :
    orderedDoctrineInvariant titusInvariant ∧
    vainDoctrineRejected titusCounterproof ∧
    TitusEldersVainTalkersWitness.orderedEldersWitness
      TitusEldersVainTalkersWitness.orderedElders ∧
    TitusEldersVainTalkersWitness.vainTalkerRejected
      TitusEldersVainTalkersWitness.vainTalkerCounterproof ∧
    TitusGraceTrainingWitness.graceTrainingWitness
      TitusGraceTrainingWitness.graceTraining ∧
    TitusRegenerationGoodWorksWitness.profitableWorksWitness
      TitusRegenerationGoodWorksWitness.profitableWorksBoundary := by
  exact ⟨titus_quality_invariant,
    titus_quality_counterproof,
    TitusEldersVainTalkersWitness.titus_ordered_elders,
    TitusEldersVainTalkersWitness.titus_vain_talker_rejected,
    TitusGraceTrainingWitness.titus_grace_training,
    TitusRegenerationGoodWorksWitness.titus_profitable_works⟩

end TitusSourceQualityWitness
end Gnosis.Witnesses.Bible.Titus
