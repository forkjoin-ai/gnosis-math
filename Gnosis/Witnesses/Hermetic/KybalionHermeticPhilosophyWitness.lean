import Gnosis.Witnesses.Hermetic.KybalionTransmissionWitness

namespace Gnosis.Witnesses.Hermetic

/-!
# Kybalion Hermetic Philosophy Witness

Witness ledger for `docs/ebooks/source-texts/kybalion-three-initiates.txt`,
chapter 1, "The Hermetic Philosophy".
-/

structure HermesLineage where
  egyptAsHiddenWisdomSource : Bool := true
  mastersTransmitToPrepared : Bool := true
  hermesAsMasterOfMasters : Bool := true
  thothHermesWisdomLineage : Bool := true
  fountOfWisdomMemory : Bool := true
deriving Repr, DecidableEq

structure SealedTeaching where
  hermeticMeansSealed : Bool := true
  secrecyPreventsEscape : Bool := true
  milkForBabesMeatForStrong : Bool := true
  occultismLostWhenPriesthoodMixedTheology : Bool := true
  philosophySmotheredByTheology : Bool := true
  guardedTransmissionPreservesEssence : Bool := true
deriving Repr, DecidableEq

structure MentalAlchemy where
  kybalionAsBasicAxiomCollection : Bool := true
  outsidersDoNotUnderstandWithoutKey : Bool := true
  trueAlchemyMastersMentalForces : Bool := true
  mentalVibrationsTransmuted : Bool := true
  metalToGoldAsAllegory : Bool := true
  studentMustApplyPrinciples : Bool := true
deriving Repr, DecidableEq

def hermesLineage : HermesLineage := {}
def sealedTeaching : SealedTeaching := {}
def mentalAlchemy : MentalAlchemy := {}

theorem kybalion_hermes_lineage :
    hermesLineage.egyptAsHiddenWisdomSource = true ∧
      hermesLineage.mastersTransmitToPrepared = true ∧
      hermesLineage.hermesAsMasterOfMasters = true ∧
      hermesLineage.thothHermesWisdomLineage = true ∧
      hermesLineage.fountOfWisdomMemory = true := by
  simp [hermesLineage]

theorem kybalion_sealed_teaching :
    sealedTeaching.hermeticMeansSealed = true ∧
      sealedTeaching.secrecyPreventsEscape = true ∧
      sealedTeaching.milkForBabesMeatForStrong = true ∧
      sealedTeaching.occultismLostWhenPriesthoodMixedTheology = true ∧
      sealedTeaching.philosophySmotheredByTheology = true ∧
      sealedTeaching.guardedTransmissionPreservesEssence = true := by
  simp [sealedTeaching]

theorem kybalion_mental_alchemy :
    mentalAlchemy.kybalionAsBasicAxiomCollection = true ∧
      mentalAlchemy.outsidersDoNotUnderstandWithoutKey = true ∧
      mentalAlchemy.trueAlchemyMastersMentalForces = true ∧
      mentalAlchemy.mentalVibrationsTransmuted = true ∧
      mentalAlchemy.metalToGoldAsAllegory = true ∧
      mentalAlchemy.studentMustApplyPrinciples = true := by
  simp [mentalAlchemy]

theorem kybalion_hermetic_philosophy_witness :
    hermesLineage.hermesAsMasterOfMasters = true ∧
      sealedTeaching.hermeticMeansSealed = true ∧
      sealedTeaching.occultismLostWhenPriesthoodMixedTheology = true ∧
      mentalAlchemy.trueAlchemyMastersMentalForces = true ∧
      mentalAlchemy.mentalVibrationsTransmuted = true ∧
      mentalAlchemy.metalToGoldAsAllegory = true := by
  simp [hermesLineage, sealedTeaching, mentalAlchemy]

end Gnosis.Witnesses.Hermetic
