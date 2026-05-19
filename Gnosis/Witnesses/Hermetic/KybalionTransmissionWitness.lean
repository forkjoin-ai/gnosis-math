import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Hermetic

/-!
# Kybalion Transmission Witness

Witness ledger for `docs/ebooks/source-texts/kybalion-three-initiates.txt`,
the introduction.
-/

structure MasterKeyTransmission where
  reconcilesOpposedFragments : Bool := true
  notNewTempleButMasterKey : Bool := true
  innerDoorsOpened : Bool := true
  secretDoctrineGuarded : Bool := true
  correspondenceUnderDivergence : Bool := true
  seedTruthManyForms : Bool := true
deriving Repr, DecidableEq

structure ReadinessGate where
  strongMeatReservedForReady : Bool := true
  pearlsNotCastBeforeUnready : Bool := true
  lipsClosedExceptUnderstanding : Bool := true
  footstepsOpenReadyEars : Bool := true
  readyStudentAttractsTeaching : Bool := true
  causeEffectBringsLipsAndEar : Bool := true
deriving Repr, DecidableEq

structure AntiCreedGuard where
  doctrineNotCrystallizedIntoCreed : Bool := true
  theologyBlanketSmothersPhilosophy : Bool := true
  flameKeptAliveByFew : Bool := true
  writtenMeaningVeiledByAlchemyAstrology : Bool := true
  mentalForcesPrimaryAlchemy : Bool := true
  wordsWithoutReadinessStayWords : Bool := true
deriving Repr, DecidableEq

def masterKeyTransmission : MasterKeyTransmission := {}
def readinessGate : ReadinessGate := {}
def antiCreedGuard : AntiCreedGuard := {}

theorem kybalion_master_key_transmission :
    masterKeyTransmission.reconcilesOpposedFragments = true ∧
      masterKeyTransmission.notNewTempleButMasterKey = true ∧
      masterKeyTransmission.innerDoorsOpened = true ∧
      masterKeyTransmission.secretDoctrineGuarded = true ∧
      masterKeyTransmission.correspondenceUnderDivergence = true ∧
      masterKeyTransmission.seedTruthManyForms = true := by
  simp [masterKeyTransmission]

theorem kybalion_readiness_gate :
    readinessGate.strongMeatReservedForReady = true ∧
      readinessGate.pearlsNotCastBeforeUnready = true ∧
      readinessGate.lipsClosedExceptUnderstanding = true ∧
      readinessGate.footstepsOpenReadyEars = true ∧
      readinessGate.readyStudentAttractsTeaching = true ∧
      readinessGate.causeEffectBringsLipsAndEar = true := by
  simp [readinessGate]

theorem kybalion_anti_creed_guard :
    antiCreedGuard.doctrineNotCrystallizedIntoCreed = true ∧
      antiCreedGuard.theologyBlanketSmothersPhilosophy = true ∧
      antiCreedGuard.flameKeptAliveByFew = true ∧
      antiCreedGuard.writtenMeaningVeiledByAlchemyAstrology = true ∧
      antiCreedGuard.mentalForcesPrimaryAlchemy = true ∧
      antiCreedGuard.wordsWithoutReadinessStayWords = true := by
  simp [antiCreedGuard]

theorem kybalion_transmission_witness :
    masterKeyTransmission.reconcilesOpposedFragments = true ∧
      readinessGate.lipsClosedExceptUnderstanding = true ∧
      readinessGate.causeEffectBringsLipsAndEar = true ∧
      antiCreedGuard.doctrineNotCrystallizedIntoCreed = true ∧
      antiCreedGuard.mentalForcesPrimaryAlchemy = true ∧
      antiCreedGuard.wordsWithoutReadinessStayWords = true := by
  simp [masterKeyTransmission, readinessGate, antiCreedGuard]

end Gnosis.Witnesses.Hermetic
