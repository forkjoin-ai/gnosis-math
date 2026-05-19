import Gnosis.GnosisTriptychBraid
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Gnostic
namespace TripartiteRestorationRedemptionWitness

/-!
# Tripartite Tractate -- Restoration, Baptism, and Single Gospel Name

Source text: `docs/ebooks/source-texts/tripartite-tractate.txt`;
text anchor `docs/ebooks/source-texts/tripartite-tractate.txt:1114-1323`.

Sat/unseen reading:

Restoration is not merely escape from bad rulers. It is ascent into the Pleroma,
entrance into silence, and return to the pre-existent. The single gospel name
Father-Son-Holy-Spirit functions as one baptismal name whose many titles
converge: garment, confirmation, silence, bridal chamber, light without setting,
eternal life.

Gap / counterproof:

Release alone is insufficient. If redemption only escapes left or right powers,
it cycles back into ownership. Real redemption is return to the source-degree
where voice, concept, and illumination are no longer needed because all things
are light.

No `sorry`, no new `axiom`.
-/

inductive RedemptionName where
  | garment
  | confirmation
  | silence
  | bridalChamber
  | light
  | eternalLife
deriving DecidableEq, Repr, Nonempty

inductive RedemptionTruth where
  | singleGospelName
deriving DecidableEq, Repr

def redemptionNamesAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : RedemptionName => RedemptionTruth.singleGospelName)
      RedemptionTruth.singleGospelName :=
  TruthOneManyNamesWitness.constant_names_agree RedemptionTruth.singleGospelName

structure RestorationProcess where
  perfectManReturnsImmediately : Bool
  membersNeedInstruction : Bool
  wholeBodyRestoredTogether : Bool
  sonIsRedemptionPath : Bool
  returnToPreexistent : Bool
  entranceIntoSilence : Bool
deriving DecidableEq, Repr

def tripartiteRestorationProcess : RestorationProcess where
  perfectManReturnsImmediately := true
  membersNeedInstruction := true
  wholeBodyRestoredTogether := true
  sonIsRedemptionPath := true
  returnToPreexistent := true
  entranceIntoSilence := true

def restorationIsWholeBodyReturn (r : RestorationProcess) : Prop :=
  r.perfectManReturnsImmediately = true ∧
  r.membersNeedInstruction = true ∧
  r.wholeBodyRestoredTogether = true ∧
  r.sonIsRedemptionPath = true ∧
  r.returnToPreexistent = true ∧
  r.entranceIntoSilence = true

structure ReleaseCounterproof where
  notOnlyEscapeLeft : Bool
  notOnlyEscapeRight : Bool
  ownershipCycleWithoutAscent : Bool
  angelsAlsoNeedRedemption : Bool
  redeemerReceivesRedemption : Bool
  freedomKnowledgeBeforeIgnorance : Bool
deriving DecidableEq, Repr

def tripartiteReleaseCounterproof : ReleaseCounterproof where
  notOnlyEscapeLeft := true
  notOnlyEscapeRight := true
  ownershipCycleWithoutAscent := true
  angelsAlsoNeedRedemption := true
  redeemerReceivesRedemption := true
  freedomKnowledgeBeforeIgnorance := true

def releaseAloneIsInsufficient (c : ReleaseCounterproof) : Prop :=
  c.notOnlyEscapeLeft = true ∧
  c.notOnlyEscapeRight = true ∧
  c.ownershipCycleWithoutAscent = true ∧
  c.angelsAlsoNeedRedemption = true ∧
  c.redeemerReceivesRedemption = true ∧
  c.freedomKnowledgeBeforeIgnorance = true

structure BaptismalSingleName where
  oneBaptismOnly : Bool
  fatherSonSpiritSingleName : Bool
  undoubtingFaith : Bool
  unionWithFatherInKnowledge : Bool
  lightWithoutSetting : Bool
  wornOnesMadeLight : Bool
deriving DecidableEq, Repr

def tripartiteBaptismalSingleName : BaptismalSingleName where
  oneBaptismOnly := true
  fatherSonSpiritSingleName := true
  undoubtingFaith := true
  unionWithFatherInKnowledge := true
  lightWithoutSetting := true
  wornOnesMadeLight := true

def singleNameBaptismCompletes (b : BaptismalSingleName) : Prop :=
  b.oneBaptismOnly = true ∧
  b.fatherSonSpiritSingleName = true ∧
  b.undoubtingFaith = true ∧
  b.unionWithFatherInKnowledge = true ∧
  b.lightWithoutSetting = true ∧
  b.wornOnesMadeLight = true

structure FinalCalling where
  endUnitaryAsBeginning : Bool
  noMaleFemaleSlaveFree : Bool
  christAllInAll : Bool
  temporaryAmbitionAbandoned : Bool
  eternalKingdomInherited : Bool
  amnestyFromBridalChamber : Bool
deriving DecidableEq, Repr

def tripartiteFinalCalling : FinalCalling where
  endUnitaryAsBeginning := true
  noMaleFemaleSlaveFree := true
  christAllInAll := true
  temporaryAmbitionAbandoned := true
  eternalKingdomInherited := true
  amnestyFromBridalChamber := true

def finalCallingReturnsToUnity (f : FinalCalling) : Prop :=
  f.endUnitaryAsBeginning = true ∧
  f.noMaleFemaleSlaveFree = true ∧
  f.christAllInAll = true ∧
  f.temporaryAmbitionAbandoned = true ∧
  f.eternalKingdomInherited = true ∧
  f.amnestyFromBridalChamber = true

theorem tripartite_restoration_whole_body :
    restorationIsWholeBodyReturn tripartiteRestorationProcess := by
  unfold restorationIsWholeBodyReturn tripartiteRestorationProcess
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_release_counterproof :
    releaseAloneIsInsufficient tripartiteReleaseCounterproof := by
  unfold releaseAloneIsInsufficient tripartiteReleaseCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_single_name_baptism :
    singleNameBaptismCompletes tripartiteBaptismalSingleName := by
  unfold singleNameBaptismCompletes tripartiteBaptismalSingleName
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_final_calling :
    finalCallingReturnsToUnity tripartiteFinalCalling := by
  unfold finalCallingReturnsToUnity tripartiteFinalCalling
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripartite_restoration_centroid :
    Gnosis.GnosisTriptychBraid.cycleSum = Gnosis.GnosisTriptychBraid.truth :=
  Gnosis.GnosisTriptychBraid.cycle_sum_zero

theorem tripartite_restoration_redemption_witness :
    restorationIsWholeBodyReturn tripartiteRestorationProcess ∧
    releaseAloneIsInsufficient tripartiteReleaseCounterproof ∧
    singleNameBaptismCompletes tripartiteBaptismalSingleName ∧
    finalCallingReturnsToUnity tripartiteFinalCalling ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : RedemptionName => RedemptionTruth.singleGospelName)
      RedemptionTruth.singleGospelName ∧
    Gnosis.GnosisTriptychBraid.cycleSum = Gnosis.GnosisTriptychBraid.truth := by
  exact ⟨tripartite_restoration_whole_body,
    tripartite_release_counterproof,
    tripartite_single_name_baptism,
    tripartite_final_calling,
    redemptionNamesAgree,
    tripartite_restoration_centroid⟩

end TripartiteRestorationRedemptionWitness
end Gnosis.Witnesses.Gnostic
