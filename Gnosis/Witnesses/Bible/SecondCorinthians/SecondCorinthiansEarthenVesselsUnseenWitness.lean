import Init

namespace Gnosis.Witnesses.Bible.SecondCorinthians
namespace SecondCorinthiansEarthenVesselsUnseenWitness

/-! # 2 Corinthians 4 -- Earthen Vessels and Unseen Glory
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92977-93025`. -/

structure EarthenVesselsUnseen where
  ministryMercyFaintNot : Bool
  truthManifestedNotCraftDeceit : Bool
  gospelHidToLostBlindedMinds : Bool
  preachChristNotOurselves : Bool
  lightKnowledgeGloryFaceChrist : Bool
  treasureEarthenVesselsPowerOfGod : Bool
  troubledNotDistressedPersecutedNotForsaken : Bool
  dyingJesusLifeManifest : Bool
  raisedWithJesusPresentedWithYou : Bool
  outwardPerishInwardRenewedUnseenEternal : Bool
deriving DecidableEq, Repr

def earthenVesselsUnseen : EarthenVesselsUnseen where
  ministryMercyFaintNot := true
  truthManifestedNotCraftDeceit := true
  gospelHidToLostBlindedMinds := true
  preachChristNotOurselves := true
  lightKnowledgeGloryFaceChrist := true
  treasureEarthenVesselsPowerOfGod := true
  troubledNotDistressedPersecutedNotForsaken := true
  dyingJesusLifeManifest := true
  raisedWithJesusPresentedWithYou := true
  outwardPerishInwardRenewedUnseenEternal := true

theorem second_corinthians_earthen_vessels_unseen_witness :
    earthenVesselsUnseen.ministryMercyFaintNot = true
    ∧ earthenVesselsUnseen.truthManifestedNotCraftDeceit = true
    ∧ earthenVesselsUnseen.gospelHidToLostBlindedMinds = true
    ∧ earthenVesselsUnseen.preachChristNotOurselves = true
    ∧ earthenVesselsUnseen.lightKnowledgeGloryFaceChrist = true
    ∧ earthenVesselsUnseen.treasureEarthenVesselsPowerOfGod = true
    ∧ earthenVesselsUnseen.troubledNotDistressedPersecutedNotForsaken = true
    ∧ earthenVesselsUnseen.dyingJesusLifeManifest = true
    ∧ earthenVesselsUnseen.raisedWithJesusPresentedWithYou = true
    ∧ earthenVesselsUnseen.outwardPerishInwardRenewedUnseenEternal = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SecondCorinthiansEarthenVesselsUnseenWitness
end Gnosis.Witnesses.Bible.SecondCorinthians
