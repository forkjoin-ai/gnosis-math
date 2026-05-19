import Gnosis.GnosisTriptychBraid

namespace Gnosis.Witnesses.Gnostic
namespace GospelThomasLivingPresenceWitness

/-!
# Gospel of Thomas -- Living Presence Over Dead Archive

Source text: `docs/ebooks/source-texts/gospel-of-thomas.txt`;
text anchor `docs/ebooks/source-texts/gospel-of-thomas.txt:161-245`.

Sat/unseen reading:

Thomas privileges the living one in front of the seeker over archive citation.
Twenty-four prophets may speak "in" Jesus, but the disciples omit the one alive
in their presence. The same cluster names origin-return, movement/repose, and
the corpse-status of the world.

Gap / counterproof:

Dead archive without living recognition is a deficit. Knowing the All while
retaining personal deficiency is complete deficiency.

No `sorry`, no new `axiom`.
-/

structure LivingPresence where
  livingOnePresent : Bool
  deadArchiveOmittedLiving : Bool
  trueCircumcisionSpirit : Bool
  worldCorpseRecognized : Bool
  livingOneBeforeDeath : Bool
deriving DecidableEq, Repr

def thomasLivingPresence : LivingPresence where
  livingOnePresent := true
  deadArchiveOmittedLiving := true
  trueCircumcisionSpirit := true
  worldCorpseRecognized := true
  livingOneBeforeDeath := true

def livingPresenceOutranksArchive (p : LivingPresence) : Prop :=
  p.livingOnePresent = true ∧
  p.deadArchiveOmittedLiving = true ∧
  p.trueCircumcisionSpirit = true ∧
  p.worldCorpseRecognized = true ∧
  p.livingOneBeforeDeath = true

structure OriginSign where
  cameFromLight : Bool
  lightSelfEstablished : Bool
  childrenOfLivingFather : Bool
  movementAndRepose : Bool
  fromKingdomReturnToKingdom : Bool
deriving DecidableEq, Repr

def thomasOriginSign : OriginSign where
  cameFromLight := true
  lightSelfEstablished := true
  childrenOfLivingFather := true
  movementAndRepose := true
  fromKingdomReturnToKingdom := true

def originReturnSign (s : OriginSign) : Prop :=
  s.cameFromLight = true ∧
  s.lightSelfEstablished = true ∧
  s.childrenOfLivingFather = true ∧
  s.movementAndRepose = true ∧
  s.fromKingdomReturnToKingdom = true

structure DeficiencyCounterproof where
  knowsAll : Bool
  stillDeficient : Bool
  completelyDeficient : Bool
  bringForthWithinSaves : Bool
  absentWithinKills : Bool
deriving DecidableEq, Repr

def thomasDeficiencyCounterproof : DeficiencyCounterproof where
  knowsAll := true
  stillDeficient := true
  completelyDeficient := true
  bringForthWithinSaves := true
  absentWithinKills := true

def allKnowledgeWithDeficiencyFails (d : DeficiencyCounterproof) : Prop :=
  d.knowsAll = true ∧
  d.stillDeficient = true ∧
  d.completelyDeficient = true ∧
  d.bringForthWithinSaves = true ∧
  d.absentWithinKills = true

theorem thomas_living_presence :
    livingPresenceOutranksArchive thomasLivingPresence := by
  unfold livingPresenceOutranksArchive thomasLivingPresence
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_origin_return_sign :
    originReturnSign thomasOriginSign := by
  unfold originReturnSign thomasOriginSign
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_deficiency_counterproof :
    allKnowledgeWithDeficiencyFails thomasDeficiencyCounterproof := by
  unfold allKnowledgeWithDeficiencyFails thomasDeficiencyCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem thomas_living_presence_recovery :
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom :=
  Gnosis.GnosisTriptychBraid.two_step_recovery

theorem gospel_thomas_living_presence_witness :
    livingPresenceOutranksArchive thomasLivingPresence ∧
    originReturnSign thomasOriginSign ∧
    allKnowledgeWithDeficiencyFails thomasDeficiencyCounterproof ∧
    Gnosis.GnosisTriptychBraid.iterateTriptych 2 Gnosis.GnosisTriptychBraid.failure =
      Gnosis.GnosisTriptychBraid.wisdom := by
  exact ⟨thomas_living_presence,
    thomas_origin_return_sign,
    thomas_deficiency_counterproof,
    thomas_living_presence_recovery⟩

end GospelThomasLivingPresenceWitness
end Gnosis.Witnesses.Gnostic
