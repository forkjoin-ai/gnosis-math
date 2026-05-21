import Init

namespace Gnosis.Witnesses.Bible.Titus
namespace TitusGraceTrainingWitness

/-!
# Titus 2 -- Sound Doctrine by Station and Grace Training Good Works

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95851-95884`.

Grace is a teacher, not a permission slip. It trains denial of ungodliness,
sober and righteous living, hope toward appearing, and zeal for good works.
Sound doctrine becomes visible in age, household, work, and speech.

No `sorry`, no new `axiom`.
-/

structure SoundDoctrineEmbodied where
  agedMenSoberFaithCharityPatience : Bool := true
  agedWomenHolyTeachersGoodThings : Bool := true
  youngWomenHouseholdWordNotBlasphemed : Bool := true
  youngMenSoberMinded : Bool := true
  titusPatternGoodWorksDoctrine : Bool := true
  soundSpeechCannotBeCondemned : Bool := true
  servantsAdornDoctrine : Bool := true
deriving DecidableEq, Repr

def soundDoctrineEmbodied : SoundDoctrineEmbodied := {}

def soundDoctrineEmbodiedWitness (s : SoundDoctrineEmbodied) : Prop :=
  s.agedMenSoberFaithCharityPatience = true ∧
  s.agedWomenHolyTeachersGoodThings = true ∧
  s.youngWomenHouseholdWordNotBlasphemed = true ∧
  s.youngMenSoberMinded = true ∧
  s.titusPatternGoodWorksDoctrine = true ∧
  s.soundSpeechCannotBeCondemned = true ∧
  s.servantsAdornDoctrine = true

structure GraceTraining where
  savingGraceAppearedAll : Bool := true
  deniesUngodlinessWorldlyLusts : Bool := true
  soberRighteousGodlyPresentLife : Bool := true
  blessedHopeGloriousAppearing : Bool := true
  gaveSelfRedeemFromIniquity : Bool := true
  purifiedPeculiarPeople : Bool := true
  zealousOfGoodWorks : Bool := true
  speakExhortRebukeAuthority : Bool := true
deriving DecidableEq, Repr

def graceTraining : GraceTraining := {}

def graceTrainingWitness (g : GraceTraining) : Prop :=
  g.savingGraceAppearedAll = true ∧ g.deniesUngodlinessWorldlyLusts = true ∧
  g.soberRighteousGodlyPresentLife = true ∧ g.blessedHopeGloriousAppearing = true ∧
  g.gaveSelfRedeemFromIniquity = true ∧ g.purifiedPeculiarPeople = true ∧
  g.zealousOfGoodWorks = true ∧ g.speakExhortRebukeAuthority = true

theorem titus_sound_doctrine_embodied :
    soundDoctrineEmbodiedWitness soundDoctrineEmbodied := by
  unfold soundDoctrineEmbodiedWitness soundDoctrineEmbodied
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem titus_grace_training :
    graceTrainingWitness graceTraining := by
  unfold graceTrainingWitness graceTraining
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem titus_grace_training_witness :
    soundDoctrineEmbodiedWitness soundDoctrineEmbodied ∧
    graceTrainingWitness graceTraining := by
  exact ⟨titus_sound_doctrine_embodied, titus_grace_training⟩

end TitusGraceTrainingWitness
end Gnosis.Witnesses.Bible.Titus
