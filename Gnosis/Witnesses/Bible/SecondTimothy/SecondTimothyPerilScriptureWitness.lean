import Init

namespace Gnosis.Witnesses.Bible.SecondTimothy
namespace SecondTimothyPerilScriptureWitness

/-!
# 2 Timothy 3 -- Perilous Times, Form Without Power, and Scripture Sufficiency

Source text: `docs/ebooks/source-texts/bible-kjv.txt:95692-95738`.

The chapter names a counterfeit godliness: form without power, ever learning
without truth. Timothy's counter-path is known doctrine and Scripture that makes
wise unto salvation and furnishes the worker.

No `sorry`, no new `axiom`.
-/

structure PerilousCounterfeit where
  perilousTimesCome : Bool := true
  selfLovePleasureMoreThanGod : Bool := true
  formGodlinessDenyPower : Bool := true
  captiveHouseholdPredation : Bool := true
  everLearningNeverTruth : Bool := true
  jannesJambresResistTruth : Bool := true
  follyManifestLimit : Bool := true
deriving DecidableEq, Repr

def perilousCounterfeit : PerilousCounterfeit := {}

def perilousCounterfeitWitness (p : PerilousCounterfeit) : Prop :=
  p.perilousTimesCome = true ∧
  p.selfLovePleasureMoreThanGod = true ∧
  p.formGodlinessDenyPower = true ∧
  p.captiveHouseholdPredation = true ∧
  p.everLearningNeverTruth = true ∧
  p.jannesJambresResistTruth = true ∧
  p.follyManifestLimit = true

structure ScriptureSufficiency where
  doctrineLifePurposeKnown : Bool := true
  persecutionsEnduredDelivered : Bool := true
  godlyLifeSuffersPersecution : Bool := true
  deceiversWaxWorse : Bool := true
  continueLearnedAssured : Bool := true
  childhoodScripturesKnown : Bool := true
  scripturesWiseUntoSalvation : Bool := true
  allScriptureInspiredProfitable : Bool := true
  manOfGodFurnishedGoodWorks : Bool := true
deriving DecidableEq, Repr

def scriptureSufficiency : ScriptureSufficiency := {}

def scriptureSufficiencyWitness (s : ScriptureSufficiency) : Prop :=
  s.doctrineLifePurposeKnown = true ∧
  s.persecutionsEnduredDelivered = true ∧
  s.godlyLifeSuffersPersecution = true ∧
  s.deceiversWaxWorse = true ∧
  s.continueLearnedAssured = true ∧
  s.childhoodScripturesKnown = true ∧
  s.scripturesWiseUntoSalvation = true ∧
  s.allScriptureInspiredProfitable = true ∧
  s.manOfGodFurnishedGoodWorks = true

theorem second_timothy_perilous_counterfeit :
    perilousCounterfeitWitness perilousCounterfeit := by
  unfold perilousCounterfeitWitness perilousCounterfeit
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_timothy_scripture_sufficiency :
    scriptureSufficiencyWitness scriptureSufficiency := by
  unfold scriptureSufficiencyWitness scriptureSufficiency
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_timothy_peril_scripture_witness :
    perilousCounterfeitWitness perilousCounterfeit ∧
    scriptureSufficiencyWitness scriptureSufficiency := by
  exact ⟨second_timothy_perilous_counterfeit,
    second_timothy_scripture_sufficiency⟩

end SecondTimothyPerilScriptureWitness
end Gnosis.Witnesses.Bible.SecondTimothy
