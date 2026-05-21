import Gnosis.Witnesses.Bible.James.JamesTestingDoingWitness
import Gnosis.Witnesses.Bible.James.JamesPartialityWorksWitness
import Gnosis.Witnesses.Bible.James.JamesTongueWisdomWitness
import Gnosis.Witnesses.Bible.James.JamesWarVaporWitness
import Gnosis.Witnesses.Bible.James.JamesRustPrayerWitness

namespace Gnosis.Witnesses.Bible.James
namespace JamesSourceQualityWitness

/-!
# James -- Opening Source Quality Spine

Book-level invariant, opened in chapters 1-5: faith is not a private interior claim
but a tested and enacted form. James begins with dispersion, trial, wisdom, word,
speech, and care because the scattered community is measured by what faith does
under pressure. Chapter 2 then forces the claim through the assembly, the poor,
the hungry body, and the works that give faith its living form. Chapter 3 tests
whether that form can survive the steering organ of speech and the fruit-texture
of wisdom. Chapter 4 follows the fire back to its source: disordered desire,
world-friendship, judgment speech, and planning that forgets life is vapor. The
closing chapter lets rust, wages, patience, and prayer testify about the economy
of a life.

Primary gap/counterproof: religious speech can simulate life while dodging
obedience. James refuses the counterfeit ledgers: blaming God for temptation,
mistaking wealth for permanence, using wrath as righteousness, and hearing the
word as if admiration were reception. It also rejects the gold-ring liturgy that
calls partiality discernment and the verbal charity that leaves bodies cold.
It refuses the mouth that blesses God while cursing God's likeness, and the
ambition that calls itself wisdom while producing confusion.
It refuses to let war blame only the room when the conflict is already in the
members, and it refuses tomorrow-plans that pretend to be sovereignty.
It refuses wealth that thinks storage is silence; even rust can become a
prosecuting witness.

Unseen sat: liberty is not less demanding than law. The perfect law of liberty
requires a doer who remembers in action; pure religion is visible where the
vulnerable are visited and the world cannot spot the witness.
Mercy is the deeper intelligence of judgment, and works are not decoration on
faith but its breath. True wisdom is not louder control; it is peaceable fruit.
Humility is not collapse; it is the restoration of creaturely location under
the Lord's will. Prayer is not atmosphere; it is the repair protocol by which
the afflicted, sick, confessing, and erring are brought back toward life.

No `sorry`, no new `axiom`.
-/

structure JamesOpeningInvariant where
  scatteredFaithIsTestedTowardWholeness : Bool := true
  wisdomRequiresUnwaveringAsk : Bool := true
  wordMustBecomeDoing : Bool := true
  libertyLawRequiresEnactedMemory : Bool := true
  mercyAndWorksAnimateFaith : Bool := true
  speechAndWisdomRevealSource : Bool := true
  humilityLocatesDesireUnderGod : Bool := true
  patientPrayerRestoresUnderJudgment : Bool := true
deriving DecidableEq, Repr

def jamesOpeningInvariant : JamesOpeningInvariant := {}

def enactedFaithInvariant (i : JamesOpeningInvariant) : Prop :=
  i.scatteredFaithIsTestedTowardWholeness = true ∧
  i.wisdomRequiresUnwaveringAsk = true ∧
  i.wordMustBecomeDoing = true ∧
  i.libertyLawRequiresEnactedMemory = true ∧
  i.mercyAndWorksAnimateFaith = true ∧
  i.speechAndWisdomRevealSource = true ∧
  i.humilityLocatesDesireUnderGod = true ∧
  i.patientPrayerRestoresUnderJudgment = true

structure JamesOpeningCounterproof where
  godCannotBeBlamedForTemptation : Bool := true
  wealthCannotAnchorIdentity : Bool := true
  wrathCannotWorkRighteousness : Bool := true
  hearingOnlyCannotCountAsObedience : Bool := true
  unbridledTongueCannotBePureReligion : Bool := true
  partialityCannotNameItselfWisdom : Bool := true
  verbalMercyCannotReplaceBodyCare : Bool := true
  blessingAndCursingCannotShareOneSource : Bool := true
  bitterEnvyCannotPassAsWisdomFromAbove : Bool := true
  appetiteCannotDisguiseItselfAsPrayer : Bool := true
  tomorrowPlanningCannotOwnLife : Bool := true
  hoardedWealthCannotSilenceLaborCry : Bool := true
  oathTheaterCannotReplacePlainTruth : Bool := true
deriving DecidableEq, Repr

def jamesOpeningCounterproof : JamesOpeningCounterproof := {}

def falseReligionRejected (c : JamesOpeningCounterproof) : Prop :=
  c.godCannotBeBlamedForTemptation = true ∧
  c.wealthCannotAnchorIdentity = true ∧
  c.wrathCannotWorkRighteousness = true ∧
  c.hearingOnlyCannotCountAsObedience = true ∧
  c.unbridledTongueCannotBePureReligion = true ∧
  c.partialityCannotNameItselfWisdom = true ∧
  c.verbalMercyCannotReplaceBodyCare = true ∧
  c.blessingAndCursingCannotShareOneSource = true ∧
  c.bitterEnvyCannotPassAsWisdomFromAbove = true ∧
  c.appetiteCannotDisguiseItselfAsPrayer = true ∧
  c.tomorrowPlanningCannotOwnLife = true ∧
  c.hoardedWealthCannotSilenceLaborCry = true ∧
  c.oathTheaterCannotReplacePlainTruth = true

theorem james_opening_quality_invariant :
    enactedFaithInvariant jamesOpeningInvariant := by
  unfold enactedFaithInvariant jamesOpeningInvariant
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem james_opening_quality_counterproof :
    falseReligionRejected jamesOpeningCounterproof := by
  unfold falseReligionRejected jamesOpeningCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem james_source_quality_opening_witness :
    enactedFaithInvariant jamesOpeningInvariant ∧
    falseReligionRejected jamesOpeningCounterproof ∧
    JamesTestingDoingWitness.testingPatienceWitness
      JamesTestingDoingWitness.testingPatience ∧
    JamesTestingDoingWitness.falseTemptationLedgerRejected
      JamesTestingDoingWitness.temptationCounterproof ∧
    JamesTestingDoingWitness.engraftedDoingWitness
      JamesTestingDoingWitness.engraftedDoing ∧
    JamesPartialityWorksWitness.partialityJudgmentWitness
      JamesPartialityWorksWitness.partialityJudgment ∧
    JamesPartialityWorksWitness.mercyLawWitness
      JamesPartialityWorksWitness.mercyLaw ∧
    JamesPartialityWorksWitness.corpseFaithRejected
      JamesPartialityWorksWitness.deadFaithCounterproof ∧
    JamesTongueWisdomWitness.tongueSteeringWitness
      JamesTongueWisdomWitness.tongueSteering ∧
    JamesTongueWisdomWitness.corruptFountainRejected
      JamesTongueWisdomWitness.corruptFountainCounterproof ∧
    JamesTongueWisdomWitness.wisdomFromAboveWitness
      JamesTongueWisdomWitness.wisdomFromAbove ∧
    JamesWarVaporWitness.warSourceWitness
      JamesWarVaporWitness.warSource ∧
    JamesWarVaporWitness.humbleNearnessWitness
      JamesWarVaporWitness.humbleNearness ∧
    JamesWarVaporWitness.falseSovereigntyRejected
      JamesWarVaporWitness.vaporPlanningCounterproof ∧
    JamesRustPrayerWitness.rustWitnessTestimony
      JamesRustPrayerWitness.rustWitness ∧
    JamesRustPrayerWitness.patientEnduranceWitness
      JamesRustPrayerWitness.patientEndurance ∧
    JamesRustPrayerWitness.restoringPrayerWitness
      JamesRustPrayerWitness.restoringPrayer := by
  exact ⟨james_opening_quality_invariant,
    james_opening_quality_counterproof,
    JamesTestingDoingWitness.james_testing_patience,
    JamesTestingDoingWitness.james_false_temptation_ledger_rejected,
    JamesTestingDoingWitness.james_engrafted_doing,
    JamesPartialityWorksWitness.james_partiality_judgment,
    JamesPartialityWorksWitness.james_mercy_law,
    JamesPartialityWorksWitness.james_corpse_faith_rejected,
    JamesTongueWisdomWitness.james_tongue_steering,
    JamesTongueWisdomWitness.james_corrupt_fountain_rejected,
    JamesTongueWisdomWitness.james_wisdom_from_above,
    JamesWarVaporWitness.james_war_source,
    JamesWarVaporWitness.james_humble_nearness,
    JamesWarVaporWitness.james_false_sovereignty_rejected,
    JamesRustPrayerWitness.james_rust_witness,
    JamesRustPrayerWitness.james_patient_endurance,
    JamesRustPrayerWitness.james_restoring_prayer⟩

end JamesSourceQualityWitness
end Gnosis.Witnesses.Bible.James
