import Init

namespace Gnosis.Witnesses.Bible.Romans
namespace RomansRenderAccordingToDeedsWitness

/-!
# Romans 2:6-11 (KJV) -- Render According to Deeds

This unit gives one bounded recompense topology:

  * God renders to every man according to his deeds;
  * patient continuance in well doing seeks glory, honour, and immortality;
  * contentious disobedience receives indignation and wrath;
  * evil-doing receives tribulation and anguish;
  * good-working receives glory, honour, and peace;
  * the pattern applies Jew first and also Gentile, with no respect of persons.

`import Init` only. Zero new `axiom`, no Mathlib.
-/

/-! ## Section 0: The text-shadow -/

/-- Romans 2:6-11 (KJV). Text-shadow kept beside the formalization so the
    witness names the exact passage it parameterizes. -/
def romans_2_6_11_quote : String :=
  "2:6 Who will render to every man according to his deeds: 2:7 To " ++
  "them who by patient continuance in well doing seek for glory and " ++
  "honour and immortality, eternal life: 2:8 But unto them that are " ++
  "contentious, and do not obey the truth, but obey unrighteousness, " ++
  "indignation and wrath, 2:9 Tribulation and anguish, upon every soul " ++
  "of man that doeth evil, of the Jew first, and also of the Gentile; " ++
  "2:10 But glory, honour, and peace, to every man that worketh good, " ++
  "to the Jew first, and also to the Gentile: 2:11 For there is no " ++
  "respect of persons with God."

/-! ## Section 1: Rendering principle -/

/-- The universal rendering principle in Romans 2:6. -/
structure RenderPrinciple where
  rendersToEveryMan : Bool
  accordingToDeeds : Bool
deriving DecidableEq, Repr

/-- God renders to every man according to his deeds. -/
def renderPrinciple : RenderPrinciple where
  rendersToEveryMan := true
  accordingToDeeds := true

/-- The rendering principle is universal and deed-indexed. -/
theorem render_to_every_man_according_to_deeds :
    renderPrinciple.rendersToEveryMan = true
    ∧ renderPrinciple.accordingToDeeds = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 2: Two deed trajectories -/

/-- The two trajectories contrasted in Romans 2:7-10. -/
inductive DeedTrajectory
  | patientContinuanceInWellDoing
  | contentiousDisobedience
  | soulDoingEvil
  | everyManWorkingGood
deriving DecidableEq, Repr

/-- The trajectories named in source order. -/
def deedTrajectories : List DeedTrajectory :=
  [ DeedTrajectory.patientContinuanceInWellDoing
  , DeedTrajectory.contentiousDisobedience
  , DeedTrajectory.soulDoingEvil
  , DeedTrajectory.everyManWorkingGood
  ]

/-- The contrast begins with patient continuance in well doing. -/
theorem trajectories_begin_with_patient_continuance :
    deedTrajectories.head? =
      some DeedTrajectory.patientContinuanceInWellDoing := rfl

/-- The contrast closes with every man that worketh good. -/
theorem trajectories_close_with_working_good :
    deedTrajectories.getLast? =
      some DeedTrajectory.everyManWorkingGood := rfl

/-! ## Section 3: Recompense outcomes -/

/-- The named recompense outcomes in Romans 2:7-10. -/
inductive RecompenseOutcome
  | eternalLife
  | indignationAndWrath
  | tribulationAndAnguish
  | gloryHonourPeace
deriving DecidableEq, Repr

/-- Outcomes in source order. -/
def recompenseOutcomes : List RecompenseOutcome :=
  [ RecompenseOutcome.eternalLife
  , RecompenseOutcome.indignationAndWrath
  , RecompenseOutcome.tribulationAndAnguish
  , RecompenseOutcome.gloryHonourPeace
  ]

/-- Patient continuance is paired with eternal life in this bounded witness. -/
structure PatientContinuancePattern where
  seeksGloryHonourImmortality : Bool
  receivesEternalLife : Bool
deriving DecidableEq, Repr

/-- The positive trajectory seeks glory, honour, and immortality. -/
def patientContinuancePattern : PatientContinuancePattern where
  seeksGloryHonourImmortality := true
  receivesEternalLife := true

/-- Patient continuance seeks glory, honour, immortality, and receives eternal life. -/
theorem patient_continuance_receives_life :
    patientContinuancePattern.seeksGloryHonourImmortality = true
    ∧ patientContinuancePattern.receivesEternalLife = true := by
  exact ⟨rfl, rfl⟩

/-! ## Section 4: Impartial application -/

/-- The Jew/Gentile and no-respect-of-persons application in Romans 2:9-11. -/
structure ImpartialApplication where
  jewFirst : Bool
  gentileAlso : Bool
  noRespectOfPersonsWithGod : Bool
deriving DecidableEq, Repr

/-- The recompense pattern applies without respect of persons. -/
def impartialApplication : ImpartialApplication where
  jewFirst := true
  gentileAlso := true
  noRespectOfPersonsWithGod := true

/-- Both Jew and Gentile are named, and God has no respect of persons. -/
theorem impartial_jew_and_gentile_application :
    impartialApplication.jewFirst = true
    ∧ impartialApplication.gentileAlso = true
    ∧ impartialApplication.noRespectOfPersonsWithGod = true := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 5: Master witness -/

/-- The bounded Romans 2:6-11 witness. -/
theorem romans_render_according_to_deeds_witness :
    renderPrinciple.rendersToEveryMan = true
    ∧ renderPrinciple.accordingToDeeds = true
    ∧ deedTrajectories.length = 4
    ∧ deedTrajectories.head? =
      some DeedTrajectory.patientContinuanceInWellDoing
    ∧ deedTrajectories.getLast? =
      some DeedTrajectory.everyManWorkingGood
    ∧ recompenseOutcomes.length = 4
    ∧ recompenseOutcomes.head? = some RecompenseOutcome.eternalLife
    ∧ recompenseOutcomes.getLast? = some RecompenseOutcome.gloryHonourPeace
    ∧ patientContinuancePattern.seeksGloryHonourImmortality = true
    ∧ patientContinuancePattern.receivesEternalLife = true
    ∧ impartialApplication.jewFirst = true
    ∧ impartialApplication.gentileAlso = true
    ∧ impartialApplication.noRespectOfPersonsWithGod = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end RomansRenderAccordingToDeedsWitness
end Gnosis.Witnesses.Bible.Romans
