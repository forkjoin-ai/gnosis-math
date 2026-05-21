namespace Gnosis.Witnesses.Bible.FirstJohn
namespace FirstJohnAdvocateAntichristWitness

/-!
# 1 John 2 -- Advocate, Command-Knowledge, World-Lust, and Antichrist Split

Source slice: 1 John 2:1-29.

Chapter invariant: knowledge is command-keeping under an Advocate, not
permission to blur sin. Propitiation is world-wide in scope, but the local test
of knowing him remains walking as he walked.

Primary gap/counterproof: brother-hate falsifies light-claims. The chapter's
contrarian force is that hatred is epistemic damage: the hater does not know
where he goes because darkness has blinded his eyes.

Unseen sat: antichrist appears as a subtraction operator. It denies the Son and
thereby loses the Father; it exits fellowship so its non-belonging becomes
manifest. The anointing does not abolish teaching but guards abiding truth from
seduction.

No `sorry`, no new `axiom`.
-/

structure AdvocateCommandKnowledge where
  advocateWithFather : Bool := true
  propitiationForWholeWorld : Bool := true
  knowingTestedByCommandKeeping : Bool := true
  wordKeptPerfectsLove : Bool := true
  abidingRequiresWalkingAsHeWalked : Bool := true
deriving DecidableEq, Repr

def advocateCommandKnowledge : AdvocateCommandKnowledge := {}

def commandKnowledgeLedger (a : AdvocateCommandKnowledge) : Prop :=
  a.advocateWithFather = true ∧
  a.propitiationForWholeWorld = true ∧
  a.knowingTestedByCommandKeeping = true ∧
  a.wordKeptPerfectsLove = true ∧
  a.abidingRequiresWalkingAsHeWalked = true

structure LightBrotherBoundary where
  oldCommandHeardFromBeginning : Bool := true
  trueLightNowShines : Bool := true
  brotherHatredLeavesDarkness : Bool := true
  brotherLoveRemovesStumbling : Bool := true
  hatredBlindsDirection : Bool := true
deriving DecidableEq, Repr

def lightBrotherBoundary : LightBrotherBoundary := {}

def hatredEpistemicDamage (l : LightBrotherBoundary) : Prop :=
  l.oldCommandHeardFromBeginning = true ∧
  l.trueLightNowShines = true ∧
  l.brotherHatredLeavesDarkness = true ∧
  l.brotherLoveRemovesStumbling = true ∧
  l.hatredBlindsDirection = true

structure WorldAntichristSplit where
  worldLoveExcludesFatherLove : Bool := true
  lustAndPridePassAway : Bool := true
  manyAntichristsMarkLastTime : Bool := true
  departureManifestsNonBelonging : Bool := true
  sonDenialLosesFather : Bool := true
  anointingAbidesAgainstSeduction : Bool := true
deriving DecidableEq, Repr

def worldAntichristSplit : WorldAntichristSplit := {}

def antichristSubtractionRejected (w : WorldAntichristSplit) : Prop :=
  w.worldLoveExcludesFatherLove = true ∧
  w.lustAndPridePassAway = true ∧
  w.manyAntichristsMarkLastTime = true ∧
  w.departureManifestsNonBelonging = true ∧
  w.sonDenialLosesFather = true ∧
  w.anointingAbidesAgainstSeduction = true

theorem first_john_command_knowledge :
    commandKnowledgeLedger advocateCommandKnowledge := by
  unfold commandKnowledgeLedger advocateCommandKnowledge
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_hatred_epistemic_damage :
    hatredEpistemicDamage lightBrotherBoundary := by
  unfold hatredEpistemicDamage lightBrotherBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_antichrist_subtraction_rejected :
    antichristSubtractionRejected worldAntichristSplit := by
  unfold antichristSubtractionRejected worldAntichristSplit
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_john_advocate_antichrist_witness :
    commandKnowledgeLedger advocateCommandKnowledge ∧
    hatredEpistemicDamage lightBrotherBoundary ∧
    antichristSubtractionRejected worldAntichristSplit := by
  exact ⟨first_john_command_knowledge,
    first_john_hatred_epistemic_damage,
    first_john_antichrist_subtraction_rejected⟩

end FirstJohnAdvocateAntichristWitness
end Gnosis.Witnesses.Bible.FirstJohn
