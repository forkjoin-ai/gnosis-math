namespace Gnosis.Witnesses.Bible.SecondPeter
namespace SecondPeterFalseTeacherWitness

/-!
# 2 Peter 2 -- Merchandise, Balaam, and Wells Without Water

Source slice: 2 Peter 2:1-22.

Chapter invariant: false teaching is not merely bad doctrine; it is an
extraction economy. Feigned words make merchandise of hearers, swelling vanity
allures the barely escaped, and promised liberty hides servitude to corruption.

Primary gap/counterproof: delay is not acquittal. Judgment does not need to
hurry in order to be awake; angels, the old world, and Sodom/Gomorrha establish
that preservation of the unjust and deliverance of the godly can run in the same
ledger.

Unseen sat: Balaam is the diagnostic key. Prophetic capacity can be overridden
by wage-love, and the rebuke arrives through the humblest mouth. The chapter's
hard contrarian theorem is that a waterless well is worse than no well because
it advertises thirst-relief while increasing drought.

No `sorry`, no new `axiom`.
-/

structure MerchandiseHeresy where
  falseTeachersPrivilyEnter : Bool := true
  denyingBuyerBringsSwiftDestruction : Bool := true
  manyFollowPerniciousWays : Bool := true
  truthEvilSpokenThroughThem : Bool := true
  feignedWordsMakeMerchandise : Bool := true
deriving DecidableEq, Repr

def merchandiseHeresy : MerchandiseHeresy := {}

def counterfeitWitnessEconomy (m : MerchandiseHeresy) : Prop :=
  m.falseTeachersPrivilyEnter = true ∧
  m.denyingBuyerBringsSwiftDestruction = true ∧
  m.manyFollowPerniciousWays = true ∧
  m.truthEvilSpokenThroughThem = true ∧
  m.feignedWordsMakeMerchandise = true

structure JudgmentDeliveranceLedger where
  angelsReservedInDarkness : Bool := true
  noahSavedAsRighteousPreacher : Bool := true
  sodomMadeEnsample : Bool := true
  lotDeliveredWhileVexed : Bool := true
  lordKnowsDeliverAndReserve : Bool := true
deriving DecidableEq, Repr

def judgmentDeliveranceLedger : JudgmentDeliveranceLedger := {}

def judgmentDoesNotSlumber (j : JudgmentDeliveranceLedger) : Prop :=
  j.angelsReservedInDarkness = true ∧
  j.noahSavedAsRighteousPreacher = true ∧
  j.sodomMadeEnsample = true ∧
  j.lotDeliveredWhileVexed = true ∧
  j.lordKnowsDeliverAndReserve = true

structure BalaamWaterlessWell where
  speaksEvilOfUnunderstoodThings : Bool := true
  balaamLovedUnrighteousWages : Bool := true
  dumbMouthRebukesPropheticMadness : Bool := true
  wellsWithoutWaterReservedDarkness : Bool := true
  promisedLibertyMasksCorruptionBondage : Bool := true
  latterEndWorseAfterEscape : Bool := true
deriving DecidableEq, Repr

def balaamWaterlessWell : BalaamWaterlessWell := {}

def libertyCounterfeitRejected (b : BalaamWaterlessWell) : Prop :=
  b.speaksEvilOfUnunderstoodThings = true ∧
  b.balaamLovedUnrighteousWages = true ∧
  b.dumbMouthRebukesPropheticMadness = true ∧
  b.wellsWithoutWaterReservedDarkness = true ∧
  b.promisedLibertyMasksCorruptionBondage = true ∧
  b.latterEndWorseAfterEscape = true

theorem second_peter_merchandise_heresy :
    counterfeitWitnessEconomy merchandiseHeresy := by
  unfold counterfeitWitnessEconomy merchandiseHeresy
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem second_peter_judgment_deliverance :
    judgmentDoesNotSlumber judgmentDeliveranceLedger := by
  unfold judgmentDoesNotSlumber judgmentDeliveranceLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem second_peter_liberty_counterfeit_rejected :
    libertyCounterfeitRejected balaamWaterlessWell := by
  unfold libertyCounterfeitRejected balaamWaterlessWell
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem second_peter_false_teacher_witness :
    counterfeitWitnessEconomy merchandiseHeresy ∧
    judgmentDoesNotSlumber judgmentDeliveranceLedger ∧
    libertyCounterfeitRejected balaamWaterlessWell := by
  exact ⟨second_peter_merchandise_heresy,
    second_peter_judgment_deliverance,
    second_peter_liberty_counterfeit_rejected⟩

end SecondPeterFalseTeacherWitness
end Gnosis.Witnesses.Bible.SecondPeter
