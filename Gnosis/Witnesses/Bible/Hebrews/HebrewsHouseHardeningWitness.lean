namespace Gnosis.Witnesses.Bible.Hebrews
namespace HebrewsHouseHardeningWitness

/-!
# Hebrews 3 -- House, Today, and Hardened Hearts

Source slice: Hebrews 3:1-19.

Chapter invariant: Moses is faithful in the house as servant and testimony, but
Christ is faithful as Son over the house. The comparison does not erase Moses;
it assigns rank by builder/house and servant/Son boundaries.

Primary gap/counterproof: prior deliverance does not guarantee entry. The
wilderness generation heard, saw works forty years, and still hardened through
unbelief; therefore the living warning is not antiquarian memory but today's
aperture of response.

Unseen sat: the house is held by persevering confidence, not by proximity to
signs. Daily exhortation functions as anti-hardening maintenance while it is
called Today.

No `sorry`, no new `axiom`.
-/

structure HouseRank where
  christIsApostleAndHighPriest : Bool := true
  mosesFaithfulAsServant : Bool := true
  christFaithfulAsSon : Bool := true
  builderHasMoreHonourThanHouse : Bool := true
  householdHeldByConfidence : Bool := true
deriving DecidableEq, Repr

def houseRank : HouseRank := {}

def houseRankWitness (h : HouseRank) : Prop :=
  h.christIsApostleAndHighPriest = true ∧
  h.mosesFaithfulAsServant = true ∧
  h.christFaithfulAsSon = true ∧
  h.builderHasMoreHonourThanHouse = true ∧
  h.householdHeldByConfidence = true

structure TodayWarning where
  voiceHeardToday : Bool := true
  hardeningRepeatsProvocation : Bool := true
  dailyExhortationResistsDeceit : Bool := true
  confidenceMustRemainSteadfast : Bool := true
deriving DecidableEq, Repr

def todayWarning : TodayWarning := {}

def todayWarningWitness (w : TodayWarning) : Prop :=
  w.voiceHeardToday = true ∧
  w.hardeningRepeatsProvocation = true ∧
  w.dailyExhortationResistsDeceit = true ∧
  w.confidenceMustRemainSteadfast = true

structure WildernessCounterproof where
  signsDoNotPreventErringHeart : Bool := true
  exodusProximityDoesNotEnsureEntry : Bool := true
  unbeliefBlocksRest : Bool := true
  departedHeartLeavesLivingGod : Bool := true
deriving DecidableEq, Repr

def wildernessCounterproof : WildernessCounterproof := {}

def wildernessUnbeliefRejected (c : WildernessCounterproof) : Prop :=
  c.signsDoNotPreventErringHeart = true ∧
  c.exodusProximityDoesNotEnsureEntry = true ∧
  c.unbeliefBlocksRest = true ∧
  c.departedHeartLeavesLivingGod = true

theorem hebrews_house_rank :
    houseRankWitness houseRank := by
  unfold houseRankWitness houseRank
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem hebrews_today_warning :
    todayWarningWitness todayWarning := by
  unfold todayWarningWitness todayWarning
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_wilderness_counterproof :
    wildernessUnbeliefRejected wildernessCounterproof := by
  unfold wildernessUnbeliefRejected wildernessCounterproof
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem hebrews_house_hardening_witness :
    houseRankWitness houseRank ∧
    todayWarningWitness todayWarning ∧
    wildernessUnbeliefRejected wildernessCounterproof := by
  exact ⟨hebrews_house_rank,
    hebrews_today_warning,
    hebrews_wilderness_counterproof⟩

end HebrewsHouseHardeningWitness
end Gnosis.Witnesses.Bible.Hebrews
