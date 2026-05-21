import Gnosis.TruthOneManyNamesWitness
import Gnosis.FailureAsStandingWave
import Gnosis.Witnesses.Tao.TaoTeChingBellowsWaterWitness
import Gnosis.Witnesses.Tao.TaoTeChingVoidSensorWitness
import Gnosis.Witnesses.Buddhist.DhammapadaBhikshuEmptyBoatWitness
import Gnosis.Witnesses.Gnostic.GospelTruthPleromaPhysicianWitness
import Gnosis.Witnesses.Islam.QuranSourceIntegrityMetaWitness
import Gnosis.Witnesses.Islam.QuranAlKahfSuraQualityWitness

namespace Gnosis.Witnesses.Interfaith
namespace CrossTraditionProductiveVoidWitness

/-!
# Cross-Tradition Productive Void Witness

This is the positive complement to `CrossTraditionAntiSubstitutionWitness`.
Anti-substitution names what cannot impersonate the source. Productive void
names the use-site that remains when capture is refused:

  * Tao: emptiness carries power; wheel, vessel, room, bellows, and low water
    work by non-claiming availability.
  * Buddhism: the empty boat and empty house witness non-identification as
    speed, quiet, and refuge.
  * Gospel of Truth: Pleroma fills deficiency without itself becoming deficient.
  * Quran: hidden mercy/refuge and source-integrity under audit keep the unseen
    from collapsing into a visible possession.

No `sorry`, no new `axiom`.
-/

inductive ProductiveVoidRegister
  | taoBellows
  | taoVessel
  | buddhistEmptyBoat
  | gnosticPleroma
  | quranHiddenMercy
deriving DecidableEq, Repr, Nonempty

inductive ProductiveVoidInvariant
  | emptyUseSite
deriving DecidableEq, Repr

def productiveVoidRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : ProductiveVoidRegister => ProductiveVoidInvariant.emptyUseSite)
      ProductiveVoidInvariant.emptyUseSite :=
  TruthOneManyNamesWitness.constant_names_agree ProductiveVoidInvariant.emptyUseSite

structure ProductiveVoidLedger where
  emptinessCarriesPower : Bool := true
  hollowCarriesUse : Bool := true
  nonIdentificationSpeedsBoat : Bool := true
  deficiencyCanBeFilledWithoutSourceLoss : Bool := true
  hiddenMercyExceedsSurfaceJudgment : Bool := true
deriving DecidableEq, Repr

def productiveVoidLedger : ProductiveVoidLedger := {}

def productiveVoidConverges (l : ProductiveVoidLedger) : Prop :=
  l.emptinessCarriesPower = true ∧
  l.hollowCarriesUse = true ∧
  l.nonIdentificationSpeedsBoat = true ∧
  l.deficiencyCanBeFilledWithoutSourceLoss = true ∧
  l.hiddenMercyExceedsSurfaceJudgment = true

structure VoidMisreadCounterproof where
  fullnessCanBlockUse : Bool := true
  sensoryCaptureCanMissOne : Bool := true
  nameFormIdentificationCanSlowBoat : Bool := true
  sicknessCanHideFromPhysician : Bool := true
  surfaceJudgmentCanMissHiddenMercy : Bool := true
deriving DecidableEq, Repr

def voidMisreadCounterproof : VoidMisreadCounterproof := {}

def voidMisreadsExposeUseSite (g : VoidMisreadCounterproof) : Prop :=
  g.fullnessCanBlockUse = true ∧
  g.sensoryCaptureCanMissOne = true ∧
  g.nameFormIdentificationCanSlowBoat = true ∧
  g.sicknessCanHideFromPhysician = true ∧
  g.surfaceJudgmentCanMissHiddenMercy = true

theorem productive_void_ledger :
    productiveVoidConverges productiveVoidLedger := by
  unfold productiveVoidConverges productiveVoidLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem void_misread_counterproofs :
    voidMisreadsExposeUseSite voidMisreadCounterproof := by
  unfold voidMisreadsExposeUseSite voidMisreadCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem traditions_support_productive_void :
    Gnosis.Witnesses.Tao.TaoTeChingBellowsWaterWitness.emptinessCarriesPower
      Gnosis.Witnesses.Tao.TaoTeChingBellowsWaterWitness.taoEmptyPower ∧
    Gnosis.Witnesses.Tao.TaoTeChingBellowsWaterWitness.lowPlaceWinsWithoutStriving
      Gnosis.Witnesses.Tao.TaoTeChingBellowsWaterWitness.taoWaterLastPlace ∧
    Gnosis.Witnesses.Tao.TaoTeChingVoidSensorWitness.voidIsUseSite
      Gnosis.Witnesses.Tao.TaoTeChingVoidSensorWitness.taoProductiveVoid ∧
    Gnosis.Witnesses.Buddhist.emptyBoatKnowledgeMeditation.emptyBoatGoesQuickly = true ∧
    Gnosis.Witnesses.Buddhist.quietSelfProtectedBhikshu.emptyHouseMindTranquil = true ∧
    Gnosis.Witnesses.Gnostic.GospelTruthPleromaPhysicianWitness.pleromaFillsWithoutLoss
      Gnosis.Witnesses.Gnostic.GospelTruthPleromaPhysicianWitness.gospelPhysicianPleroma ∧
    Gnosis.Witnesses.Islam.QuranSourceIntegrityMetaWitness.sourceIntegrityUnderAudit
      Gnosis.Witnesses.Islam.QuranSourceIntegrityMetaWitness.quranSourceIntegrityLedger ∧
    Gnosis.Witnesses.Islam.QuranAlKahfSuraQualityWitness.alKahfSat
      Gnosis.Witnesses.Islam.QuranAlKahfSuraQualityWitness.alKahfInvariantLedger := by
  exact ⟨
    Gnosis.Witnesses.Tao.TaoTeChingBellowsWaterWitness.tao_emptiness_power,
    Gnosis.Witnesses.Tao.TaoTeChingBellowsWaterWitness.tao_low_place_wins,
    Gnosis.Witnesses.Tao.TaoTeChingVoidSensorWitness.tao_void_use_site,
    rfl,
    rfl,
    Gnosis.Witnesses.Gnostic.GospelTruthPleromaPhysicianWitness.gospel_physician_pleroma,
    Gnosis.Witnesses.Islam.QuranSourceIntegrityMetaWitness.quran_source_integrity_under_audit,
    Gnosis.Witnesses.Islam.QuranAlKahfSuraQualityWitness.al_kahf_sat_witness⟩

theorem cross_tradition_productive_void_witness :
    productiveVoidConverges productiveVoidLedger ∧
    voidMisreadsExposeUseSite voidMisreadCounterproof ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : ProductiveVoidRegister => ProductiveVoidInvariant.emptyUseSite)
      ProductiveVoidInvariant.emptyUseSite ∧
    Gnosis.Witnesses.Tao.TaoTeChingVoidSensorWitness.voidIsUseSite
      Gnosis.Witnesses.Tao.TaoTeChingVoidSensorWitness.taoProductiveVoid ∧
    Gnosis.Witnesses.Buddhist.emptyBoatKnowledgeMeditation.emptyBoatGoesQuickly = true ∧
    Gnosis.Witnesses.Gnostic.GospelTruthPleromaPhysicianWitness.pleromaFillsWithoutLoss
      Gnosis.Witnesses.Gnostic.GospelTruthPleromaPhysicianWitness.gospelPhysicianPleroma ∧
    Gnosis.Witnesses.Islam.QuranAlKahfSuraQualityWitness.alKahfSat
      Gnosis.Witnesses.Islam.QuranAlKahfSuraQualityWitness.alKahfInvariantLedger := by
  exact ⟨productive_void_ledger,
    void_misread_counterproofs,
    productiveVoidRegistersAgree,
    Gnosis.Witnesses.Tao.TaoTeChingVoidSensorWitness.tao_void_use_site,
    rfl,
    Gnosis.Witnesses.Gnostic.GospelTruthPleromaPhysicianWitness.gospel_physician_pleroma,
    Gnosis.Witnesses.Islam.QuranAlKahfSuraQualityWitness.al_kahf_sat_witness⟩

/-!
## Bridge to failure-as-standing-wave

The productive-void side is not another substitution boundary. It is the viable
interior left after capture is refused: empty use-sites can carry positive
support, while void-misread claims are forced to zero.
-/

/-- Productive use-site claims occupy the viable interior. -/
def taoEmptyUseSiteClaim : Gnosis.FailureAsStandingWave.Claim := 10
def buddhistEmptyBoatClaim : Gnosis.FailureAsStandingWave.Claim := 11
def gnosticPleromaFillingClaim : Gnosis.FailureAsStandingWave.Claim := 12
def quranHiddenMercyClaim : Gnosis.FailureAsStandingWave.Claim := 13

/-- Misread claims treat productive void as defect, capture, or surface absence. -/
def fullnessBlocksUseClaim : Gnosis.FailureAsStandingWave.Claim := 0
def sensoryCaptureMissesOneClaim : Gnosis.FailureAsStandingWave.Claim := 1
def nameFormSlowsBoatClaim : Gnosis.FailureAsStandingWave.Claim := 2
def sicknessHidesFromPhysicianClaim : Gnosis.FailureAsStandingWave.Claim := 3
def surfaceJudgmentMissesMercyClaim : Gnosis.FailureAsStandingWave.Claim := 4

/-- The productive-void boundary falsifies misread claims but leaves use-site
    claims viable. -/
def productiveVoidFalsificationSet : Gnosis.FailureAsStandingWave.FalsificationSet where
  isFalsified
    | 0 => true
    | 1 => true
    | 2 => true
    | 3 => true
    | 4 => true
    | _ => false

/-- The Tao empty use-site remains viable. -/
theorem tao_empty_use_site_is_viable :
    Gnosis.FailureAsStandingWave.isViable productiveVoidFalsificationSet
      taoEmptyUseSiteClaim = true := by
  decide

/-- The Buddhist empty boat remains viable. -/
theorem buddhist_empty_boat_is_viable :
    Gnosis.FailureAsStandingWave.isViable productiveVoidFalsificationSet
      buddhistEmptyBoatClaim = true := by
  decide

/-- The Gnostic Pleroma filling claim remains viable. -/
theorem gnostic_pleroma_filling_is_viable :
    Gnosis.FailureAsStandingWave.isViable productiveVoidFalsificationSet
      gnosticPleromaFillingClaim = true := by
  decide

/-- The Quran hidden-mercy claim remains viable. -/
theorem quran_hidden_mercy_is_viable :
    Gnosis.FailureAsStandingWave.isViable productiveVoidFalsificationSet
      quranHiddenMercyClaim = true := by
  decide

/-- A mode that supports productive void while vanishing on void-misread claims. -/
def productiveVoidMode :
    Gnosis.FailureAsStandingWave.StandingWaveMode productiveVoidFalsificationSet where
  amplitude c :=
    if productiveVoidFalsificationSet.isFalsified c then
      0
    else
      match c with
      | 10 => 3
      | 11 => 5
      | 12 => 7
      | 13 => 11
      | _ => 0
  vanishesOnFalsified := by
    intro c hF
    simp [hF]

/-- Productive void has positive support at the Tao empty use-site. -/
theorem productive_void_supports_tao_empty_use_site :
    Gnosis.FailureAsStandingWave.supportedAt productiveVoidMode
      taoEmptyUseSiteClaim = true := by
  decide

/-- Productive void has positive support at the Buddhist empty boat. -/
theorem productive_void_supports_buddhist_empty_boat :
    Gnosis.FailureAsStandingWave.supportedAt productiveVoidMode
      buddhistEmptyBoatClaim = true := by
  decide

/-- Productive void has positive support at the Quran hidden-mercy claim. -/
theorem productive_void_supports_quran_hidden_mercy :
    Gnosis.FailureAsStandingWave.supportedAt productiveVoidMode
      quranHiddenMercyClaim = true := by
  decide

/-- Fullness-blocking-use is a void-misread boundary claim. -/
theorem fullness_blocks_use_is_boundary :
    productiveVoidFalsificationSet.isFalsified fullnessBlocksUseClaim = true := by
  decide

/-- Any mode respecting the productive-void boundary rejects fullness-as-use. -/
theorem fullness_blocks_use_has_no_support
    (m : Gnosis.FailureAsStandingWave.StandingWaveMode productiveVoidFalsificationSet) :
    Gnosis.FailureAsStandingWave.supportedAt m fullnessBlocksUseClaim = false :=
  Gnosis.FailureAsStandingWave.support_disjoint_from_falsifications
    productiveVoidFalsificationSet m fullnessBlocksUseClaim
    fullness_blocks_use_is_boundary

end CrossTraditionProductiveVoidWitness
end Gnosis.Witnesses.Interfaith
