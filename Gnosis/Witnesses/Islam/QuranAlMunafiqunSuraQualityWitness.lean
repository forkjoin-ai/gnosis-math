import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlMunafiqunSuraQualityWitness

/-!
# Quran 63, Al-Munafiqun / The Hypocrites -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14620-14655`.

This complete sura witness covers Quran 63:1-11.

Al-Munafiqun is the oath-mask-and-deferred-death witness: hypocrites testify with
their tongues while God knows they lie, oaths become shields, impressive bodies
hide hollow panic, spending is weaponized against the Messenger's companions,
and death exposes the impossibility of postponed charity.

No `sorry`, no new `axiom`.
-/

inductive MunafiqunQualityCluster
  | tongueTestimonyAndGodsCounterWitness
  | oathShieldAndSealedHearts
  | impressiveBodiesAndHollowPanic
  | spendingThreatAndHonorCorrection
  | deathDeferralAndLostCharity
deriving DecidableEq, Repr

def munafiqunQualityClusters : List MunafiqunQualityCluster :=
  [ .tongueTestimonyAndGodsCounterWitness, .oathShieldAndSealedHearts,
    .impressiveBodiesAndHollowPanic, .spendingThreatAndHonorCorrection,
    .deathDeferralAndLostCharity ]

structure MunafiqunInvariantLedger where
  godKnowsFalseTestimony : Bool := true
  oathsCannotShieldSealedHearts : Bool := true
  honorBelongsToGodMessengerAndBelievers : Bool := true
  wealthAndChildrenMustNotDistractFromRemembrance : Bool := true
  deathClosesDeferredGiving : Bool := true
deriving DecidableEq, Repr

def munafiqunInvariantLedger : MunafiqunInvariantLedger := {}

def munafiqunSat (l : MunafiqunInvariantLedger) : Prop :=
  l.godKnowsFalseTestimony = true ∧ l.oathsCannotShieldSealedHearts = true ∧
  l.honorBelongsToGodMessengerAndBelievers = true ∧
  l.wealthAndChildrenMustNotDistractFromRemembrance = true ∧
  l.deathClosesDeferredGiving = true

structure MunafiqunGapLedger where
  speechCanContradictKnownTruth : Bool := true
  oathsBecomeSocialCover : Bool := true
  hollowBodiesAppearImpressive : Bool := true
  provisionIsUsedAsCoercion : Bool := true
  laterCharityRequestArrivesTooLate : Bool := true
deriving DecidableEq, Repr

def munafiqunGapLedger : MunafiqunGapLedger := {}

def munafiqunGapsExposeBoundary (g : MunafiqunGapLedger) : Prop :=
  g.speechCanContradictKnownTruth = true ∧ g.oathsBecomeSocialCover = true ∧
  g.hollowBodiesAppearImpressive = true ∧ g.provisionIsUsedAsCoercion = true ∧
  g.laterCharityRequestArrivesTooLate = true

def munafiqunSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 63 / Al-Munafiqun witnesses oath masks, hollow status, and deferred-death failure"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive MunafiqunRegister | testimony | oaths | bodies | honor | wealth | death
deriving DecidableEq, Repr, Nonempty

inductive MunafiqunInvariant | oathMaskDeathBoundary
deriving DecidableEq, Repr

def munafiqunRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MunafiqunRegister => MunafiqunInvariant.oathMaskDeathBoundary)
      MunafiqunInvariant.oathMaskDeathBoundary :=
  TruthOneManyNamesWitness.constant_names_agree MunafiqunInvariant.oathMaskDeathBoundary

theorem munafiqun_quality_clusters_shape :
    munafiqunQualityClusters.length = 5 ∧
    munafiqunQualityClusters.head? = some .tongueTestimonyAndGodsCounterWitness ∧
    munafiqunQualityClusters.getLast? = some .deathDeferralAndLostCharity := by
  exact ⟨rfl, rfl, rfl⟩

theorem munafiqun_sat_witness : munafiqunSat munafiqunInvariantLedger := by
  unfold munafiqunSat munafiqunInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem munafiqun_gap_witness : munafiqunGapsExposeBoundary munafiqunGapLedger := by
  unfold munafiqunGapsExposeBoundary munafiqunGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem munafiqun_access_archaeological :
    munafiqunSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_munafiqun_sura_quality_witness :
    munafiqunQualityClusters.length = 5 ∧ munafiqunSat munafiqunInvariantLedger ∧
    munafiqunGapsExposeBoundary munafiqunGapLedger ∧
    munafiqunSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : MunafiqunRegister => MunafiqunInvariant.oathMaskDeathBoundary)
      MunafiqunInvariant.oathMaskDeathBoundary := by
  exact ⟨munafiqun_quality_clusters_shape.left, munafiqun_sat_witness, munafiqun_gap_witness,
    munafiqun_access_archaeological, munafiqunRegistersAgree⟩

end QuranAlMunafiqunSuraQualityWitness
end Gnosis.Witnesses.Islam
