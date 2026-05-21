import Gnosis.ArchaeologicalInfinityAccess
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Islam
namespace QuranAlJumuaSuraQualityWitness

/-!
# Quran 62, Al-Jumua / The Day of Congregation -- Complete Sura Quality Witness

Source text: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`, extracted with
`pdftotext -layout`; text anchor `/tmp/emotions-quran/abdel-haleem-quran.txt:14575-14610`.

This complete sura witness covers Quran 62:1-11.

Al-Jumua is the gathered-remembrance witness: the Sovereign sends a messenger
to recite, purify, and teach; those carrying Torah without bearing it are likened
to a donkey carrying books; death cannot be wished away; and trade or diversion
must not displace Friday remembrance.

No `sorry`, no new `axiom`.
-/

inductive JumuaQualityCluster
  | glorificationSovereigntyAndMessengerPedagogy
  | graceBeyondFormerError
  | torahBearerDonkeyCounterproof
  | deathWishAndUnseenReturn
  | fridayCallTradeDiversionAndBetterProvision
deriving DecidableEq, Repr

def jumuaQualityClusters : List JumuaQualityCluster :=
  [ .glorificationSovereigntyAndMessengerPedagogy, .graceBeyondFormerError,
    .torahBearerDonkeyCounterproof, .deathWishAndUnseenReturn,
    .fridayCallTradeDiversionAndBetterProvision ]

structure JumuaInvariantLedger where
  messengerPurifiesAndTeaches : Bool := true
  graceIsGodsToGive : Bool := true
  carriedBookRequiresLivedBearing : Bool := true
  deathReturnsToUnseenKnower : Bool := true
  remembranceOutranksTradeDiversion : Bool := true
deriving DecidableEq, Repr

def jumuaInvariantLedger : JumuaInvariantLedger := {}

def jumuaSat (l : JumuaInvariantLedger) : Prop :=
  l.messengerPurifiesAndTeaches = true ∧ l.graceIsGodsToGive = true ∧
  l.carriedBookRequiresLivedBearing = true ∧ l.deathReturnsToUnseenKnower = true ∧
  l.remembranceOutranksTradeDiversion = true

structure JumuaGapLedger where
  scriptureCanBeCarriedWithoutBearing : Bool := true
  chosenStatusClaimAvoidsDeathTest : Bool := true
  wrongdoingPreventsDesiredDeath : Bool := true
  tradeAndEntertainmentScatterAssembly : Bool := true
  provisionCanBeMisrankedBelowDiversion : Bool := true
deriving DecidableEq, Repr

def jumuaGapLedger : JumuaGapLedger := {}

def jumuaGapsExposeBoundary (g : JumuaGapLedger) : Prop :=
  g.scriptureCanBeCarriedWithoutBearing = true ∧ g.chosenStatusClaimAvoidsDeathTest = true ∧
  g.wrongdoingPreventsDesiredDeath = true ∧ g.tradeAndEntertainmentScatterAssembly = true ∧
  g.provisionCanBeMisrankedBelowDiversion = true

def jumuaSuraAccess : Gnosis.ArchaeologicalInfinityAccess.Access :=
  { claim := "Quran 62 / Al-Jumua witnesses pedagogy, carried-book failure, and gathered remembrance"
    positiveSamples := [1, 2, 3, 4, 5]
    negativeSamples := [6, 7, 8, 9, 10] }

inductive JumuaRegister | sovereign | messenger | book | death | call | provision
deriving DecidableEq, Repr, Nonempty

inductive JumuaInvariant | gatheredRemembranceBearing
deriving DecidableEq, Repr

def jumuaRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : JumuaRegister => JumuaInvariant.gatheredRemembranceBearing)
      JumuaInvariant.gatheredRemembranceBearing :=
  TruthOneManyNamesWitness.constant_names_agree JumuaInvariant.gatheredRemembranceBearing

theorem jumua_quality_clusters_shape :
    jumuaQualityClusters.length = 5 ∧
    jumuaQualityClusters.head? = some .glorificationSovereigntyAndMessengerPedagogy ∧
    jumuaQualityClusters.getLast? = some .fridayCallTradeDiversionAndBetterProvision := by
  exact ⟨rfl, rfl, rfl⟩

theorem jumua_sat_witness : jumuaSat jumuaInvariantLedger := by
  unfold jumuaSat jumuaInvariantLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem jumua_gap_witness : jumuaGapsExposeBoundary jumuaGapLedger := by
  unfold jumuaGapsExposeBoundary jumuaGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem jumua_access_archaeological :
    jumuaSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological := by
  rfl

theorem quran_al_jumua_sura_quality_witness :
    jumuaQualityClusters.length = 5 ∧ jumuaSat jumuaInvariantLedger ∧
    jumuaGapsExposeBoundary jumuaGapLedger ∧
    jumuaSuraAccess.mode = Gnosis.ArchaeologicalInfinityAccess.AccessMode.archaeological ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : JumuaRegister => JumuaInvariant.gatheredRemembranceBearing)
      JumuaInvariant.gatheredRemembranceBearing := by
  exact ⟨jumua_quality_clusters_shape.left, jumua_sat_witness, jumua_gap_witness,
    jumua_access_archaeological, jumuaRegistersAgree⟩

end QuranAlJumuaSuraQualityWitness
end Gnosis.Witnesses.Islam
