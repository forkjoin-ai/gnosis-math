import Gnosis.Witnesses.Bible.Galatians.GalatiansAbrahamFaithBlessingWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansLawCurseRedeemedWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansPromiseBeforeLawWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansSchoolmasterUnityWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansSpiritFaithFleshWitness
import Gnosis.Witnesses.Bible.Torah.DeuteronomyLawCurseTreeWitness
import Gnosis.Witnesses.Bible.Torah.GenesisPromiseSeedBlessingWitness

namespace Gnosis.Witnesses.Bible.Torah
namespace TorahGalatiansPromiseLawTandemWitness

/-!
# Torah/Galatians Tandem -- Promise, Law, Curse, and Schoolmaster

This bridge prevents duplicate coverage. Genesis owns seed/blessing source
anchors; Leviticus and Deuteronomy own law/curse source anchors; Galatians 3
owns the apostolic projection: faith receives the Spirit, promise precedes law,
law functions as schoolmaster, and unity heirship follows promise.

No `sorry`, no new `axiom`.
-/

structure TandemCoverageBoundary where
  genesisOwnsPromiseSource : Bool := true
  torahOwnsLawAndCurseSource : Bool := true
  galatiansOwnsFaithProjection : Bool := true
  duplicateSourceCoverageRejected : Bool := true
  bridgeRecordsSemanticOverlap : Bool := true
deriving DecidableEq, Repr

def tandemCoverageBoundary : TandemCoverageBoundary := {}

def noDuplicateCoverageBoundary (b : TandemCoverageBoundary) : Prop :=
  b.genesisOwnsPromiseSource = true ∧
  b.torahOwnsLawAndCurseSource = true ∧
  b.galatiansOwnsFaithProjection = true ∧
  b.duplicateSourceCoverageRejected = true ∧
  b.bridgeRecordsSemanticOverlap = true

theorem torah_galatians_no_duplicate_coverage :
    noDuplicateCoverageBoundary tandemCoverageBoundary := by
  unfold noDuplicateCoverageBoundary tandemCoverageBoundary
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem torah_galatians_promise_law_tandem_witness :
    GenesisPromiseSeedBlessingWitness.seedPromiseAnchor
      GenesisPromiseSeedBlessingWitness.genesisSeedPromise ∧
    GenesisPromiseSeedBlessingWitness.nationsBlessingAnchor
      GenesisPromiseSeedBlessingWitness.genesisNationsBlessing ∧
    DeuteronomyLawCurseTreeWitness.doAndLiveAnchor
      DeuteronomyLawCurseTreeWitness.doAndLiveLedger ∧
    DeuteronomyLawCurseTreeWitness.curseLedgerAnchor
      DeuteronomyLawCurseTreeWitness.curseLedger ∧
    Galatians.GalatiansSpiritFaithFleshWitness.fleshCompletionGap
      Galatians.GalatiansSpiritFaithFleshWitness.bewitchedRegression ∧
    Galatians.GalatiansAbrahamFaithBlessingWitness.nationsBlessedByFaith
      Galatians.GalatiansAbrahamFaithBlessingWitness.nationsBlessingSignal ∧
    Galatians.GalatiansLawCurseRedeemedWitness.curseReroutedToPromise
      Galatians.GalatiansLawCurseRedeemedWitness.redeemedFromCurse ∧
    Galatians.GalatiansPromiseBeforeLawWitness.inheritanceByPromiseNotLaw
      Galatians.GalatiansPromiseBeforeLawWitness.lawAfterPromise ∧
    Galatians.GalatiansSchoolmasterUnityWitness.unityHeirshipByPromise
      Galatians.GalatiansSchoolmasterUnityWitness.unityHeirship ∧
    noDuplicateCoverageBoundary tandemCoverageBoundary := by
  exact ⟨GenesisPromiseSeedBlessingWitness.genesis_seed_promise_anchor,
    GenesisPromiseSeedBlessingWitness.genesis_nations_blessing_anchor,
    DeuteronomyLawCurseTreeWitness.torah_do_and_live_anchor,
    DeuteronomyLawCurseTreeWitness.torah_curse_ledger_anchor,
    Galatians.GalatiansSpiritFaithFleshWitness.galatians_flesh_completion_gap,
    Galatians.GalatiansAbrahamFaithBlessingWitness.galatians_nations_blessed_by_faith,
    Galatians.GalatiansLawCurseRedeemedWitness.galatians_curse_rerouted_to_promise,
    Galatians.GalatiansPromiseBeforeLawWitness.galatians_inheritance_by_promise_not_law,
    Galatians.GalatiansSchoolmasterUnityWitness.galatians_unity_heirship_by_promise,
    torah_galatians_no_duplicate_coverage⟩

end TorahGalatiansPromiseLawTandemWitness
end Gnosis.Witnesses.Bible.Torah
