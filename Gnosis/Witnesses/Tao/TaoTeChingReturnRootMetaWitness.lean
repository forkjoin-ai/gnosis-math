import Gnosis.TruthOneManyNamesWitness
import Gnosis.Witnesses.Tao.TaoTeChingNameMysteryWitness
import Gnosis.Witnesses.Tao.TaoTeChingVoidSensorWitness
import Gnosis.Witnesses.Tao.TaoTeChingReturnRootWitness
import Gnosis.Witnesses.Tao.TaoTeChingSourceCompletionWitness
import Gnosis.Witnesses.Tao.TaoTeChingTraceLessGovernanceWitness
import Gnosis.Witnesses.Tao.TaoTeChingHiddenDiminishingWitness
import Gnosis.Witnesses.Tao.TaoTeChingLowPlaceWuWeiWitness
import Gnosis.Witnesses.Tao.TaoTeChingClosingCounterproofWitness

namespace Gnosis.Witnesses.Tao
namespace TaoTeChingReturnRootMetaWitness

/-!
# Tao Te Ching Return-Root Meta Witness

Tao-wide synthesis after the chapter-wave witnesses. The repeated invariant is
not generic quietism. It is a runtime law:

  * names teach only while they do not capture the enduring source;
  * void is the use-site of wheel, vessel, room, bellows, valley, and low water;
  * motion remains valid only while stillness/root remains underneath it;
  * completion arrives by partiality, emptiness, diminishing, and return;
  * false knowing, hard strength, forced reach, and accumulation expose the
    boundary where process has left Tao.

No `sorry`, no new `axiom`.
-/

inductive TaoMetaOperator
  | nameBoundary
  | voidUseSite
  | rootStillness
  | completionByLack
  | traceLessGovernance
  | diminishingPractice
  | lowPlaceWuWei
  | closingCounterproof
deriving DecidableEq, Repr

def taoMetaOperators : List TaoMetaOperator :=
  [ TaoMetaOperator.nameBoundary
  , TaoMetaOperator.voidUseSite
  , TaoMetaOperator.rootStillness
  , TaoMetaOperator.completionByLack
  , TaoMetaOperator.traceLessGovernance
  , TaoMetaOperator.diminishingPractice
  , TaoMetaOperator.lowPlaceWuWei
  , TaoMetaOperator.closingCounterproof
  ]

structure TaoReturnRootLedger where
  nameCaptureFails : Bool := true
  voidCarriesUse : Bool := true
  stillnessReturnsToRoot : Bool := true
  sourceCompletesThroughLack : Bool := true
  namedActionRestsBackIntoNoName : Bool := true
  practiceDiminishesDoing : Bool := true
  lowPlaceReceivesAndWins : Bool := true
  closingRejectsFalseKnowingAndHardness : Bool := true
deriving DecidableEq, Repr

def taoReturnRootLedger : TaoReturnRootLedger := {}

def returnRootInvariant (l : TaoReturnRootLedger) : Prop :=
  l.nameCaptureFails = true ∧
  l.voidCarriesUse = true ∧
  l.stillnessReturnsToRoot = true ∧
  l.sourceCompletesThroughLack = true ∧
  l.namedActionRestsBackIntoNoName = true ∧
  l.practiceDiminishesDoing = true ∧
  l.lowPlaceReceivesAndWins = true ∧
  l.closingRejectsFalseKnowingAndHardness = true

structure TaoReturnRootGapLedger where
  namedNameCanPretendToEndure : Bool := true
  fullnessCanHideUse : Bool := true
  activeMovementCanLoseRoot : Bool := true
  selfDisplayCanMissCompletion : Bool := true
  coerciveTraceCanCaptureGovernance : Bool := true
  accumulationCanBlockTao : Bool := true
  hardStrengthCanSignalDeath : Bool := true
deriving DecidableEq, Repr

def taoReturnRootGapLedger : TaoReturnRootGapLedger := {}

def returnRootGapsExposeBoundary (g : TaoReturnRootGapLedger) : Prop :=
  g.namedNameCanPretendToEndure = true ∧
  g.fullnessCanHideUse = true ∧
  g.activeMovementCanLoseRoot = true ∧
  g.selfDisplayCanMissCompletion = true ∧
  g.coerciveTraceCanCaptureGovernance = true ∧
  g.accumulationCanBlockTao = true ∧
  g.hardStrengthCanSignalDeath = true

inductive TaoMetaRegister
  | name
  | void
  | root
  | lack
  | noName
  | diminish
  | lowPlace
  | closing
deriving DecidableEq, Repr, Nonempty

inductive TaoMetaInvariant
  | returnRoot
deriving DecidableEq, Repr

def taoMetaRegistersAgree :
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TaoMetaRegister => TaoMetaInvariant.returnRoot)
      TaoMetaInvariant.returnRoot :=
  TruthOneManyNamesWitness.constant_names_agree TaoMetaInvariant.returnRoot

theorem tao_meta_operators_shape :
    taoMetaOperators.length = 8 ∧
    taoMetaOperators.head? = some TaoMetaOperator.nameBoundary ∧
    taoMetaOperators.getLast? = some TaoMetaOperator.closingCounterproof := by
  exact ⟨rfl, rfl, rfl⟩

theorem tao_return_root_invariant :
    returnRootInvariant taoReturnRootLedger := by
  unfold returnRootInvariant taoReturnRootLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tao_return_root_gaps :
    returnRootGapsExposeBoundary taoReturnRootGapLedger := by
  unfold returnRootGapsExposeBoundary taoReturnRootGapLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tao_chapter_witnesses_support_return_root :
    TaoTeChingNameMysteryWitness.nameCaptureFailsButTeaches
      TaoTeChingNameMysteryWitness.taoNameBoundary ∧
    TaoTeChingVoidSensorWitness.voidIsUseSite
      TaoTeChingVoidSensorWitness.taoProductiveVoid ∧
    TaoTeChingReturnRootWitness.rootReturnStillness
      TaoTeChingReturnRootWitness.taoStillnessClears ∧
    activeForceSource.sourceIsTao = true ∧
    completionByLack.emptyFull = true ∧
    returnLawChain.greatPassesRemoteReturns = true ∧
    noNameGovernance.namedActionRequiresRest = true ∧
    diminishingPractice.taoDiminishesDoing = true ∧
    gentleNonContention.seasRuleByBeingLower = true ∧
    hiddenJadeNonKnowledge.falseKnowingDisease = true ∧
    hardnessCounterproofs.waterSoftOvercomesHard = true := by
  exact ⟨
    TaoTeChingNameMysteryWitness.tao_name_boundary,
    TaoTeChingVoidSensorWitness.tao_void_use_site,
    TaoTeChingReturnRootWitness.tao_root_return_stillness,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tao_te_ching_return_root_meta_witness :
    taoMetaOperators.length = 8 ∧
    returnRootInvariant taoReturnRootLedger ∧
    returnRootGapsExposeBoundary taoReturnRootGapLedger ∧
    TruthOneManyNamesWitness.manyNamesAgree
      (fun _ : TaoMetaRegister => TaoMetaInvariant.returnRoot)
      TaoMetaInvariant.returnRoot ∧
    TaoTeChingReturnRootWitness.rootReturnStillness
      TaoTeChingReturnRootWitness.taoStillnessClears ∧
    completionByLack.emptyFull = true ∧
    noNameGovernance.namedActionRequiresRest = true ∧
    diminishingPractice.taoDiminishesDoing = true ∧
    smallStateClosing.sageDoesNotStrive = true := by
  exact ⟨tao_meta_operators_shape.left,
    tao_return_root_invariant,
    tao_return_root_gaps,
    taoMetaRegistersAgree,
    TaoTeChingReturnRootWitness.tao_root_return_stillness,
    rfl, rfl, rfl, rfl⟩

end TaoTeChingReturnRootMetaWitness
end Gnosis.Witnesses.Tao
