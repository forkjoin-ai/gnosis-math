import Gnosis.GnosisTriptychBraid
import Gnosis.TruthOneManyNamesWitness

namespace Gnosis.Witnesses.Tao

/-!
# Tao Te Ching Source Completion Witness

Witness ledger for `docs/ebooks/source-texts/tao-te-ching-legge.txt`,
chapters 21-25.

These chapters deepen the earlier name-boundary witness. Tao functions as the
source of active force while evading sight and touch; completion appears through
partiality, crookedness, emptiness, and wear rather than through maximal display.
The counterproof is egoic over-extension: many desires, self-display, tiptoe
standing, and stretched-leg walking all lose the root they try to advertise.
-/

/-- Chapter 21: the active force has Tao as source, while sensory capture fails. -/
structure ActiveForceSource where
  sourceIsTao : Bool := true
  sightFails : Bool := true
  touchFails : Bool := true
  essencesEndure : Bool := true
  enduringName : Bool := true
deriving Repr, DecidableEq

/-- Chapters 22 and 24: completion is recovered through lack, not through display. -/
structure CompletionByLack where
  partialComplete : Bool := true
  crookedStraight : Bool := true
  emptyFull : Bool := true
  wornNew : Bool := true
  fewDesiresReceive : Bool := true
  manyDesiresAstray : Bool := true
  selfDisplayFails : Bool := true
deriving Repr, DecidableEq

/-- Chapter 25: the great unnamed source returns and grounds the law-chain. -/
structure ReturnLawChain where
  beforeHeavenEarth : Bool := true
  unnamedMother : Bool := true
  greatPassesRemoteReturns : Bool := true
  earthLawForMan : Bool := true
  heavenLawForEarth : Bool := true
  taoLawForHeaven : Bool := true
  taoLawSelfSo : Bool := true
deriving Repr, DecidableEq

def activeForceSource : ActiveForceSource := {}

def completionByLack : CompletionByLack := {}

def returnLawChain : ReturnLawChain := {}

theorem tao_active_force_source :
    activeForceSource.sourceIsTao = true ∧
      activeForceSource.sightFails = true ∧
      activeForceSource.touchFails = true ∧
      activeForceSource.essencesEndure = true ∧
      activeForceSource.enduringName = true := by
  simp [activeForceSource]

theorem tao_completion_by_lack :
    completionByLack.partialComplete = true ∧
      completionByLack.crookedStraight = true ∧
      completionByLack.emptyFull = true ∧
      completionByLack.wornNew = true ∧
      completionByLack.fewDesiresReceive = true ∧
      completionByLack.manyDesiresAstray = true ∧
      completionByLack.selfDisplayFails = true := by
  simp [completionByLack]

theorem tao_return_law_chain :
    returnLawChain.beforeHeavenEarth = true ∧
      returnLawChain.unnamedMother = true ∧
      returnLawChain.greatPassesRemoteReturns = true ∧
      returnLawChain.earthLawForMan = true ∧
      returnLawChain.heavenLawForEarth = true ∧
      returnLawChain.taoLawForHeaven = true ∧
      returnLawChain.taoLawSelfSo = true := by
  simp [returnLawChain]

/--
Chapters 21-25 witness that the Tao source is not reached by louder naming or
larger possession. The runtime-relevant invariant is negative: the source powers
forms, yet the attempt to capture it by sight, grasp, desire, display, or
over-stride fails.
-/
theorem tao_te_ching_source_completion_witness :
    activeForceSource.sourceIsTao = true ∧
      completionByLack.emptyFull = true ∧
      completionByLack.selfDisplayFails = true ∧
      returnLawChain.unnamedMother = true ∧
      returnLawChain.taoLawSelfSo = true := by
  simp [activeForceSource, completionByLack, returnLawChain]

end Gnosis.Witnesses.Tao
