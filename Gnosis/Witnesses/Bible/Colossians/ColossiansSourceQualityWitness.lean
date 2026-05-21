import Gnosis.Witnesses.Bible.Colossians.ColossiansAboveOldNewCharityWitness
import Gnosis.Witnesses.Bible.Colossians.ColossiansCompleteInChristWitness
import Gnosis.Witnesses.Bible.Colossians.ColossiansFruitTransferChristologyWitness
import Gnosis.Witnesses.Bible.Colossians.ColossiansHouseholdPrayerEnvoysWitness
import Gnosis.Witnesses.Bible.Colossians.ColossiansReconciliationMysteryWitness
import Gnosis.Witnesses.Bible.Colossians.ColossiansShadowHeadRudimentsWitness

namespace Gnosis.Witnesses.Bible.Colossians
namespace ColossiansSourceQualityWitness

/-!
# Colossians -- Source Quality Spine

This repair module is the interpretive spine for the fast Colossians pass. The
book invariant is head-held completeness: all things cohere in Christ, fullness
dwells bodily in him, and the body grows only while holding the Head.

Primary gap/counterproof: every supplement tries to complete the complete:
philosophy, tradition, rudiments, angelic intrusion, food/day shadows, ascetic
handling rules, and household hierarchy detached from the Lord. Colossians
records these as completion-forgeries.

Unseen sat: the visible ethical surface is downstream of cosmic coherence. Old
and new, above and earth, household and speech only stabilize when Christ remains
the non-substitutable head.

No `sorry`, no new `axiom`.
-/

structure ColossiansInvariant where
  allThingsConsistInChrist : Bool := true
  fullnessDwellsBodily : Bool := true
  believersCompleteInHead : Bool := true
  bodyIncreaseRequiresHoldingHead : Bool := true
deriving DecidableEq, Repr

def colossiansInvariant : ColossiansInvariant := {}

def headHeldCompleteness (i : ColossiansInvariant) : Prop :=
  i.allThingsConsistInChrist = true ∧
  i.fullnessDwellsBodily = true ∧
  i.believersCompleteInHead = true ∧
  i.bodyIncreaseRequiresHoldingHead = true

structure ColossiansCounterproof where
  philosophyCannotCompleteFullness : Bool := true
  shadowCannotReplaceBody : Bool := true
  angelIntrusionCannotReplaceHead : Bool := true
  touchTasteHandleCannotMortifyFlesh : Bool := true
  earthlyMembersCannotGovernHiddenLife : Bool := true
deriving DecidableEq, Repr

def colossiansCounterproof : ColossiansCounterproof := {}

def completionForgeriesRejected (c : ColossiansCounterproof) : Prop :=
  c.philosophyCannotCompleteFullness = true ∧
  c.shadowCannotReplaceBody = true ∧
  c.angelIntrusionCannotReplaceHead = true ∧
  c.touchTasteHandleCannotMortifyFlesh = true ∧
  c.earthlyMembersCannotGovernHiddenLife = true

theorem colossians_quality_invariant :
    headHeldCompleteness colossiansInvariant := by
  unfold headHeldCompleteness colossiansInvariant
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem colossians_quality_counterproof :
    completionForgeriesRejected colossiansCounterproof := by
  unfold completionForgeriesRejected colossiansCounterproof
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem colossians_source_quality_witness :
    headHeldCompleteness colossiansInvariant ∧
    completionForgeriesRejected colossiansCounterproof ∧
    ColossiansFruitTransferChristologyWitness.transferChristologyWitness
      ColossiansFruitTransferChristologyWitness.transferChristology ∧
    ColossiansCompleteInChristWitness.completeInChristWitness
      ColossiansCompleteInChristWitness.completeInChrist ∧
    ColossiansShadowHeadRudimentsWitness.shadowHeadBoundary
      ColossiansShadowHeadRudimentsWitness.shadowJudgment ∧
    ColossiansAboveOldNewCharityWitness.oldNewCharityWitness
      ColossiansAboveOldNewCharityWitness.oldNewCharity := by
  exact ⟨colossians_quality_invariant,
    colossians_quality_counterproof,
    ColossiansFruitTransferChristologyWitness.colossians_transfer_christology,
    ColossiansCompleteInChristWitness.colossians_complete_in_christ,
    ColossiansShadowHeadRudimentsWitness.colossians_shadow_head_boundary,
    ColossiansAboveOldNewCharityWitness.colossians_old_new_charity⟩

end ColossiansSourceQualityWitness
end Gnosis.Witnesses.Bible.Colossians
