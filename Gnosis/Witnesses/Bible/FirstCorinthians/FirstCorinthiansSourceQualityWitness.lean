import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansCrossFoolishnessChosenWitness
import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansCarnalBuildersTempleWitness
import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansDisciplineLeavenWitness
import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansIdolKnowledgeCharityWitness
import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansOrdinancesSupperWitness
import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansGiftsBodyWitness
import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansCharityWitness
import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansProphecyOrderWitness
import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansResurrectionVictoryWitness
import Gnosis.Witnesses.Bible.FirstCorinthians.FirstCorinthiansCollectionFinalChargeWitness

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansSourceQualityWitness

/-!
# 1 Corinthians -- Source Quality Spine

Book-level invariant: 1 Corinthians is not a grab bag of church problems. It is
an anti-fragmentation machine. The cross breaks name-faction prestige; the
Spirit breaks rhetoric prestige; the temple/body witnesses make private conduct
publicly structural; the supper exposes consumption without discernment; gifts
are routed through one body; charity outranks spectacular signal; resurrection
keeps labor from becoming vanity.

Primary gap/counterproof: Corinth keeps trying to turn real gifts into private
rank. Wisdom becomes faction, liberty becomes damage, supper becomes appetite,
tongues become noise, and even knowledge becomes destructive unless charity
governs it.

Unseen sat: the strangest line is that resurrection is operational. If the dead
rise not, preaching and faith are vain; if Christ is raised, the last enemy is
being destroyed and ordinary labor is not vain. The body is therefore not a
metaphor only. It is the audit surface where doctrine either coheres or splits.

No `sorry`, no new `axiom`.
-/

structure FirstCorinthiansBookInvariant where
  crossBreaksPrestigeFactions : Bool := true
  buildersMustRespectTemple : Bool := true
  leavenRequiresCommunalPurge : Bool := true
  knowledgeMustServeCharity : Bool := true
  supperRequiresBodyDiscernment : Bool := true
  giftsNeedOneBodyOrdering : Bool := true
  charityOutranksSpectacle : Bool := true
  prophecySeeksEdifyingOrder : Bool := true
  resurrectionMakesLaborNotVain : Bool := true
  collectionAndFinalChargeKeepBodyMaterial : Bool := true
deriving DecidableEq, Repr

def firstCorinthiansBookInvariant : FirstCorinthiansBookInvariant := {}

def firstCorinthiansQualitySpine (f : FirstCorinthiansBookInvariant) : Prop :=
  f.crossBreaksPrestigeFactions = true ∧
  f.buildersMustRespectTemple = true ∧
  f.leavenRequiresCommunalPurge = true ∧
  f.knowledgeMustServeCharity = true ∧
  f.supperRequiresBodyDiscernment = true ∧
  f.giftsNeedOneBodyOrdering = true ∧
  f.charityOutranksSpectacle = true ∧
  f.prophecySeeksEdifyingOrder = true ∧
  f.resurrectionMakesLaborNotVain = true ∧
  f.collectionAndFinalChargeKeepBodyMaterial = true

theorem first_corinthians_source_quality_spine :
    firstCorinthiansQualitySpine firstCorinthiansBookInvariant := by
  unfold firstCorinthiansQualitySpine firstCorinthiansBookInvariant
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_corinthians_source_quality_witness :
    firstCorinthiansQualitySpine firstCorinthiansBookInvariant := by
  have _ := FirstCorinthiansCrossFoolishnessChosenWitness.first_corinthians_cross_foolishness_chosen_witness
  have _ := FirstCorinthiansCarnalBuildersTempleWitness.first_corinthians_carnal_builders_temple_witness
  have _ := FirstCorinthiansDisciplineLeavenWitness.first_corinthians_discipline_leaven_witness
  have _ := FirstCorinthiansIdolKnowledgeCharityWitness.first_corinthians_idol_knowledge_charity_witness
  have _ := FirstCorinthiansOrdinancesSupperWitness.first_corinthians_ordinances_supper_witness
  have _ := FirstCorinthiansGiftsBodyWitness.first_corinthians_gifts_body_witness
  have _ := FirstCorinthiansCharityWitness.first_corinthians_charity_witness
  have _ := FirstCorinthiansProphecyOrderWitness.first_corinthians_prophecy_order_witness
  have _ := FirstCorinthiansResurrectionVictoryWitness.first_corinthians_resurrection_victory_witness
  have _ := FirstCorinthiansCollectionFinalChargeWitness.first_corinthians_collection_final_charge_witness
  exact first_corinthians_source_quality_spine

end FirstCorinthiansSourceQualityWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
