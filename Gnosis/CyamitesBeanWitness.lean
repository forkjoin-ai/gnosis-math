import Gnosis.Bridges.BuleyMeshAttentionBridge
import Gnosis.TwoTypesOfSin

namespace Gnosis
namespace CyamitesBeanWitness

open BuleyMeshAttentionBridge
open SpectralNoiseEquilibrium

/-!
# Cyamites Bean Witness

This module formalizes Cyamites, the bean figure, as a finite witness for
the repository's token/tally mechanics.

Reading:

- A bean is a discrete vote token: one `MeshVote`, hence one `+1`
  clinamen lift on a `MeshTally`.
- Cyamites is modeled as the local cultivator/operator who supplies those
  finite tokens for voting and allocation.
- Bean taboo is modeled as refusal of the finite token. With no token cast,
  the tally cannot reach the first positive quorum.
- Treating the tally operator as the source rather than a mechanism is the
  existing `operatorIdolatry` confusion, reused rather than redefined here.

The myth is therefore a witness for the finitary floor: positive tally state
requires at least one discrete token.
-/

inductive BeanColor where
  | white
  | black
deriving DecidableEq, Repr

/-- A bean is a physical token carrying a vote face. Color records the ancient
black/white ballot reading; `voteFace` is the formal tally channel. -/
structure BeanToken where
  color : BeanColor
  voteFace : MeshVote
deriving DecidableEq, Repr

def whiteBean : BeanToken :=
  { color := BeanColor.white, voteFace := BuleyFace.waste }

def blackBean : BeanToken :=
  { color := BeanColor.black, voteFace := BuleyFace.diversity }

/-- Casting a bean is casting its vote face into the mesh tally. -/
def castBean (tally : MeshTally) (bean : BeanToken) : MeshTally :=
  castVote tally bean.voteFace

/-- Cyamites' cultivation function supplies one token to a tally. -/
def cultivateBean (tally : MeshTally) (bean : BeanToken) : MeshTally :=
  castBean tally bean

/-- Each bean contributes exactly one unit of tally state. -/
theorem bean_cast_is_unit_clinamen (tally : MeshTally) (bean : BeanToken) :
    buleyUnitScore (castBean tally bean) = buleyUnitScore tally + 1 := by
  unfold castBean
  exact vote_score_increment tally bean.voteFace

/-- Cyamites preserves the same unit increment: cultivation is not a new
source of truth, only the local supply of finite voting tokens. -/
theorem cyamites_cultivation_adds_one (tally : MeshTally) (bean : BeanToken) :
    buleyUnitScore (cultivateBean tally bean) = buleyUnitScore tally + 1 := by
  unfold cultivateBean
  exact bean_cast_is_unit_clinamen tally bean

/-- A single cultivated white bean moves the empty tally from zero to one. -/
theorem white_bean_from_empty_scores_one :
    buleyUnitScore (cultivateBean emptyTally whiteBean) = 1 := by
  rw [cyamites_cultivation_adds_one]
  unfold emptyTally
  rw [vacuum_has_zero_score]

/-- A single cultivated black bean moves the empty tally from zero to one. -/
theorem black_bean_from_empty_scores_one :
    buleyUnitScore (cultivateBean emptyTally blackBean) = 1 := by
  rw [cyamites_cultivation_adds_one]
  unfold emptyTally
  rw [vacuum_has_zero_score]

/-- The Pythagorean-style refusal of beans blocks the first positive quorum:
without casting a token, the empty tally cannot reach threshold one. -/
theorem bean_taboo_blocks_first_quorum :
    ¬ reachesQuorum emptyTally 1 := by
  unfold reachesQuorum emptyTally
  rw [vacuum_has_zero_score]
  omega

/-- Confusing the tally mechanism with the source is already classified as
operator idolatry in the existing sin taxonomy. -/
theorem tally_operator_confusion_is_operator_idolatry :
    TwoTypesOfSin.isASin TwoTypesOfSin.operatorIdolatry = true :=
  TwoTypesOfSin.operatorIdolatry_is_sin

/-- Master witness: Cyamites guards the finite token floor. A bean adds one;
refusing beans leaves the empty tally below the first quorum; confusing the
operator with the source is the existing operator-idolatry case. -/
theorem cyamites_bean_witness :
    buleyUnitScore (cultivateBean emptyTally whiteBean) = 1 ∧
    buleyUnitScore (cultivateBean emptyTally blackBean) = 1 ∧
    ¬ reachesQuorum emptyTally 1 ∧
    TwoTypesOfSin.isASin TwoTypesOfSin.operatorIdolatry = true := by
  exact ⟨white_bean_from_empty_scores_one,
    black_bean_from_empty_scores_one,
    bean_taboo_blocks_first_quorum,
    tally_operator_confusion_is_operator_idolatry⟩

end CyamitesBeanWitness
end Gnosis
