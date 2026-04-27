import Gnosis.SpectralNoiseEquilibrium
import Gnosis.BuleyClinamenBraid

/-!
# Buley ↔ Mesh Attention Bridge

The mesh-attention-as-voting picture (cf. `Gnosis.MeshAttentionAsVoting`,
`Gnosis.MeshCharismaAttention`) reads attention scores as votes cast
across distributed nodes, with charisma weighting which channel a vote
flows into. This module formalizes that picture inside the Bule
calculus:

* a **vote** is a `+1` clinamen lift on a chosen `BuleyFace`;
* a **charisma face** is the face the voter biases toward;
* a **quorum threshold** is a lower bound on the Bule unit's score;
* **vote independence** is the conservation law `clinamen_lift_commutes`
  — order of votes on distinct faces does not change the outcome;
* **gauge invariance** is `cyclePermute` — relabeling which face is
  Q vs K vs V (or waste vs opportunity vs diversity) preserves the
  score.

All theorems are reused from `Gnosis.SpectralNoiseEquilibrium` and
restated in voting vocabulary.

Imports `Gnosis.SpectralNoiseEquilibrium` and `Gnosis.BuleyClinamenBraid`.
Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace BuleyMeshAttentionBridge

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit clinamenLift
   cyclePermute clinamen_lift_score_strict_increment
   clinamen_lift_commutes
   cycle_permute_preserves_score
   cycle_permute_three_times_returns)

/-! ## Vote = clinamen lift -/

abbrev MeshVote := BuleyFace
abbrev MeshTally := BuleyUnit

def emptyTally : MeshTally := vacuumBuleUnit

def castVote (tally : MeshTally) (vote : MeshVote) : MeshTally :=
  clinamenLift tally vote

theorem empty_tally_has_zero_score :
    buleyUnitScore emptyTally = 0 := rfl

/-- Each vote adds exactly +1 to the tally's score. The unit clinamen
residue from `UniversalClinamenPlusOne` is exactly one vote. -/
theorem vote_score_increment (tally : MeshTally) (vote : MeshVote) :
    buleyUnitScore (castVote tally vote) = buleyUnitScore tally + 1 :=
  clinamen_lift_score_strict_increment tally vote

/-! ## Vote independence: votes on distinct channels commute -/

/-- Two votes on different channels commute — the order they arrive
doesn't change the final tally. This is the mesh's distributed-vote
conservation law, lifted from `clinamen_lift_commutes`. -/
theorem votes_commute (tally : MeshTally) (v1 v2 : MeshVote) :
    castVote (castVote tally v1) v2 = castVote (castVote tally v2) v1 :=
  clinamen_lift_commutes tally v1 v2

/-! ## Charisma face — biased toward one channel -/

/-- A charisma profile picks one of the three faces as the preferred
channel for incoming votes. -/
abbrev CharismaProfile := BuleyFace

def charismaVote (tally : MeshTally) (profile : CharismaProfile) : MeshTally :=
  castVote tally profile

theorem charisma_vote_score_increment (tally : MeshTally) (profile : CharismaProfile) :
    buleyUnitScore (charismaVote tally profile) = buleyUnitScore tally + 1 :=
  vote_score_increment tally profile

/-! ## Quorum threshold = Bule score lower bound -/

def reachesQuorum (tally : MeshTally) (threshold : Nat) : Prop :=
  buleyUnitScore tally ≥ threshold

theorem quorum_after_n_votes
    (tally : MeshTally) (vote : MeshVote) (threshold : Nat)
    (h : buleyUnitScore tally ≥ threshold) :
    reachesQuorum (castVote tally vote) threshold := by
  unfold reachesQuorum
  rw [vote_score_increment]
  omega

theorem quorum_one_vote_short
    (tally : MeshTally) (threshold : Nat)
    (h : buleyUnitScore tally + 1 = threshold) (vote : MeshVote) :
    reachesQuorum (castVote tally vote) threshold := by
  unfold reachesQuorum
  rw [vote_score_increment]
  omega

/-! ## Gauge invariance: relabeling Q/K/V channels preserves the tally -/

/-- Cyclic relabeling of the three channels preserves the tally's
score. This is the formal statement that Q, K, V are interchangeable
labels — the underlying mesh-attention dynamics depend on the channel
*structure*, not the names. -/
theorem relabel_channels_preserves_score (tally : MeshTally) :
    buleyUnitScore (cyclePermute tally) = buleyUnitScore tally :=
  cycle_permute_preserves_score tally

theorem three_relabels_return_to_self (tally : MeshTally) :
    cyclePermute (cyclePermute (cyclePermute tally)) = tally :=
  cycle_permute_three_times_returns tally

end BuleyMeshAttentionBridge
end Gnosis
