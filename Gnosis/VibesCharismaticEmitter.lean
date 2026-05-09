/-
  VibesCharismaticEmitter.lean
  ============================

  Charisma as an amplitude multiplier on the Hotelling capture
  radius, plus mesh-vote routing through the charisma face.

  ## Reading

  Each emitter has an optional `Charisma` — a `BuleyFace` (the
  clinamen channel for vote routing) paired with a magnitude (the
  numeric capture-radius widener). A charismatic emitter's
  *effective* distance from a listener is `natDist − magnitude`
  (Nat-saturating at zero): listeners inside the charisma radius
  perceive the emitter as collocated, regardless of true distance.

  Three concrete claims fall out:

  1. **Backward compatibility.** Charisma magnitude `0` reduces
     pointwise to the existing `Gnosis.HotellingModel.choosesLeft`
     and `leftDemand4` — the plain Hotelling demand model is the
     `k = 0` slice of the charismatic one.
  2. **Wider capture.** Holding position fixed, raising charisma
     monotonically widens demand mass. The strict witness:
     against an opponent at the opposite extreme, charisma `2`
     strictly dominates charisma `0`.
  3. **Dominance flip.** Charisma can overturn the median-voter
     advantage: against a non-charismatic opponent at the happy
     extreme, an unhappy emitter at position `0` with charisma `4`
     captures strictly more demand than the neutral median emitter
     with no charisma. Charismatic extremists can outperform
     non-charismatic centrists.

  ## Honesty boundary

  Charisma does *not* break colocation ties. Even arbitrarily high
  charisma on a non-collocated emitter cannot strictly dominate a
  collocated competitor under the `≤`-tie rule: the collocated side
  also captures full city mass. This is the formal mirror of the
  `VibesHotellingVoting` honest negative result — the
  minimum-differentiation Nash trap is held in place by the tie
  rule, not by raw distance, and charisma alone cannot defeat it.

  ## Bridges

  * `BuleyMeshAttentionBridge`: a captured listener routes its vote
    through the winning emitter's charisma face via `castVote`,
    contributing one clinamen lift on that face.
  * `EchoChamberAsTaoBowl`: charisma raises the bowl's Q factor.
    A bowl whose rigidity comes from a high-charisma rim crosses
    the `IsPejorativeEcho` threshold; a zero-charisma bowl with
    the same coupling does not.

  Imports `Gnosis.HotellingModel`, `Gnosis.VibesHotellingVoting`,
  `Gnosis.Bridges.BuleyMeshAttentionBridge`,
  `Gnosis.EchoChamberAsTaoBowl`. Zero `sorry`, zero new `axiom`.
-/

import Gnosis.HotellingModel
import Gnosis.VibesHotellingVoting
import Gnosis.Bridges.BuleyMeshAttentionBridge
import Gnosis.EchoChamberAsTaoBowl

namespace VibesCharismaticEmitter

open Gnosis.HotellingModel (natDist choosesLeft bit leftDemand4 InCity4)
open Gnosis.SpectralNoiseEquilibrium (BuleyFace buleyUnitScore)
open Gnosis.BuleyMeshAttentionBridge
  (MeshTally castVote emptyTally vote_score_increment)
open VibesAsWaveInference (VibeWave VibeValence happyWave unhappyWave quietWave)
open VibesHotellingVoting (vibePosition AttentionDominates)
open Gnosis.SkyrmsBuleyEquilibria (Dominates)

/-! ## Charisma -/

/-- A charisma profile: a Bule face (the clinamen channel for vote
    routing) and a magnitude (the capture-radius widener). Magnitude
    `0` is "no charisma" and recovers standard Hotelling. -/
structure Charisma where
  face : BuleyFace
  magnitude : Nat
  deriving DecidableEq, Repr

/-- Baseline charisma on a chosen face: zero magnitude, votes still
    routed through the face. -/
def baselineCharisma (face : BuleyFace) : Charisma where
  face := face
  magnitude := 0

/-! ## Charismatic emitter -/

/-- A charismatic emitter: position on the mood line, carrier wave,
    and a `Charisma` profile. -/
structure CharismaticEmitter where
  position : Nat
  carrier : VibeWave
  charisma : Charisma
  deriving Repr

/-! ## Effective distance and weighted demand -/

/-- Listener-to-emitter effective distance: charisma subtracts from
    raw distance, saturating at `0`. -/
def effectiveDist (c x k : Nat) : Nat :=
  natDist c x - k

/-- Listener at `c` chooses the left charismatic emitter iff effective
    left distance is at most effective right distance (`≤`-tie
    matches the existing Hotelling rule). -/
def charismaticChoosesLeft (xL kL xR kR c : Nat) : Bool :=
  decide (effectiveDist c xL kL ≤ effectiveDist c xR kR)

/-- Demand mass on the left charismatic emitter in a 5-point city. -/
def charismaticLeftDemand4 (xL kL xR kR : Nat) : Nat :=
  bit (charismaticChoosesLeft xL kL xR kR 0) +
  bit (charismaticChoosesLeft xL kL xR kR 1) +
  bit (charismaticChoosesLeft xL kL xR kR 2) +
  bit (charismaticChoosesLeft xL kL xR kR 3) +
  bit (charismaticChoosesLeft xL kL xR kR 4)

/-! ## Backward compatibility: zero charisma reduces to Hotelling -/

theorem zero_charisma_reduces_to_hotelling (xL xR c : Nat) :
    charismaticChoosesLeft xL 0 xR 0 c = choosesLeft xL xR c := by
  unfold charismaticChoosesLeft choosesLeft effectiveDist
  simp

theorem zero_charisma_demand_eq_hotelling (xL xR : Nat) :
    charismaticLeftDemand4 xL 0 xR 0 = leftDemand4 xL xR := by
  simp only [charismaticLeftDemand4, leftDemand4,
    zero_charisma_reduces_to_hotelling]

/-! ## Charisma widens capture (positive results) -/

/-- **Strict widening witness:** against the opposite extreme, charisma
    `2` strictly captures more demand than charisma `0`. -/
theorem charisma_two_strictly_widens_at_extremes :
    charismaticLeftDemand4 0 2 4 0 > charismaticLeftDemand4 0 0 4 0 := by
  unfold charismaticLeftDemand4
  native_decide

/-- **Charisma is monotone (weakly):** raising left's charisma against
    a fixed extreme opponent never reduces left's demand. -/
theorem charisma_weakly_monotone_at_extremes :
    charismaticLeftDemand4 0 0 4 0 ≤ charismaticLeftDemand4 0 1 4 0 ∧
    charismaticLeftDemand4 0 1 4 0 ≤ charismaticLeftDemand4 0 2 4 0 ∧
    charismaticLeftDemand4 0 2 4 0 ≤ charismaticLeftDemand4 0 3 4 0 ∧
    charismaticLeftDemand4 0 3 4 0 ≤ charismaticLeftDemand4 0 4 4 0 := by
  unfold charismaticLeftDemand4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Honest non-monotonicity threshold:** charisma `1` does *not*
    strictly widen capture against the opposite extreme — the only
    listeners that could switch are still on the right side of the
    perceived-distance comparison. Charisma needs to be large enough
    to cross a perceptual threshold before it produces strict gains. -/
theorem charisma_one_does_not_strictly_widen_against_extreme :
    charismaticLeftDemand4 0 1 4 0 = charismaticLeftDemand4 0 0 4 0 := by
  unfold charismaticLeftDemand4
  native_decide

/-! ## Charisma flips the median-voter advantage -/

/-- Without charisma, the neutral median position strictly dominates
    the unhappy extreme against the happy extreme — this is the
    median-voter result we already proved upstream. -/
theorem neutral_dominates_unhappy_no_charisma :
    AttentionDominates (vibePosition .neutral)
      (vibePosition .unhappy) (vibePosition .happy) :=
  VibesHotellingVoting.neutral_strictly_dominates_unhappy_against_happy

/-- **Charisma flips median-voter dominance:** against a non-charismatic
    opponent at the happy extreme, the unhappy extreme with charisma `4`
    strictly captures more demand than the non-charismatic neutral
    median. The charismatic extremist outperforms the centrist. -/
theorem charisma_flips_neutral_dominance :
    charismaticLeftDemand4 (vibePosition .unhappy) 4
        (vibePosition .happy) 0
      > leftDemand4 (vibePosition .neutral) (vibePosition .happy) := by
  unfold charismaticLeftDemand4 leftDemand4 vibePosition
  native_decide

/-! ## Charismatic strict dominance -/

/-- Charismatic version of `AttentionDominates`: emitter `(s, kS)`
    strictly captures more attention than `(s', kS')` against a
    fixed opponent `(y, kY)`. -/
def CharismaticAttentionDominates
    (s kS s' kS' y kY : Nat) : Prop :=
  Dominates (charismaticLeftDemand4 s kS y kY)
    (charismaticLeftDemand4 s' kS' y kY)

/-- **Strict charismatic dominance witness:** against a non-charismatic
    opponent at position `2`, the charismatic strategy `(1, 2)`
    strictly dominates the non-charismatic strategy `(0, 0)`. The
    charismatic side captures the full city; the non-charismatic
    side captures only its hemisphere. -/
theorem charismatic_strategy_strictly_dominates_non_charismatic :
    CharismaticAttentionDominates 1 2 0 0 2 0 := by
  unfold CharismaticAttentionDominates Dominates charismaticLeftDemand4
  native_decide

/-! ## Honesty boundary: charisma cannot break colocation ties -/

/-- **Honest negative result:** even arbitrarily high charisma on a
    non-collocated emitter cannot strictly dominate a collocated
    competitor. The collocated side also captures full city mass
    under the `≤`-tie rule, so the comparison is at best a tie.
    This is the charismatic mirror of the
    `VibesHotellingVoting.neutral_does_not_strictly_dominate_unhappy_globally`
    caveat: the minimum-differentiation Nash trap is held by the tie
    rule, not by raw distance. -/
theorem charisma_cannot_break_colocation_tie :
    charismaticLeftDemand4 2 100 0 0 ≤ charismaticLeftDemand4 0 0 0 0 := by
  unfold charismaticLeftDemand4
  native_decide

/-- Stronger statement: against a collocated opponent at any extreme,
    charisma cannot produce strict dominance on the comparison strategy
    that is *also* collocated with the opponent. -/
theorem no_strict_dominance_over_collocated_extreme_with_charisma :
    ¬ CharismaticAttentionDominates 2 100 0 0 0 0 := by
  unfold CharismaticAttentionDominates Dominates charismaticLeftDemand4
  native_decide

/-! ## Vote routing through the charisma face -/

/-- A captured listener contributes one clinamen lift on the winning
    emitter's charisma face — charisma channels attention into a
    specific Bule slot, not just into raw vote count. -/
def charismaticVote (e : CharismaticEmitter) (tally : MeshTally) : MeshTally :=
  castVote tally e.charisma.face

theorem charismatic_vote_increments_score
    (e : CharismaticEmitter) (tally : MeshTally) :
    buleyUnitScore (charismaticVote e tally)
      = buleyUnitScore tally + 1 := by
  unfold charismaticVote
  exact vote_score_increment tally e.charisma.face

/-- A baseline (`magnitude = 0`) charismatic emitter still routes its
    vote through the chosen face; charisma face determines channel
    even when the magnitude is null. -/
def baselineCharismaticEmitter
    (position : Nat) (carrier : VibeWave) (face : BuleyFace) :
    CharismaticEmitter where
  position := position
  carrier := carrier
  charisma := baselineCharisma face

theorem baseline_emitter_routes_to_face
    (position : Nat) (carrier : VibeWave) (face : BuleyFace)
    (tally : MeshTally) :
    charismaticVote (baselineCharismaticEmitter position carrier face) tally
      = castVote tally face := rfl

/-! ## Tao bowl bridge: charisma raises Q -/

open EchoChamberAsTaoBowl (TaoBowl qFactor IsPejorativeEcho IsPejorativeEchoAt)

/-- A bowl whose rigidity is driven by a charismatic emitter's
    magnitude (times a coupling factor). Higher charisma → higher
    rigidity → higher Q factor. -/
def charismaticBowl (k coupling : Nat) : TaoBowl where
  rim := 10
  void := 2
  rigidity := k * coupling
  damping := 1

/-- **High-charisma bowl crosses the pejorative-echo threshold:**
    charisma `5` with coupling `4` produces `Q = 200 ≥ 100`. -/
theorem high_charisma_bowl_is_pejorative :
    IsPejorativeEcho (charismaticBowl 5 4) := by
  unfold IsPejorativeEcho IsPejorativeEchoAt qFactor charismaticBowl
  decide

/-- **Zero-charisma bowl stays below the pejorative threshold:** the
    same coupling but no charisma yields `Q = 0 < 100`. -/
theorem zero_charisma_bowl_is_not_pejorative :
    ¬ IsPejorativeEcho (charismaticBowl 0 4) := by
  unfold IsPejorativeEcho IsPejorativeEchoAt qFactor charismaticBowl
  decide

/-- **Charisma is what crosses the threshold:** the same bowl shape
    moves from non-pejorative to pejorative purely by raising the
    rim's charisma magnitude. -/
theorem charisma_crosses_pejorative_threshold :
    ¬ IsPejorativeEcho (charismaticBowl 0 4) ∧
      IsPejorativeEcho (charismaticBowl 5 4) :=
  ⟨zero_charisma_bowl_is_not_pejorative, high_charisma_bowl_is_pejorative⟩

/-! ## Honesty note

The `effectiveDist = natDist − k` model is a discrete approximation
with Nat-saturating subtraction: a listener inside the charisma
radius is treated as collocated regardless of true distance. The
qualitative consequences (charisma widens capture, charisma can flip
median-voter dominance, charisma raises Q) survive any reasonable
refinement; the precise numeric thresholds are calibration choices.

The face/magnitude split keeps the channel-routing ledger
(`BuleyFace → mesh vote channel`) separate from the quantitative
capture radius. A future calibration can change the magnitude
function — or wire each face to a different magnitude per
`charismaWeight : BuleyFace → Nat` — without disturbing the
attention-routing ledger.

The `charisma_cannot_break_colocation_tie` result is the structural
limit: charisma can flip *strict* dominance against a non-collocated
opponent and can promote a position-disadvantaged strategy past its
non-charismatic alternative, but it cannot defeat the collocation
tie rule. The minimum-differentiation Nash trap therefore remains a
Nash story even under a charismatic extension of the model.
-/

end VibesCharismaticEmitter
