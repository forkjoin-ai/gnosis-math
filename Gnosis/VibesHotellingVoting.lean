/-
  VibesHotellingVoting.lean
  =========================

  Vibes as Hotelling positions on a 1-D affective line, attention voting
  (mesh-style), strict-dominance witnesses (positive + honest negative),
  and secondary interference effects.

  Layered ledger:

  * **Position** — `vibePosition : VibeValence → Nat` puts vibes on
    `{0, 2, 4} ⊆ [0..4]` (unhappy = 0, neutral = 2, happy = 4).
  * **Demand** — `leftDemand4` from `Gnosis.HotellingModel` gives each
    emitter's nearest-neighbor mass on the 5-point city.
  * **Attention vote** — each captured listener contributes a +1
    `clinamenLift` onto a chosen `BuleyFace`, lifted via
    `Gnosis.BuleyMeshAttentionBridge.castVote`.
  * **Strict dominance** — `AttentionDominates s s' y` =
    `Dominates (leftDemand4 s y) (leftDemand4 s' y)` — the
    Skyrms-rung `Dominates` predicate from
    `Gnosis.SkyrmsBuleyEquilibria`. Witnesses: neutral strictly
    dominates each extreme against the *opposite* extreme; honest
    negative result: no globally strictly-dominant position
    (collocation with an extreme opponent harvests the full city under
    the `≤`-tie rule, so minimum differentiation is a Nash story, not a
    strict-dominance story).
  * **Secondary interference** — the dominant aggregate re-radiates
    into the field; tied fields are a neutral fixed point, majority
    fields amplify under one round of re-radiation.

  Imports `Gnosis.HotellingModel`, `Gnosis.VibesAsWaveInference`,
  `Gnosis.SkyrmsBuleyEquilibria`,
  `Gnosis.Bridges.BuleyMeshAttentionBridge`. Zero `sorry`, zero new
  `axiom`.
-/

import Gnosis.HotellingModel
import Gnosis.VibesAsWaveInference
import Gnosis.SkyrmsBuleyEquilibria
import Gnosis.Bridges.BuleyMeshAttentionBridge

namespace VibesHotellingVoting

open Gnosis.HotellingModel (leftDemand4 InCity4 center_is_nash4)
open VibesAsWaveInference
  (VibeValence VibeWave happyWave unhappyWave quietWave inferBetween
   aggregateValence happyCount unhappyCount HappinessContagion DepressionContagion)

/-! ## Vibe positions on a 5-point affective line -/

/-- Coarse mood axis: unhappy at the left end, neutral at the median,
    happy at the right end. Other valences can be added later by
    widening the city beyond 5 points. -/
def vibePosition : VibeValence → Nat
  | .unhappy => 0
  | .neutral => 2
  | .happy => 4

theorem unhappy_at_zero : vibePosition .unhappy = 0 := rfl
theorem neutral_at_center : vibePosition .neutral = 2 := rfl
theorem happy_at_four : vibePosition .happy = 4 := rfl

theorem vibe_position_in_city (v : VibeValence) : InCity4 (vibePosition v) := by
  cases v <;> (unfold InCity4 vibePosition; decide)

/-! ## Mood emitter -/

/-- An emitter is a position on the mood axis paired with its carrier wave. -/
structure MoodEmitter where
  position : Nat
  carrier : VibeWave
  deriving Repr

/-- Canonical emitter for a vibe wave: place it at its valence's mood
    coordinate. -/
def emitterAt (v : VibeWave) : MoodEmitter where
  position := vibePosition v.valence
  carrier := v

theorem emitter_position_matches_valence (v : VibeWave) :
    (emitterAt v).position = vibePosition v.valence := rfl

/-- Listener mass captured by the left emitter — direct lift of
    `leftDemand4` from `Gnosis.HotellingModel`. -/
def emitterDemand (left right : MoodEmitter) : Nat :=
  leftDemand4 left.position right.position

theorem unhappy_emitter_against_happy_emitter :
    emitterDemand (emitterAt unhappyWave) (emitterAt happyWave) = 3 := by
  unfold emitterDemand emitterAt unhappyWave happyWave vibePosition
  native_decide

theorem neutral_emitter_against_happy_emitter :
    emitterDemand (emitterAt quietWave) (emitterAt happyWave) = 4 := by
  unfold emitterDemand emitterAt quietWave happyWave vibePosition
  native_decide

/-! ## Strict dominance via the Skyrms-rung `Dominates` predicate -/

open Gnosis.SkyrmsBuleyEquilibria (Dominates)

/-- A position `s` strictly dominates a comparison `s'` against a fixed
    opponent `y` exactly when `s` collects strictly more demand. We
    reuse the Nat-level `Dominates` from
    `Gnosis.SkyrmsBuleyEquilibria` so the dominance reading sits on the
    Skyrms rung of the Nash → Skyrms → Buley ladder. -/
def AttentionDominates (s s' y : Nat) : Prop :=
  Dominates (leftDemand4 s y) (leftDemand4 s' y)

/-- **Median-voter dominance:** with opponent at the *high* extreme,
    the neutral position captures strictly more demand than the unhappy
    extreme. -/
theorem neutral_strictly_dominates_unhappy_against_happy :
    AttentionDominates (vibePosition .neutral) (vibePosition .unhappy)
      (vibePosition .happy) := by
  unfold AttentionDominates Dominates vibePosition
  native_decide

/-- Symmetric flip: with opponent at the *low* extreme, neutral still
    strictly dominates the happy extreme. -/
theorem neutral_strictly_dominates_happy_against_unhappy :
    AttentionDominates (vibePosition .neutral) (vibePosition .happy)
      (vibePosition .unhappy) := by
  unfold AttentionDominates Dominates vibePosition
  native_decide

/-- **Honest Hotelling caveat (no globally dominant strategy):** when
    the opponent is at the unhappy extreme, the unhappy strategy
    *collocates* with the opponent and harvests the full 5-point city
    via the `≤`-tie rule, so neutral does **not** strictly dominate
    unhappy globally. Minimum differentiation is a Nash story (the
    `center_is_nash4` witness), not a strict-dominance story. -/
theorem neutral_does_not_strictly_dominate_unhappy_globally :
    ¬ AttentionDominates (vibePosition .neutral) (vibePosition .unhappy)
        (vibePosition .unhappy) := by
  unfold AttentionDominates Dominates vibePosition
  native_decide

/-- Symmetric negative result for the opposite extreme. -/
theorem neutral_does_not_strictly_dominate_happy_globally :
    ¬ AttentionDominates (vibePosition .neutral) (vibePosition .happy)
        (vibePosition .happy) := by
  unfold AttentionDominates Dominates vibePosition
  native_decide

/-- The center profile {2, 2} is a finite-city Hotelling Nash, lifted
    to the vibe layer: minimum differentiation as Skyrms convention. -/
theorem center_vibe_profile_is_nash :
    Gnosis.HotellingModel.IsNash4
      (vibePosition .neutral) (vibePosition .neutral) :=
  center_is_nash4

/-! ## Attention voting hookup (mesh ledger) -/

open Gnosis.SpectralNoiseEquilibrium (BuleyFace BuleyUnit buleyUnitScore)
open Gnosis.BuleyMeshAttentionBridge
  (MeshTally castVote emptyTally reachesQuorum
   vote_score_increment empty_tally_has_zero_score)

/-- One attention vote: a +1 clinamen lift on a chosen charisma face. -/
def attentionVote (face : BuleyFace) (tally : MeshTally) : MeshTally :=
  castVote tally face

theorem attention_vote_increments_score (face : BuleyFace) (tally : MeshTally) :
    buleyUnitScore (attentionVote face tally)
      = buleyUnitScore tally + 1 := by
  unfold attentionVote
  exact vote_score_increment tally face

/-- Replay `n` consecutive attention votes for the same charisma face. -/
def popularityVotes (face : BuleyFace) : Nat → MeshTally
  | 0 => emptyTally
  | n + 1 => attentionVote face (popularityVotes face n)

theorem popularity_score_eq_count (face : BuleyFace) (n : Nat) :
    buleyUnitScore (popularityVotes face n) = n := by
  induction n with
  | zero => exact empty_tally_has_zero_score
  | succ n ih =>
      show buleyUnitScore (attentionVote face (popularityVotes face n)) = n + 1
      rw [attention_vote_increments_score, ih]

theorem popularity_reaches_quorum
    (face : BuleyFace) (count threshold : Nat) (h : threshold ≤ count) :
    reachesQuorum (popularityVotes face count) threshold := by
  unfold reachesQuorum
  rw [popularity_score_eq_count]
  exact h

/-! ## Secondary interference: aggregate re-radiates into the field -/

/-- Pick the canonical carrier wave for the group's dominant valence.
    Tied / empty groups produce the neutral quiet wave. -/
def aggregateWave (waves : List VibeWave) : VibeWave :=
  match aggregateValence waves with
  | .happy => happyWave
  | .unhappy => unhappyWave
  | .neutral => quietWave

/-- Secondary field: each listener's wave is re-inferred against the
    aggregate carrier (constructive when valence matches, destructive
    when it opposes, transparent when the listener is neutral). -/
def secondaryField (waves : List VibeWave) : List VibeWave :=
  let agg := aggregateWave waves
  waves.map (fun v => inferBetween v agg)

theorem aggregate_wave_happy_when_majority_happy
    (waves : List VibeWave) (h : HappinessContagion waves) :
    aggregateWave waves = happyWave := by
  unfold aggregateWave
  rw [h.2]

theorem aggregate_wave_unhappy_when_majority_unhappy
    (waves : List VibeWave) (h : DepressionContagion waves) :
    aggregateWave waves = unhappyWave := by
  unfold aggregateWave
  rw [h.2]

/-- **Secondary amplification (happy):** a 2-happy field stays happy
    after the aggregate re-radiates back into it. -/
theorem happy_field_secondary_stays_happy :
    aggregateValence (secondaryField [happyWave, happyWave])
      = VibeValence.happy := by
  unfold secondaryField aggregateWave aggregateValence
    happyCount unhappyCount happyWave inferBetween
  decide

/-- **Secondary amplification (unhappy):** a 1-happy / 2-unhappy field
    stays unhappy under aggregate re-radiation. -/
theorem unhappy_majority_secondary_stays_unhappy :
    aggregateValence
        (secondaryField [happyWave, unhappyWave, unhappyWave])
      = VibeValence.unhappy := by
  unfold secondaryField aggregateWave aggregateValence
    happyCount unhappyCount happyWave unhappyWave inferBetween
  decide

/-- **Tied field is a neutral fixed point:** with the aggregate already
    neutral, secondary re-radiation does not flip the count. -/
theorem tied_field_secondary_no_flip :
    aggregateValence (secondaryField [happyWave, unhappyWave])
      = aggregateValence [happyWave, unhappyWave] := by
  unfold secondaryField aggregateWave aggregateValence
    happyCount unhappyCount happyWave unhappyWave inferBetween
  decide

/-! ## Iterated re-radiation (tertiary, …) -/

/-- Apply the aggregate-re-radiation step `n` times. -/
def iteratedField : Nat → List VibeWave → List VibeWave
  | 0, waves => waves
  | n + 1, waves => iteratedField n (secondaryField waves)

/-- A 2-happy field stays happy across two rounds of re-radiation. -/
theorem happy_field_stays_happy_two_rounds :
    aggregateValence (iteratedField 2 [happyWave, happyWave])
      = VibeValence.happy := by
  unfold iteratedField secondaryField aggregateWave aggregateValence
    happyCount unhappyCount happyWave inferBetween
  decide

/-! ## Skyrms-rung dominance bridge -/

/-- The strict-dominance chain `Buley > Skyrms > Nash` from
    `Gnosis.SkyrmsBuleyEquilibria` carries through to the vibe layer:
    Hotelling minimum differentiation is a Nash anchor (each emitter
    best-responds at the median), but the *convention* that an
    entire population coordinates on the median is a strictly higher
    Skyrms rung in the same `Dominates` ladder. -/
theorem skyrms_strictly_dominates_nash_for_vibes :
    Dominates Gnosis.NashSkyrmsBuleyKernelLadder.skyrmsLevel
      Gnosis.SkyrmsBuleyEquilibria.nashLevel :=
  Gnosis.SkyrmsBuleyEquilibria.skyrms_strictly_dominates_nash

end VibesHotellingVoting
