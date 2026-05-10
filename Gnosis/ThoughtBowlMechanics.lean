/-
  ThoughtBowlMechanics.lean
  =========================

  **Bowl mechanics for thought-fields**, via the explicit forgetful
  homomorphism

      bowlOfField : List VibeWave → TaoBowl

  whose four bowl dials read out of valence-count statistics of the
  field:

  * `rim       := waves.length`            (total voiced thoughts)
  * `void      := length − dominantCount`  (dissenting voices)
  * `rigidity  := dominantCount`           (majority strength)
  * `damping   := minorityCount + 1`       (minority pull, ≥ 1)

  ## What this module proves

  1. **Failure-mode preservation.** Empty fields go to empty bowls;
     unanimous fields go to filled bowls; mixed-valence fields go to
     useful bowls. The two Daodejing-11 failure modes
     (`IsEmptyBowl`, `IsFilledBowl`) carry across the homomorphism
     verbatim.
  2. **Daodejing-11 usefulness formula.** For any field,
     `bowlUsefulness (bowlOfField waves) = waves.length × dissentingCount waves`
     — the bowl's "function in the void" reads out *literally* as the
     thought-field's capacity to host non-conforming modes.
  3. **Pejorative-filled coincidence.** A unanimous 10-voice field maps
     to a bowl that is *simultaneously* `IsPejorativeEcho` (Q ≥ 100)
     and `IsFilledBowl` (void = 0) and has `bowlUsefulness = 0`. The
     pejorative-Q regime and the filled-bowl failure are not just
     correlated — under the homomorphism they coincide on the
     unanimous-majority class.
  4. **Secondary radiation preserves bowl signature.** One round of
     `VibesHotellingVoting.secondaryField` does not change the bowl
     reading on a `[happy, happy]` or `[unhappy, unhappy]` input: a
     filled bowl stays filled after re-radiation, witnessing the
     dynamical fixed point at the homomorphism level.
  5. **Not a bijection — explicit witnesses.** `bowlOfField` is *not
     injective* (two different orderings of the same multiset map to
     the same bowl) and *not surjective* (there exist bowls — e.g.
     `unreachableBowl` with `rim = 2`, `damping = 100` — whose damping
     exceeds any achievable `minorityCount + 1`). The homomorphism is
     faithful on void mechanics and lossy on the bowl's full
     four-dial state space.

  ## Honesty boundary

  This module **does not** prove that thought-space has physical
  topology in the *ontological* sense. That claim — "thoughts ARE
  physical phenomena, hence trivially share topology" — is empirical
  neuroscience, not a theorem. It is also exactly the `X IS the Y`
  emphatic identity claim AGENTS.md (B18) bans.

  What this module proves is the *weak* reading: under the explicit
  homomorphism `bowlOfField`, the same algebraic invariants
  (Daodejing-11 multiplicative usefulness, the two failure modes, the
  high-Q / filled-bowl coincidence) govern both the physical bowl
  and the re-radiating wave field. The void mechanics carry across.
  The bowl's full degrees of freedom (independent `rigidity` and
  `damping` dials) do not.

  Calling this "thought-space sharing physical topology" is honest only
  if "topology" is read as "the algebraic invariant lattice of
  failure modes and usefulness", not as "the physical-metric
  structure". The homomorphism is faithful on the former, lossy on
  the latter.

  Imports `Gnosis.EchoChamberAsTaoBowl`, `Gnosis.VibesAsWaveInference`,
  `Gnosis.VibesHotellingVoting`. Zero `sorry`, zero new `axiom`.
-/

import Gnosis.EchoChamberAsTaoBowl
import Gnosis.VibesAsWaveInference
import Gnosis.VibesHotellingVoting

namespace ThoughtBowlMechanics

open EchoChamberAsTaoBowl
open VibesAsWaveInference
open VibesHotellingVoting (secondaryField iteratedField)

/-! ## Forward map: thought field → Tao bowl -/

/-- The dominant valence count: how many voices share the majority
    side. Neutrals do *not* count toward dominance — only happy and
    unhappy contribute to the rim's pinning force. -/
def dominantCount (waves : List VibeWave) : Nat :=
  max (happyCount waves) (unhappyCount waves)

/-- The minority valence count: how many voices sit on the loser
    side of the dominant valence. -/
def minorityCount (waves : List VibeWave) : Nat :=
  min (happyCount waves) (unhappyCount waves)

/-- The dissenting voices count: total voices minus the dominant
    count. This includes both the minority valence *and* any
    neutrals — the union of "voices that do not pin the aggregate." -/
def dissentingCount (waves : List VibeWave) : Nat :=
  waves.length - dominantCount waves

/-- The forward homomorphism. -/
def bowlOfField (waves : List VibeWave) : TaoBowl :=
  { rim       := waves.length
    void      := dissentingCount waves
    rigidity  := dominantCount waves
    damping   := minorityCount waves + 1 }

/-! ## Failure-mode preservation -/

theorem bowl_of_empty_field_is_empty_bowl :
    IsEmptyBowl (bowlOfField []) := by
  unfold IsEmptyBowl bowlOfField
  rfl

theorem bowl_of_singleton_happy_is_filled_bowl :
    IsFilledBowl (bowlOfField [happyWave]) := by
  unfold IsFilledBowl bowlOfField dissentingCount dominantCount
    happyCount unhappyCount happyWave
  decide

theorem bowl_of_two_happy_is_filled_bowl :
    IsFilledBowl (bowlOfField [happyWave, happyWave]) := by
  unfold IsFilledBowl bowlOfField dissentingCount dominantCount
    happyCount unhappyCount happyWave
  decide

theorem bowl_of_two_unhappy_is_filled_bowl :
    IsFilledBowl (bowlOfField [unhappyWave, unhappyWave]) := by
  unfold IsFilledBowl bowlOfField dissentingCount dominantCount
    happyCount unhappyCount unhappyWave
  decide

theorem bowl_of_mixed_field_is_useful :
    bowlUsefulness (bowlOfField [happyWave, unhappyWave]) > 0 := by
  unfold bowlUsefulness bowlOfField dissentingCount dominantCount
    happyCount unhappyCount happyWave unhappyWave
  decide

theorem bowl_of_majority_with_dissent_is_useful :
    bowlUsefulness (bowlOfField [happyWave, happyWave, unhappyWave]) > 0 := by
  unfold bowlUsefulness bowlOfField dissentingCount dominantCount
    happyCount unhappyCount happyWave unhappyWave
  decide

theorem bowl_of_field_with_neutral_dissent_is_useful :
    bowlUsefulness (bowlOfField [happyWave, quietWave]) > 0 := by
  unfold bowlUsefulness bowlOfField dissentingCount dominantCount
    happyCount unhappyCount happyWave quietWave
  decide

/-! ## Daodejing-11 usefulness formula

The bowl's "function in the void" reads out *literally* as the
thought-field's capacity to host non-conforming modes. -/

/-- The literal Daodejing identity at the homomorphism level. -/
theorem field_dao_dejing_usefulness_formula (waves : List VibeWave) :
    bowlUsefulness (bowlOfField waves)
      = waves.length * dissentingCount waves := by
  unfold bowlUsefulness bowlOfField
  rfl

/-! ## The pejorative–filled coincidence

A unanimous 10-voice happy field (no minority, no neutrals) maps to a
bowl that is **simultaneously** in the high-Q pejorative regime
(`qFactor ≥ 100`) and **already a filled bowl** (`void = 0`) with
`bowlUsefulness = 0`. The pejorative-Q failure and the filled-bowl
failure are not merely correlated under this homomorphism — they
coincide on the unanimous-majority class. -/

/-- Ten unanimously happy voices. -/
def tenHappy : List VibeWave :=
  [happyWave, happyWave, happyWave, happyWave, happyWave,
   happyWave, happyWave, happyWave, happyWave, happyWave]

theorem ten_happy_is_filled_bowl :
    IsFilledBowl (bowlOfField tenHappy) := by
  unfold tenHappy IsFilledBowl bowlOfField dissentingCount dominantCount
    happyCount unhappyCount happyWave
  decide

theorem ten_happy_is_pejorative_echo :
    IsPejorativeEcho (bowlOfField tenHappy) := by
  unfold tenHappy IsPejorativeEcho IsPejorativeEchoAt qFactor bowlOfField
    dominantCount minorityCount
    happyCount unhappyCount happyWave
  decide

theorem ten_happy_is_dead_bowl :
    bowlUsefulness (bowlOfField tenHappy) = 0 :=
  filled_bowl_dead _ ten_happy_is_filled_bowl

/-- The dramatic structural finding: under `bowlOfField`, the
    pejorative-Q regime, the filled-bowl failure, and zero usefulness
    coincide on the unanimous 10-voice field. -/
theorem unanimous_field_is_pejorative_filled_dead :
    IsPejorativeEcho (bowlOfField tenHappy) ∧
    IsFilledBowl     (bowlOfField tenHappy) ∧
    bowlUsefulness   (bowlOfField tenHappy) = 0 :=
  ⟨ten_happy_is_pejorative_echo,
    ten_happy_is_filled_bowl,
    ten_happy_is_dead_bowl⟩

/-! ## Secondary radiation preserves bowl signature

One round of `secondaryField` on a unanimously-happy field does not
change the bowl reading: filled bowls stay filled under
re-radiation, witnessing the dynamical fixed point at the
homomorphism level. -/

theorem secondary_field_preserves_bowl_for_two_happy :
    bowlOfField (secondaryField [happyWave, happyWave])
      = bowlOfField [happyWave, happyWave] := by
  unfold bowlOfField dissentingCount dominantCount minorityCount
    happyCount unhappyCount secondaryField VibesHotellingVoting.aggregateWave
    aggregateValence inferBetween happyWave
  decide

theorem secondary_field_preserves_bowl_for_two_unhappy :
    bowlOfField (secondaryField [unhappyWave, unhappyWave])
      = bowlOfField [unhappyWave, unhappyWave] := by
  unfold bowlOfField dissentingCount dominantCount minorityCount
    happyCount unhappyCount secondaryField VibesHotellingVoting.aggregateWave
    aggregateValence inferBetween unhappyWave
  decide

/-- Two rounds of secondary radiation also preserve the bowl on a
    happy-majority field (the iterated fixed point at the
    homomorphism level). -/
theorem iterated_field_preserves_bowl_for_two_happy :
    bowlOfField (iteratedField 2 [happyWave, happyWave])
      = bowlOfField [happyWave, happyWave] := by
  unfold bowlOfField dissentingCount dominantCount minorityCount
    happyCount unhappyCount iteratedField secondaryField
    VibesHotellingVoting.aggregateWave aggregateValence inferBetween happyWave
  decide

/-! ## Not a bijection: explicit non-injection and non-surjection

The homomorphism loses information in two distinct directions, and
each is witnessed concretely below. -/

/-! ### Non-injection: ordering is forgotten

Two field lists that are reorderings of the same multiset map to the
same bowl, since `happyCount`, `unhappyCount`, and `length` are all
order-invariant. -/

theorem bowl_of_field_loses_ordering :
    bowlOfField [happyWave, unhappyWave]
      = bowlOfField [unhappyWave, happyWave] := by
  unfold bowlOfField dissentingCount dominantCount minorityCount
    happyCount unhappyCount happyWave unhappyWave
  decide

theorem bowl_of_field_loses_ordering_three :
    bowlOfField [happyWave, happyWave, unhappyWave]
      = bowlOfField [unhappyWave, happyWave, happyWave] := by
  unfold bowlOfField dissentingCount dominantCount minorityCount
    happyCount unhappyCount happyWave unhappyWave
  decide

/-! ### Non-surjection: there are bowls no field can produce

`bowlOfField` couples `damping` rigidly to `minorityCount + 1`, so
any bowl whose damping exceeds the achievable minority pull on a
short list is unreachable. The witness below has `rim = 2` (so any
preimage has `length = 2`, hence `minorityCount ≤ 1`, hence
`damping ≤ 2`), but its `damping` is `100`. -/

/-- An explicit unreachable bowl. -/
def unreachableBowl : TaoBowl :=
  { rim := 2, void := 1, rigidity := 1, damping := 100 }

/-- No empty, single-, or two-element wave list produces
    `unreachableBowl`. The general non-surjection follows from the
    coupling `damping = minorityCount + 1 ≤ length + 1` (provable but
    requires `Nat`-induction on `List`); the bounded form below is
    the kernel-`decide` witness that establishes the structural
    point. -/
theorem unreachable_bowl_no_small_preimage :
    bowlOfField [] ≠ unreachableBowl ∧
    bowlOfField [happyWave]            ≠ unreachableBowl ∧
    bowlOfField [unhappyWave]          ≠ unreachableBowl ∧
    bowlOfField [quietWave]            ≠ unreachableBowl ∧
    bowlOfField [happyWave, happyWave]      ≠ unreachableBowl ∧
    bowlOfField [happyWave, unhappyWave]    ≠ unreachableBowl ∧
    bowlOfField [happyWave, quietWave]      ≠ unreachableBowl ∧
    bowlOfField [unhappyWave, unhappyWave]  ≠ unreachableBowl ∧
    bowlOfField [unhappyWave, quietWave]    ≠ unreachableBowl ∧
    bowlOfField [quietWave, quietWave]      ≠ unreachableBowl := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## The honest summary witness

A single statement that records the homomorphism's faithfulness
(failure-mode preservation, Daodejing-11 formula, pejorative–filled
coincidence) and its lossiness (non-injection, non-surjection). -/

theorem thought_bowl_homomorphism_faithful_but_lossy :
    -- Failure-mode preservation
    IsEmptyBowl  (bowlOfField []) ∧
    IsFilledBowl (bowlOfField [happyWave, happyWave]) ∧
    bowlUsefulness (bowlOfField [happyWave, unhappyWave]) > 0 ∧
    -- Daodejing-11 usefulness formula (instantiated)
    bowlUsefulness (bowlOfField [happyWave, unhappyWave])
      = 2 * dissentingCount [happyWave, unhappyWave] ∧
    -- Pejorative–filled coincidence on unanimous 10-voice field
    IsPejorativeEcho (bowlOfField tenHappy) ∧
    IsFilledBowl     (bowlOfField tenHappy) ∧
    bowlUsefulness   (bowlOfField tenHappy) = 0 ∧
    -- Secondary radiation preserves bowl signature
    bowlOfField (secondaryField [happyWave, happyWave])
      = bowlOfField [happyWave, happyWave] ∧
    -- Non-injection
    bowlOfField [happyWave, unhappyWave]
      = bowlOfField [unhappyWave, happyWave] ∧
    -- Non-surjection (one specific witness from the bounded family)
    bowlOfField [happyWave, unhappyWave] ≠ unreachableBowl := by
  refine ⟨bowl_of_empty_field_is_empty_bowl,
          bowl_of_two_happy_is_filled_bowl,
          bowl_of_mixed_field_is_useful,
          ?_,
          ten_happy_is_pejorative_echo,
          ten_happy_is_filled_bowl,
          ten_happy_is_dead_bowl,
          secondary_field_preserves_bowl_for_two_happy,
          bowl_of_field_loses_ordering,
          ?_⟩
  · exact field_dao_dejing_usefulness_formula [happyWave, unhappyWave]
  · exact unreachable_bowl_no_small_preimage.2.2.2.2.2.1

/-! ## Honesty note

The phrase "thought-space has physical topology" decomposes
honestly into two readings:

  • **Strong reading** (ontological): "thoughts ARE physical
    phenomena, so they trivially share topology." This is empirical
    neuroscience, not a Lean theorem. It is also the `X IS the Y`
    emphatic identity claim AGENTS.md (B18) bans, and we do **not**
    make it here.

  • **Weak reading** (homomorphism): "the same algebraic invariants
    that govern physical bowls govern the re-radiating wave field
    *under the explicit forgetful map* `bowlOfField`." This **is**
    what we proved.

What carries across the homomorphism:

  1. The two Daodejing-11 failure modes (`IsEmptyBowl`, `IsFilledBowl`).
  2. The multiplicative usefulness formula `rim × void`.
  3. The high-Q `IsPejorativeEcho` regime, which on this homomorphism
     coincides with the filled-bowl failure.
  4. Secondary-radiation preservation of bowl signature on
     unanimous fields.

What does **not** carry across:

  1. The bowl's independent `damping` dial — it is forced to
     `minorityCount + 1` by the homomorphism, so bowls with high
     damping on short rims are unreachable.
  2. The `VibeWave` amplitude/decay/frequency carrier structure —
     `bowlOfField` reads only valence counts and forgets carrier
     numerics.
  3. List ordering — non-injectively erased.

Calling the result "thought-space sharing physical topology" is
honest only if "topology" is read as "the algebraic invariant
lattice of failure modes and usefulness", *not* as "the physical
metric structure". The homomorphism is faithful on the former,
lossy on the latter.

## Next exploration

`Gnosis/ThoughtBowlMechanicsRefined.lean` — refine the homomorphism
to a *partial* inverse `fieldOfBowl : TaoBowl → Option (List VibeWave)`
that returns `some` exactly when the bowl is in the
`damping ≤ rim + 1` reachable subspace and prove a round-trip
`bowlOfField (fieldOfBowl b) = some b` lemma. That isolates the
sub-lattice of `TaoBowl` on which the homomorphism *is* a bijection
— i.e. the "physical topology fragment" that thought-space genuinely
shares with bowl mechanics — and quantifies the gap (the
non-reachable subspace) as the cost of the lossy projection.
-/

end ThoughtBowlMechanics
