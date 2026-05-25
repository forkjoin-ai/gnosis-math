/-
  TritonSwerveGame.lean
  =====================

  One pure form, many games. The clinamen-swerve move, lifted from a BIT to a
  TRIT, turns out to be the shared skeleton of several "pure form" games — and
  the lift maps cause to effect.

  The trit (`TritonCanonical.Verdict = {decline, abstain, accept}`, sign
  `{−1, 0, +1}`) wears six masks, all sign-preserving and provably the same form:

      sign  clinamen     Verdict   Fork/Race/Fold   resonance (Basho)   interference
      −1    declinamen   decline   fold             silence             destructive
       0    clinamen     abstain   race             sting               (rest)
      +1    swerve       accept    fork             trill               constructive

  And on this one set live several games:

    * CHICKEN / the Chickie Run  (Part II) — binary Chicken is the COLLAPSED
      sub-game on the two definite verdicts {accept, decline}; the middle
      `abstain` is strictly new, gives a never-crashing brave move, and opens a
      new equilibrium. (Companion to `Gnosis/ChickieRunSwerveGame.lean`.)
    * ROCK-PAPER-SCISSORS  (Part III) — the SAME three moves under the cyclic
      structure `Z/3`. No dominant move, every move countered by exactly one:
      the perfect symmetry whose simplicity is the whole point.
    * CAUSE → EFFECT = the TRILL  (Part IV) — the swerve (the sting) resolves by
      interference: constructive → trill → survival (Jim); destructive → silence
      → the fall (Buzz's blocked swerve). The effect's sign IS the cause's sign;
      that sign-preserving bijection is what it means to have mapped cause to
      effect, and it is exactly Basho's trill-witnesses-sting. And the Buley bit
      paid (the swerve lift) is precisely the visibility purchased — in an
      asymmetric game, paying the bit buys the witness; a free move stays
      concealed. (Bridges `BashoClinamenTrillWitness`, `RebelHadACause`.)

  Init-only Rustic Church: no Mathlib, no `omega`, no `simp`/`decide` on
  open-variable goals; `decide` only on closed/finite statements.
-/
import Gnosis.TritonCanonical
import Gnosis.ChickieRunSwerveGame
import Gnosis.RebelHadACause
import Gnosis.BashoClinamenTrillWitness
import Gnosis.StepwiseAnalysisFramework
import Gnosis.CauseAndEffect

namespace GnosisMath
namespace TritonSwerveGame

open Gnosis.TritonCanonical (Verdict sign)
open GnosisMath.ChickieRunSwerveGame (Move myPayoff payoffT payoffR payoffS payoffP)
open StepwiseAnalysisFramework (FrfStep)

/-- The move is the canonical triton. `accept = +1 = swerve`, `abstain = 0 =
    the bare clinamen`, `decline = −1 = declinamen`. -/
abbrev Move3 := Verdict

-- ══════════════════════════════════════════════════════════
-- PART I.  ONE FORM, MANY NAMES  (sign-preserving readings)
-- ══════════════════════════════════════════════════════════

/-- Fork/Race/Fold reading: the swerve forks (branches a new possibility), the
    bare clinamen races (holds the line), the declinamen folds (collapses back).
    This is the triton plugged into the Fork/Race/Fold game. -/
def frfOf : Move3 → FrfStep
  | .accept  => .fork
  | .abstain => .race
  | .decline => .fold

theorem fork_is_the_swerve : frfOf .accept = FrfStep.fork := rfl
theorem race_is_the_clinamen : frfOf .abstain = FrfStep.race := rfl
theorem fold_is_the_declinamen : frfOf .decline = FrfStep.fold := rfl

/-- The Fork/Race/Fold reading is faithful: distinct moves give distinct steps. -/
theorem frfOf_injective (a b : Move3) (h : frfOf a = frfOf b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Resonance reading (Basho): silence / sting / trill on the `{−1, 0, +1}` axis.
    The sting is the bare clinamen; constructive interference amplifies it to the
    trill, destructive interference cancels it to silence. -/
inductive Resonance
  | silence   -- −1 : destructive interference, the fall, the cancelled wave
  | sting     --  0 : the bare clinamen, the moment-zero perturbation
  | trill     -- +1 : constructive interference, the witness, the survival
  deriving DecidableEq

def resonanceOf : Move3 → Resonance
  | .accept  => .trill
  | .abstain => .sting
  | .decline => .silence

def resonanceSign : Resonance → Int
  | .silence => -1
  | .sting   => 0
  | .trill   => 1

-- ══════════════════════════════════════════════════════════
-- PART II.  CHICKEN / THE CHICKIE RUN  (binary collapse + the new middle)
-- ══════════════════════════════════════════════════════════

/-- Aggression level: the swerve yields (0), the clinamen rides the brink (1),
    the declinamen drives straight (2). -/
def aggression : Move3 → Nat
  | .accept  => 0
  | .abstain => 1
  | .decline => 2

/-- The ternary Chicken payoff. The catastrophe is mutual maximal aggression
    (both drive straight = head-on). Otherwise out-braving the opponent wins,
    matching aggression draws, and yielding is the (surviving) chicken. -/
def tritonPayoff (me opp : Move3) : Nat :=
  if aggression me = 2 ∧ aggression opp = 2 then payoffP
  else if aggression opp < aggression me then payoffT
  else if aggression me = aggression opp then payoffR
  else payoffS

/-- Binary Chicken embeds: chicken `swerve ↦ accept`, chicken `stay ↦ decline`
    (drive straight). The two binary moves are the two DEFINITE verdicts. -/
def ofChicken : Move → Move3
  | .swerve => .accept
  | .stay   => .decline

/-- **Binary Chicken is the collapsed triton.** On the two definite verdicts the
    ternary payoff agrees exactly with `ChickieRunSwerveGame.myPayoff`. Classical
    Chicken is the trit with the middle decohered away — same shape as
    `TritonForkRaceFold.classical_is_collapsed_trit`. -/
theorem chicken_is_collapsed_triton (a b : Move) :
    tritonPayoff (ofChicken a) (ofChicken b) = myPayoff a b := by
  cases a <;> cases b <;> decide

/-- **The middle is strictly new.** `abstain` (the bare clinamen, the brink) has
    no binary preimage: it is the move classical Chicken cannot express. -/
theorem abstain_is_strictly_new : ¬ ∃ m : Move, ofChicken m = Verdict.abstain := by
  rintro ⟨m, hm⟩
  cases m <;> exact absurd hm (by decide)

/-- **The brink never crashes.** Riding the middle never triggers the
    catastrophe, whatever the opponent does — a brave move (it can still win)
    that cannot kill you. Only mutual maximal aggression crashes. -/
theorem brink_never_crashes (opp : Move3) : tritonPayoff .abstain opp ≠ payoffP := by
  cases opp <;> decide

/-- The catastrophe is reachable only through mutual declination (both drive
    straight). -/
theorem only_collision_crashes (a b : Move3) (h : tritonPayoff a b = payoffP) :
    a = Verdict.decline ∧ b = Verdict.decline := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-- The brink strictly out-pays driving straight against an opponent who drives
    straight: `S = 2 > 0 = P`. Against a maniac, ride the brink, don't collide. -/
theorem brink_beats_collision :
    tritonPayoff .abstain .decline > tritonPayoff .decline .decline := by decide

/-- A (pure) Nash equilibrium of the ternary game. -/
def isNash3 (m1 m2 : Move3) : Prop :=
  (∀ m, tritonPayoff m m2 ≤ tritonPayoff m1 m2) ∧
  (∀ m, tritonPayoff m m1 ≤ tritonPayoff m2 m1)

/-- The classical Chicken equilibrium survives the lift. -/
theorem nash_decline_accept : isNash3 .decline .accept := by
  refine ⟨?_, ?_⟩ <;> (intro m; cases m <;> decide)

/-- **A new equilibrium opens.** Against a driver who goes straight, riding the
    brink is a best response — so `(decline, abstain)` is a Nash equilibrium that
    binary Chicken could not express. -/
theorem nash_decline_abstain : isNash3 .decline .abstain := by
  refine ⟨?_, ?_⟩ <;> (intro m; cases m <;> decide)

-- ══════════════════════════════════════════════════════════
-- PART III.  ROCK-PAPER-SCISSORS  (the cyclic form; simplicity = symmetry)
-- ══════════════════════════════════════════════════════════

/-- The keystone cycle: the coupled swerve ↔ declinamen rotation through the
    middle. `decline → abstain → accept → decline`. This `Z/3` is the pure form
    of Rock-Paper-Scissors. -/
def cyclicSucc : Move3 → Move3
  | .decline => .abstain
  | .abstain => .accept
  | .accept  => .decline

/-- `a` beats `b` when `a` is `b`'s successor in the cycle. -/
def beats (a b : Move3) : Bool := decide (cyclicSucc b = a)

/-- **The cycle closes** — three rotations are the identity (`Z/3`). The minimal
    nontrivial symmetric game; its simplicity is exactly this closure. -/
theorem rps_cycle_closes (m : Move3) : cyclicSucc (cyclicSucc (cyclicSucc m)) = m := by
  cases m <;> rfl

/-- The three-cycle of dominance. -/
theorem rps_cycle :
    beats .accept .abstain ∧ beats .abstain .decline ∧ beats .decline .accept := by decide

/-- Nothing beats itself. -/
theorem rps_no_self_beat (a : Move3) : beats a a = false := by cases a <;> decide

/-- Dominance is antisymmetric: if `a` beats `b`, then `b` does not beat `a`. -/
theorem rps_antisymmetric (a b : Move3) (h : beats a b) : beats b a = false := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **No dominant move.** Every move is beaten by exactly one other — the perfect
    cyclic symmetry that makes Rock-Paper-Scissors fair and great. -/
theorem rps_every_move_has_a_counter (a : Move3) : ∃ b, beats b a := by
  cases a
  · exact ⟨.abstain, by decide⟩   -- decline is countered by abstain
  · exact ⟨.accept,  by decide⟩   -- abstain is countered by accept
  · exact ⟨.decline, by decide⟩   -- accept is countered by decline

/-- And every move beats exactly one other — total balance. -/
theorem rps_every_move_wins_once (a : Move3) : ∃ b, beats a b := by
  cases a
  · exact ⟨.accept,  by decide⟩   -- decline beats accept
  · exact ⟨.decline, by decide⟩   -- abstain beats decline
  · exact ⟨.abstain, by decide⟩   -- accept beats abstain

-- ══════════════════════════════════════════════════════════
-- PART IV.  CAUSE → EFFECT = THE TRILL  (interference + visibility)
-- ══════════════════════════════════════════════════════════

/-- The triton's cause↦effect mapping, as an instance of the extracted general
    `CausalLaw` from `Gnosis/CauseAndEffect.lean`: `resonanceOf` is a
    sign-preserving bijection from moves (causes) to resonances (effects). -/
def tritonCausalLaw : CauseAndEffect.CausalLaw Move3 Resonance where
  causeSign := sign
  effectSign := resonanceSign
  effectOf := resonanceOf
  preserves := fun c => by cases c <;> decide
  surjective := fun e => by
    cases e
    · exact ⟨.decline, rfl⟩
    · exact ⟨.abstain, rfl⟩
    · exact ⟨.accept, rfl⟩
  injective := fun a b h => by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **Cause maps to effect, sign for sign** (from the general law). -/
theorem cause_maps_to_effect (m : Move3) : resonanceSign (resonanceOf m) = sign m :=
  tritonCausalLaw.preserves m

/-- **We have mapped cause and effect.** `resonanceOf` is a sign-preserving
    bijection from moves (causes) to resonances (effects): faithful, onto, and
    injective — now sourced from the general `CausalLaw`. -/
theorem cause_and_effect_are_mapped :
    (∀ m, resonanceSign (resonanceOf m) = sign m) ∧
    (∀ e, ∃ m, resonanceOf m = e) ∧
    (∀ m1 m2, resonanceOf m1 = resonanceOf m2 → m1 = m2) :=
  ⟨tritonCausalLaw.preserves, tritonCausalLaw.surjective, tritonCausalLaw.injective⟩

/-- **The trill witnesses the swerve.** The trill effect occurs iff the move was
    the swerve — exactly Basho's `trill_witnesses_sting`. -/
theorem trill_witnesses_swerve (m : Move3) :
    resonanceOf m = Resonance.trill ↔ m = Verdict.accept := by
  cases m <;> decide

/-- **Constructive and destructive interference.** The free swerve is
    constructive (it amplifies to the trill, the witness, survival); the blocked
    swerve — the declinamen — is destructive (it cancels to silence, the fall).
    Buzz's caught sleeve is destructive interference. -/
theorem swerve_constructive_declinamen_destructive :
    resonanceOf .accept = Resonance.trill ∧
    resonanceOf .decline = Resonance.silence := by decide

/-- The Buley bit a move spends: the swerve lifts one bit, the others pay
    nothing. (Cf. `BuleyBiSidedBit.swerveLiftLifted`, the +1 lift.) -/
def bitPaid : Move3 → Nat
  | .accept  => 1
  | .abstain => 0
  | .decline => 0

/-- A move is visible when it produces the trill — the observable witness. -/
def isVisible (m : Move3) : Bool := decide (resonanceOf m = Resonance.trill)

/-- **The bit paid is the visibility bought.** In an asymmetric game, the only
    move that pays a Buley bit (the swerve) is exactly the move that becomes
    visible (produces the trill / witness). Paying buys the witness; a free move
    stays concealed — the signaling dual of "continuity conceals information". -/
theorem bit_paid_is_visibility (m : Move3) : 0 < bitPaid m ↔ isVisible m = true := by
  cases m <;> decide

/-- **Cause and effect is the trill.** Bundled across the three modules: the
    swerve's effect is the trill (this module); the same swerve causes Jim's
    survival (`RebelHadACause`); and no sting yields no trill (`Basho`). One
    difference-making witness, three masks. -/
theorem cause_effect_is_the_trill :
    resonanceOf .accept = Resonance.trill ∧
    GnosisMath.RebelHadACause.swerveCausesSurvival
      GnosisMath.ChickieRunSwerveGame.jimBailFrame
      GnosisMath.ChickieRunSwerveGame.cliffFrames ∧
    BashoClinamenTrillWitness.Trill 0 = 0 :=
  ⟨rfl, GnosisMath.RebelHadACause.james_dean_had_a_cause, by decide⟩

-- ══════════════════════════════════════════════════════════
-- MASTER: ONE PURE FORM
-- ══════════════════════════════════════════════════════════

/-- The whole synthesis: one trit, carrying Chicken (collapse + new middle),
    Rock-Paper-Scissors (the closed cycle), the Fork/Race/Fold reading, and the
    sign-preserving cause→effect/trill map with the bit-paid-is-visibility law. -/
theorem one_pure_form :
    -- Chicken is the collapsed sub-game; the middle is new
    (∀ a b : Move, tritonPayoff (ofChicken a) (ofChicken b) = myPayoff a b) ∧
    (¬ ∃ m : Move, ofChicken m = Verdict.abstain) ∧
    -- Rock-Paper-Scissors: the cycle closes, no dominant move
    (∀ m, cyclicSucc (cyclicSucc (cyclicSucc m)) = m) ∧
    (∀ a, ∃ b, beats b a) ∧
    -- Fork = the swerve
    (frfOf .accept = FrfStep.fork) ∧
    -- cause maps to effect, sign for sign
    (∀ m, resonanceSign (resonanceOf m) = sign m) ∧
    -- the bit paid is the visibility bought
    (∀ m, 0 < bitPaid m ↔ isVisible m = true) := by
  refine ⟨?_, abstain_is_strictly_new, rps_cycle_closes,
          rps_every_move_has_a_counter, rfl, ?_, ?_⟩
  · intro a b; exact chicken_is_collapsed_triton a b
  · intro m; exact cause_maps_to_effect m
  · intro m; exact bit_paid_is_visibility m

end TritonSwerveGame
end GnosisMath
