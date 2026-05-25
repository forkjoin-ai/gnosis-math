/-
  RebelHadACause.lean
  ===================

  "Rebel Without a Cause" — and yet James Dean's Jim Stark had one. We can
  prove it, and the proof turns on the double meaning of the word *cause*.

    cause (motive)    : a reason to act, a purpose, what a rebel is "without".
    cause (causation) : a difference-maker, the C in C ⟹ E.

  In the Chickie Run both senses collapse into a single object: the clinamen,
  the swerve (`Gnosis/ChickieRunSwerveGame.lean`). The swerve is Jim's reason to
  act — and it is also the strict *cause* of his survival, in the counterfactual,
  difference-making sense due to Lewis: C causes E when E holds with C present and
  fails with C removed. Jim's swerve is present and he lives; remove it (the
  obstruction, Buzz's caught sleeve) and the same driver dies. That is exactly
  what it means for the swerve to be the cause.

  This is the Lucretian point made literal. The clinamen is the *causa sui* — the
  uncaused declination that breaks the deterministic straight fall and lets a
  cause exist at all. To have a clinamen is to have a cause. The trajectory
  truly "without a cause" is the one with no swerve: the straight Lucretian fall,
  the cliff. So the title is ironic — the rebel who swerves is precisely the one
  WITH a cause, and the one without a cause is destroyed.

  Init-only Rustic Church. No Mathlib, no `omega`, no `simp`/`decide` on
  open-variable goals.
-/
import Gnosis.ChickieRunSwerveGame
import Gnosis.CauseAndEffect

namespace GnosisMath
namespace RebelHadACause

open GnosisMath.ChickieRunSwerveGame
open GnosisMath.CauseAndEffect (IsDifferenceMaker)

-- ══════════════════════════════════════════════════════════
-- COUNTERFACTUAL CAUSATION  (difference-making)
-- ══════════════════════════════════════════════════════════

/-- Whether the driver survives, as a function of whether the swerve is
    OBSTRUCTED. `obstructed = false` is the cause present (the clinamen is free);
    `obstructed = true` is the cause removed (the sleeve catches). -/
def survivesUnder (obstructed : Bool) (intended cliff : Nat) : Prop :=
  realizedJump obstructed intended cliff ≤ cliff

/-- The swerve causes survival: survival holds with the clinamen free and fails
    with it blocked. `IsDifferenceMaker` is the extracted, general counterfactual
    cause from `Gnosis/CauseAndEffect.lean` — this module is now an instance. -/
def swerveCausesSurvival (intended cliff : Nat) : Prop :=
  IsDifferenceMaker (fun obstructed => survivesUnder obstructed intended cliff)

/-- **The clinamen is a cause.** For any survivable intention, the swerve is a
    difference-maker: with it the driver lives, without it the driver dies. This
    is counterfactual causation, proved Init-only. -/
theorem clinamen_is_a_cause (intended cliff : Nat) (h : intended ≤ cliff) :
    swerveCausesSurvival intended cliff := by
  show survivesUnder false intended cliff ∧ ¬ survivesUnder true intended cliff
  refine ⟨h, ?_⟩
  intro hle
  exact Nat.lt_irrefl cliff (Nat.lt_of_lt_of_le (Nat.lt_succ_self cliff) hle)

-- ══════════════════════════════════════════════════════════
-- JAMES DEAN HAD A CAUSE
-- ══════════════════════════════════════════════════════════

/-- **James Dean had a cause.** Jim Stark's swerve, fired at the measured frame
    648 (well inside the edge at 744), is a genuine difference-maker: with it he
    survives, and had it been blocked he would have died. The rebel had — and
    exercised — a cause. -/
theorem james_dean_had_a_cause :
    swerveCausesSurvival jimBailFrame cliffFrames :=
  clinamen_is_a_cause jimBailFrame cliffFrames (by decide)

/-- The actual effect: Jim's cause produced its effect — he lived. -/
theorem james_dean_lived : survivesUnder false jimBailFrame cliffFrames := by
  show realizedJump false jimBailFrame cliffFrames ≤ cliffFrames
  show jimBailFrame ≤ cliffFrames
  decide

/-- The counterfactual: had Jim's swerve been obstructed, the same play kills
    him — which is exactly what makes the swerve the cause. -/
theorem without_the_swerve_he_dies : ¬ survivesUnder true jimBailFrame cliffFrames :=
  (james_dean_had_a_cause).2

-- ══════════════════════════════════════════════════════════
-- THE TITLE IS IRONIC: "WITHOUT A CAUSE" IS THE FALL
-- ══════════════════════════════════════════════════════════

/-- **Without a cause is the fall.** The trajectory with NO swerve — the blocked
    clinamen — does not survive, and follows the deterministic straight fall over
    the edge. To be without a cause is to be the determined one, the one who
    falls. (This is Buzz.) -/
theorem without_a_cause_is_the_fall (intended cliff : Nat) :
    ¬ survivesUnder true intended cliff ∧
    deterministicFall (realizedJump true intended cliff) cliff := by
  refine ⟨?_, ?_⟩
  · intro hle
    exact Nat.lt_irrefl cliff (Nat.lt_of_lt_of_le (Nat.lt_succ_self cliff) hle)
  · exact blocked_clinamen_is_fall intended cliff

/-- **The irony of the title.** The rebel (Jim) HAD a cause — his swerve is a
    genuine difference-maker — while the one truly "without a cause", the
    swerveless trajectory, is the deterministic fall. The cause is what saves;
    its absence is the cliff. -/
theorem rebel_without_a_cause_is_ironic :
    swerveCausesSurvival jimBailFrame cliffFrames ∧
    (∀ intended cliff : Nat, ¬ survivesUnder true intended cliff) := by
  refine ⟨james_dean_had_a_cause, ?_⟩
  intro intended cliff hle
  exact Nat.lt_irrefl cliff (Nat.lt_of_lt_of_le (Nat.lt_succ_self cliff) hle)

-- ══════════════════════════════════════════════════════════
-- "REBEL WITHOUT A CAUSE" = False
-- ══════════════════════════════════════════════════════════

/-- The proposition the title asserts: that the rebel had no cause — that his
    swerve made no difference. -/
def rebelWithoutACause : Prop := ¬ swerveCausesSurvival jimBailFrame cliffFrames

/-- The rebel did not lack a cause: the negation is refuted by the proof that he
    had one. -/
theorem not_rebel_without_a_cause : ¬ rebelWithoutACause :=
  fun h => h james_dean_had_a_cause

/-- **`"rebel without a cause" = False`.** The titular claim, taken as a
    proposition about Jim's swerve, is literally equal to `False`. lol. -/
theorem rebel_without_a_cause_is_false : rebelWithoutACause = False :=
  propext ⟨fun h => h james_dean_had_a_cause, False.elim⟩

end RebelHadACause
end GnosisMath
