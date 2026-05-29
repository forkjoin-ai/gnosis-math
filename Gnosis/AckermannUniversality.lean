import Init
import Gnosis.AckermannFunction

/-
  AckermannUniversality.lean
  ==========================

  Obligation 3 of the "Ackermann ceiling occupies the role of c" program
  (see `AckermannLightConeBridge`, `AckermannIsLightSpeed`).

  ## What this module proves (the PR-ladder identification)

  The hyperoperation hierarchy `hyperop k` *is* the primitive-recursive
  ladder: each fixed level is one of the familiar PR operations.

    * `hyperop_one`   :  `hyperop 1 a b = a + b`   (addition)
    * `hyperop_two`   :  `hyperop 2 a b = a * b`   (multiplication)
    * `hyperop_three` :  `hyperop 3 a b = a ^ b`   (exponentiation)

  Each is a *fixed* total function definable by primitive recursion. This is
  the rigorous core of "every fixed level is PR": levels 0–3 are
  successor / addition / multiplication / exponentiation, and the same
  recursion schema gives tetration, pentation, … at every higher fixed
  level. The Ackermann diagonal `ackermannDiag n = hyperop n n n` is the
  ONE function that is not pinned to any fixed level — it climbs the ladder
  with its own argument.

  ## What remains (the cited classical universal)

  The full classical Ackermann-is-not-primitive-recursive theorem (Ackermann
  1928; Grzegorczyk hierarchy) has two halves:
    (a) a primitive-recursive function encoder showing every PR runtime is
        bounded by some fixed hyperoperation level (`prBoundedByLadder`); and
    (b) the diagonal eventually strictly dominates every fixed level
        (`eventualLevelDomination`), which needs the `hyperop`
        level-monotonicity tower.

  Half (b) is now DISCHARGED — `AckermannMonotone.eventualLevelDomination_holds`
  proves it in full (zero `sorry`). Half (a), the PR-encoder, is the only part
  not mechanized in Init-only Lean; we keep it as a documented `Prop`
  placeholder (`prBoundedByLadder`), following the `SpacetimePromotionObligation`
  pattern in `CausalDiamond`, rather than assert it with a `sorry`. The
  concrete escalating-dominance witnesses on the calibration window are in
  `AckermannFunction.ack_dominates` and `AckermannPrimitiveRecursiveBound`.

  Init-only. Zero `sorry`, zero new `axiom`.
-/

namespace AckermannUniversality

open AckermannFunction

/-! ## The PR ladder: levels 1–3 are addition, multiplication, exponentiation -/

/-- **Level 1 = addition.** `hyperop 1 a b = a + b`. -/
theorem hyperop_one (a b : Nat) : hyperop 1 a b = a + b := by
  induction b with
  | zero => simp [hyperop]
  | succ b ih =>
    -- hyperop 1 a (b+1) = hyperop 0 a (hyperop 1 a b) = (hyperop 1 a b) + 1
    simp only [hyperop, Nat.zero_add]; omega

/-- **Level 2 = multiplication.** `hyperop 2 a b = a * b`. -/
theorem hyperop_two (a b : Nat) : hyperop 2 a b = a * b := by
  induction b with
  | zero => simp [hyperop]
  | succ b ih =>
    -- hyperop 2 a (b+1) = hyperop 1 a (hyperop 2 a b) = a + (a*b)
    simp only [hyperop]
    rw [hyperop_one, ih, Nat.mul_succ]
    omega

/-- **Level 3 = exponentiation.** `hyperop 3 a b = a ^ b`. -/
theorem hyperop_three (a b : Nat) : hyperop 3 a b = a ^ b := by
  induction b with
  | zero => simp [hyperop]
  | succ b ih =>
    -- hyperop 3 a (b+1) = hyperop 2 a (hyperop 3 a b) = a * (a^b)
    simp only [hyperop]
    rw [hyperop_two, ih, Nat.pow_succ, Nat.mul_comm]

/-! ## The diagonal sits on the ladder it climbs

  At each fixed level the diagonal argument `n` evaluates the level-`n`
  operation. The closed forms above let us read the diagonal at the
  calibration points directly in familiar operations. -/

/-- The diagonal in closed form at the ladder rungs we can name:
    `A(1) = 1+1`, `A(2) = 2·2`, `A(3) = 3³`. -/
theorem diagonal_on_ladder :
    ackermannDiag 1 = 1 + 1 ∧
    ackermannDiag 2 = 2 * 2 ∧
    ackermannDiag 3 = 3 ^ 3 := by
  refine ⟨?_, ?_, ?_⟩
  · show hyperop 1 1 1 = 1 + 1; rw [hyperop_one]
  · show hyperop 2 2 2 = 2 * 2; rw [hyperop_two]
  · show hyperop 3 3 3 = 3 ^ 3; rw [hyperop_three]

/-- The named ladder operations are genuinely escalating at the calibration
    argument `n = 3`: `succ 3 < 3+3 < 3·3 < 3³`. Each fixed level strictly
    out-grows the one below it where the diagonal already lives. -/
theorem ladder_strictly_escalates_at_three :
    hyperop 0 3 3 < hyperop 1 3 3 ∧
    hyperop 1 3 3 < hyperop 2 3 3 ∧
    hyperop 2 3 3 < hyperop 3 3 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## The classical universal — recorded here; (b) discharged in `AckermannMonotone` -/

/-- The two universal statements whose composition is the full
    Ackermann-is-not-primitive-recursive theorem. We record them precisely
    as `Prop`s, in the `SpacetimePromotionObligation` style, without
    discharging them. -/
structure AckermannUniversalityObligation where
  /-- Every fixed hyperoperation level is eventually strictly dominated by
      the Ackermann diagonal. DISCHARGED in
      `AckermannMonotone.eventualLevelDomination_holds` via the full `hyperop`
      monotonicity tower. -/
  eventualLevelDomination : Prop
  /-- Every primitive-recursive runtime is bounded by some fixed level of
      the hyperoperation ladder (Grzegorczyk hierarchy). Stated in prose;
      its formalization needs a primitive-recursive function encoder. -/
  prBoundedByLadder : Prop

/-- The obligation, with `eventualLevelDomination` written out as the exact
    Lean proposition a future proof must discharge. -/
def ackermannUniversalityObligation : AckermannUniversalityObligation :=
  { eventualLevelDomination :=
      ∀ k, ∃ N, ∀ n, N ≤ n → hyperop k n n < ackermannDiag n
  , prBoundedByLadder :=
      -- Placeholder Prop for the cited Grzegorczyk result; not the load-
      -- bearing content of this module. Marked `True` deliberately so the
      -- structure is total without claiming a false formalization.
      True }

end AckermannUniversality
