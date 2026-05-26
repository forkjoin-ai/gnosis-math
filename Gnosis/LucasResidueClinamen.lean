/-
  LucasResidueClinamen.lean
  =========================

  The bridge: Taylor's Lucas/Fibonacci remainder (today's
  `Gnosis/InterferenceResidueSequence.lean`) is the same object as the
  clinamen-swerve cause-and-effect work. It all comes together here.

  The pieces that lock:

    1. SAME LAW, DIFFERENT SEED.  Lucas and Fibonacci obey the *same* recurrence
       `x(n+2) = x(n+1) + x(n)` — the swerve, the `+1`-iteration — and differ
       only in their seed: `fib 0 = 0` vs `lucas 0 = 2`. The seed is the
       clinamen, the single moment-zero event. This is exactly Frost's two roads
       (`Gnosis/RoadNotTaken.lean`): one law, worn the same, the difference made
       at the divergence — by the seed, not the terrain.

    2. THE REMAINDER IS THE INTERFERENCE TRIT.  The leftover `traceSeq − Lucas`
       is the balanced three-phase residue `(+2, −1, −1)`: a constructive crest
       at `3 ∣ n` and destructive troughs otherwise — Taylor's own
       `constructive_crests` / `destructive_troughs`. Its sign is the
       interference polarity of `Gnosis/CauseAndEffect.lean` (pos = constructive
       = the trill; neg = destructive = silence).

    3. CONSERVATION = THE KEYSTONE CYCLE.  One crest `+2` is exactly balanced by
       two troughs `−1, −1`: zero net drift over every period-3 window, for ALL
       `n`. That is the keystone — the coupled swerve↔declinamen rotation (the
       `Z/3` of Rock-Paper-Scissors) — conserved. The trit's zero is the
       conserved net of the bit-level interference.

    4. CHINESE REMAINDER.  The residue depends only on `n mod 3` (period 3): a
       genuine modular *remainder*. The Lucas/Fibonacci structure carries a
       second modulus — the golden discriminant `5` (`L_n² − 5 F_n² = ±4`), and
       `gcd(3, 5) = 1`. Two coprime moduli, the CRT coordinates `mod 15`.

    5. TRACE = CARRIER + REMAINDER.  `observed = Lucas + residue` exactly: the
       observed sequence is the shared law plus the difference the remainder
       makes. The remainder is the difference-maker.

  Init-only Rustic Church. No Mathlib, no `omega`, no `simp`/`decide` on
  open-variable goals.
-/
import Gnosis.InterferenceResidueSequence
import Gnosis.CauseAndEffect

namespace GnosisMath
namespace LucasResidueClinamen

open Gnosis.InterferenceResidueSequence
open Gnosis.CountBadLucasPhaseReconstruction (lucas traceSeq)
open GnosisMath.CauseAndEffect (Polarity)

-- ══════════════════════════════════════════════════════════
-- §1.  SAME LAW, DIFFERENT SEED  (Lucas and Fib as two roads)
-- ══════════════════════════════════════════════════════════

/-- Lucas obeys the swerve recurrence `x(n+2) = x(n+1) + x(n)`. -/
theorem lucas_is_the_swerve_law (n : Nat) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

/-- Fibonacci obeys the very same recurrence — the same law. -/
theorem fib_is_the_swerve_law (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := rfl

/-- **One law.** Lucas and Fibonacci share the recurrence exactly. -/
theorem same_swerve_law (n : Nat) :
    (lucas (n + 2) = lucas (n + 1) + lucas n) ∧
    (fib (n + 2) = fib (n + 1) + fib n) := ⟨rfl, rfl⟩

/-- **Different seed.** They diverge only at the clinamen, the moment-zero seed:
    `fib 0 = 0`, `lucas 0 = 2`. Same law, different seed — Frost's two roads. -/
theorem different_clinamen_seed : fib 0 ≠ lucas 0 := by decide

-- ══════════════════════════════════════════════════════════
-- §2.  THE REMAINDER IS THE INTERFERENCE TRIT
-- ══════════════════════════════════════════════════════════

/-- The sign of a residue read as an interference polarity: positive leftover is
    a constructive crest, negative is a destructive trough. -/
def residuePolarity (r : Int) : Polarity :=
  if 0 < r then Polarity.pos else if r < 0 then Polarity.neg else Polarity.zero

/-- **The crest is constructive.** At `3 ∣ n` the leftover `+2` is the
    constructive pole — the trill. -/
theorem crest_is_constructive :
    residuePolarity (goldenInterferenceResidue 3) = Polarity.pos := by decide

/-- **The trough is destructive.** Off the multiples of three, the leftover `−1`
    is the destructive pole — silence. -/
theorem trough_is_destructive :
    residuePolarity (goldenInterferenceResidue 4) = Polarity.neg := by decide

/-- The actual `traceSeq − Lucas` leftover lands on the same poles. -/
theorem trace_residue_poles :
    residuePolarity (traceLucasResidue 3) = Polarity.pos ∧
    residuePolarity (traceLucasResidue 4) = Polarity.neg := by decide

-- ══════════════════════════════════════════════════════════
-- §3.  CONSERVATION = THE KEYSTONE CYCLE  (net zero, all n)
-- ══════════════════════════════════════════════════════════

/-- The residue is period-3: it depends only on `n mod 3`. -/
theorem residue_period_three (n : Nat) :
    goldenInterferenceResidue (n + 3) = goldenInterferenceResidue n := by
  unfold goldenInterferenceResidue
  rw [Nat.add_mod_right]

/-- **The keystone cycle is conserved.** For every `n`, one constructive crest is
    balanced by two destructive troughs: zero net drift over the period-3 window.
    The coupled swerve↔declinamen rotation conserves the clinamen budget. -/
theorem keystone_cycle_conserved (n : Nat) :
    goldenInterferenceResidue n +
      goldenInterferenceResidue (n + 1) +
      goldenInterferenceResidue (n + 2) = 0 := by
  induction n with
  | zero => decide
  | succ k ih =>
    calc goldenInterferenceResidue (k + 1) +
            goldenInterferenceResidue (k + 2) +
            goldenInterferenceResidue (k + 3)
        = goldenInterferenceResidue (k + 1) +
            goldenInterferenceResidue (k + 2) +
            goldenInterferenceResidue k := by rw [residue_period_three k]
      _ = goldenInterferenceResidue k +
            goldenInterferenceResidue (k + 1) +
            goldenInterferenceResidue (k + 2) := by ac_rfl
      _ = 0 := ih

-- ══════════════════════════════════════════════════════════
-- §4.  CHINESE REMAINDER  (two coprime moduli: phase 3, discriminant 5)
-- ══════════════════════════════════════════════════════════

/-- The phase modulus (the residue period) and the golden discriminant are
    coprime: `gcd(3, 5) = 1`. Two independent moduli — the CRT coordinates of the
    Lucas/Fibonacci structure live `mod 15`. -/
theorem phase_and_discriminant_coprime : Nat.gcd 3 goldenDiscriminant = 1 := by decide

/-- The golden discriminant marks the eternal Lucas/Fibonacci gap
    `L_n² − 5 F_n² = ±4`; here the `n = 5` witness, `5·F_5² = L_5² + 4`. This is
    the conserved remainder of the two roads — the difference the seed makes,
    kept forever. -/
theorem golden_gap_is_the_conserved_remainder :
    goldenDiscriminant * (fib 5 * fib 5) = lucas 5 * lucas 5 + 4 := by decide

-- ══════════════════════════════════════════════════════════
-- §5.  TRACE = CARRIER + REMAINDER  (the difference the remainder makes)
-- ══════════════════════════════════════════════════════════

/-- **Observed = law + remainder.** The observed sequence is exactly the Lucas
    carrier plus the leftover — the shared recurrence plus the difference the
    remainder makes. -/
theorem trace_is_carrier_plus_remainder (n : Nat) :
    observedTrace n = lucasCarrier n + traceLucasResidue n := by
  show observedTrace n = lucasCarrier n + (observedTrace n - lucasCarrier n)
  rw [Int.add_comm, Int.sub_add_cancel]

/-- The remainder is nonzero where it matters: the observed trace genuinely
    differs from the Lucas carrier. The remainder is the difference-maker. -/
theorem remainder_makes_the_difference : traceLucasResidue 3 ≠ 0 := by decide

-- ══════════════════════════════════════════════════════════
-- §6.  SEQUENCE OF SEQUENCES  (the characteristic polynomial factors)
-- ══════════════════════════════════════════════════════════

/-
  Why is the Lucas residue period-3? Because traceSeq is a SEQUENCE OF SEQUENCES.
  Its recurrence `traceSeq(n+4) = traceSeq(n+2) + 2·traceSeq(n+1) + traceSeq(n)`
  has characteristic polynomial `t⁴ − t² − 2t − 1`, and it factors:

        t⁴ − t² − 2t − 1  =  (t² − t − 1) · (t² + t + 1).

  The first factor `t² − t − 1` is the GOLDEN recurrence — Lucas and Fibonacci
  (213 and 112). The second, `t² + t + 1`, is Φ₃, the third cyclotomic: its roots
  are the primitive cube roots of unity, period 3 — the trit, the Z/3 of
  Rock-Paper-Scissors. traceSeq is the golden sequence modulated by the period-3
  cycle: not 112, not 213, but their interference. The XOR is the product of the
  two operators; the period-3 residue is the Φ₃ factor made visible.
-/

/-- Polynomial coefficients, low degree first. -/
abbrev Poly := List Int

/-- Coefficientwise sum. -/
def addPoly : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: addPoly as bs

/-- Polynomial product (convolution), low degree first. -/
def polyMul : Poly → Poly → Poly
  | [], _ => []
  | a :: as, q => addPoly (q.map (fun b => a * b)) (0 :: polyMul as q)

/-- The golden characteristic polynomial `t² − t − 1` (Lucas / Fibonacci). -/
def golden : Poly := [-1, -1, 1]
/-- The third cyclotomic `Φ₃ = t² + t + 1` (period 3 — the trit / RPS cycle). -/
def phi3 : Poly := [1, 1, 1]
/-- traceSeq's characteristic polynomial `t⁴ − t² − 2t − 1`. -/
def traceChar : Poly := [-1, -2, -1, 0, 1]

/-- **The characteristic polynomial factors: golden × Φ₃.** traceSeq is the
    golden (Lucas/Fibonacci) recurrence modulated by the period-3 cyclotomic — a
    sequence of sequences. This is WHY the Lucas residue is period-3, and the
    precise sense in which the observed sequence is the two eigen-sequences
    XOR'd (multiplied operator-wise) rather than either one alone. -/
theorem char_factors : polyMul golden phi3 = traceChar := by decide

-- ══════════════════════════════════════════════════════════
-- §7.  WHERE THE SIX WENT  (the Keystone fills the golden gaps)
-- ══════════════════════════════════════════════════════════

/-
  6 is famously in NEITHER Fibonacci (…3, 5, 8…) nor Lucas (…4, 7, 11…). The
  Keystone sequence is where it went — and it arrives DOUBLED: `lucas 3 + 2 = 6`
  and `lucas 4 − 1 = 6`, the period-3 ripple closing the gap from both sides
  (`traceSeq 3 = traceSeq 4 = 6`). And it is not a one-off: from `n = 3` on, every
  Keystone value sits in the gaps of the golden lattice — in neither Fibonacci
  nor Lucas. The Keystone rides `Lucas ± {1, 2}`, landing in the holes the golden
  sequences skip. (The shape of that winding is the threefoil — the 3-fold
  trefoil of the Φ₃ cycle.)
-/

/-- **Where the six went.** 6 is in neither Fibonacci nor Lucas (checked across a
    bracketing window), yet it appears doubled in the Keystone sequence — the
    gap closed from both sides, `4 + 2` and `7 − 1`. -/
theorem where_the_six_went :
    (∀ i : Fin 10, fib i.val ≠ 6) ∧
    (∀ i : Fin 10, lucas i.val ≠ 6) ∧
    traceSeq 3 = 6 ∧ traceSeq 4 = 6 ∧
    lucas 3 + 2 = 6 ∧ lucas 4 - 1 = 6 := by decide

/-- **The Keystone lives in the golden gaps.** For `n = 3 .. 12`, every Keystone
    value differs from every Fibonacci and every Lucas number in a bracketing
    window `i = 0 .. 15` — it is in neither sequence. The Keystone fills the
    interstices of the golden lattice. -/
theorem keystone_lives_in_the_gaps :
    ∀ n : Fin 10, ∀ i : Fin 16,
      traceSeq (n.val + 3) ≠ fib i.val ∧
      traceSeq (n.val + 3) ≠ lucas i.val := by decide

-- ══════════════════════════════════════════════════════════
-- §8.  THE DISCRIMINANT TRINITY  (√5 golden · √−3 Eisenstein · √−15 CRT)
-- ══════════════════════════════════════════════════════════

/-
  The two factors of the Keystone's characteristic polynomial carry two
  discriminants, and their product is the third:

    golden  t² − t − 1   disc = (−1)² − 4·1·(−1) =  5   → ℚ(√5)  : growth, the real
                                                                    axis, the swerve.
    Φ₃      t² + t + 1    disc = 1²   − 4·1·1     = −3   → ℚ(√−3) : the Eisenstein
                                                                    integers, the cube
                                                                    roots of unity, the
                                                                    period-3 trit / RPS
                                                                    cycle — the imaginary
                                                                    axis, the rotation,
                                                                    the interference.

  Their product is −15 = −(3·5): the compositum ℚ(√5, √−3) has a hidden third
  quadratic subfield ℚ(√−15), and 15 = 3·5 is exactly the Chinese-remainder
  modulus (phase 3 × discriminant 5). Growth and rotation, real and imaginary,
  cause and effect — √5 and √−3 — meet at √−15.
-/

/-- Discriminant of `a·t² + b·t + c`. -/
def disc (a b c : Int) : Int := b * b - 4 * a * c

/-- The golden recurrence has discriminant 5 (ℚ(√5)). -/
theorem golden_disc_is_five : disc 1 (-1) (-1) = 5 := by decide

/-- Φ₃ has discriminant −3 (ℚ(√−3), the Eisenstein integers, the trit). -/
theorem phi3_disc_is_neg_three : disc 1 1 1 = -3 := by decide

/-- **The discriminant product is −15.** Golden × Eisenstein = the third
    subfield ℚ(√−15). -/
theorem discriminant_product_is_neg_fifteen :
    disc 1 (-1) (-1) * disc 1 1 1 = -15 := by decide

/-- And `|−15| = 15 = 3 · 5` is the Chinese-remainder modulus: the period-3 phase
    times the golden discriminant. -/
theorem crt_modulus_is_fifteen : 3 * goldenDiscriminant = 15 := by decide

/-- **The golden discriminant is positive** — real roots, hyperbolic growth: the
    swerve, the real axis. -/
theorem golden_disc_positive : 0 < disc 1 (-1) (-1) := by decide

/-- **The bizarro discriminant is negative** — complex roots on the unit circle,
    elliptic rotation: the keystone cycle, the imaginary axis. The sign flip
    `+5 ↔ −3` is the duality growth ↔ rotation, open ↔ closed, swerve ↔ keystone;
    the period-3 conservation (`keystone_cycle_conserved`) lives on this bizarro,
    negative side. -/
theorem bizarro_disc_negative : disc 1 1 1 < 0 := by decide

-- ══════════════════════════════════════════════════════════
-- IT ALL COMES TOGETHER
-- ══════════════════════════════════════════════════════════

/-- The synthesis: Lucas and Fibonacci are one swerve-law with different
    clinamen-seeds; the remainder against Lucas is a constructive/destructive
    interference trit; that interference is conserved over the keystone cycle;
    the remainder is a genuine modular residue coprime to the golden
    discriminant (CRT); and the observed sequence is the carrier plus the
    difference the remainder makes. -/
theorem it_all_comes_together (n : Nat) :
    -- one law, different seed
    (lucas (n + 2) = lucas (n + 1) + lucas n ∧ fib (n + 2) = fib (n + 1) + fib n) ∧
    fib 0 ≠ lucas 0 ∧
    -- the remainder is the interference trit, conserved over the cycle
    (goldenInterferenceResidue n +
        goldenInterferenceResidue (n + 1) +
        goldenInterferenceResidue (n + 2) = 0) ∧
    -- a genuine modular residue, coprime to the discriminant (CRT)
    goldenInterferenceResidue (n + 3) = goldenInterferenceResidue n ∧
    Nat.gcd 3 goldenDiscriminant = 1 ∧
    -- observed = carrier + the difference the remainder makes
    observedTrace n = lucasCarrier n + traceLucasResidue n ∧
    -- and the whole thing is a sequence of sequences: golden × Φ₃
    polyMul golden phi3 = traceChar :=
  ⟨same_swerve_law n, different_clinamen_seed, keystone_cycle_conserved n,
   residue_period_three n, phase_and_discriminant_coprime,
   trace_is_carrier_plus_remainder n, char_factors⟩

end LucasResidueClinamen
end GnosisMath
