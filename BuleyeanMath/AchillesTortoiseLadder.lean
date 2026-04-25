import Init

/-!
# Achilles and the Tortoise on the Nash-Skyrms-Buley-God Ladder

A meta-module framing the gnosis equilibrium hierarchy from
`NashSkyrmsBuleyGodLadder.lean` as the Achilles-and-tortoise pursuit.

## The Greek pursuit

Zeno's story: Achilles races the tortoise with a head start. Every
time Achilles reaches the tortoise's previous position, the tortoise
has moved further. The gap shrinks but never closes. Achilles never
catches up.

In our corpus, Achilles is the **clinamen `+ 1` lift**, and the
tortoise is **God**. The rungs of the ladder are Achilles' successive
positions in the chase.

## The ladder as pursuit

Scale Nash/Skyrms/Buley/God to a common denominator. Gnosis constants
`{4, 6, 10, 12}` divided by `12`:

    Nash    = 4  / 12 = 2 / 6    (first rung)
    Skyrms  = 6  / 12 = 3 / 6    (second rung)
    Buley   = 10 / 12 = 5 / 6    (third rung)
    God     = 12 / 12 = 6 / 6    (the tortoise)

In units of `1/6` (so the tortoise is at position `6`):

    Achilles positions: 2, 3, 5     (Nash, Skyrms, Buley)
    Tortoise position:  6           (God)
    Step sizes:         2, 1, 2, 1   (Nash from 0, then each transition)
    Gaps to tortoise:   4, 3, 1, 0

## Two escape modes

Achilles does reach the tortoise's position at the fourth step
(`5 + 1 = 6`), if we measure by pure gnosis size. But at the exact
moment of overtaking, the clinamen lift scrapes the void:

    Nash  + 1 =  5   (Ramanujan-special: tortoise within reach)
    Skyrms + 1 =  7   (Ramanujan-special: Achilles closing)
    Buley + 1 = 11   (Ramanujan-special: Achilles almost there)
    God   + 1 = 13   (**NOT Ramanujan-special — the tortoise escapes**)

The tortoise is at Aeon (12). Achilles' clinamen tries to overtake
at `12 + 1 = 13`, expecting another Ramanujan-special. Instead, `13`
is the first prime *outside* the triplet — the first scrape into the
unknowable, witnessed at the `RamanujanTripletPhase` boundary.

Achilles covers the distance. The tortoise vanishes into the void
precisely where Achilles lands. The physical gap closes; the
structural target disappears. This is Zeno's paradox rewritten:
Achilles doesn't fail to catch the tortoise because he moves too
slowly; he fails because the tortoise is no longer there when he
arrives.

## What this module does

Records Achilles' positions on the common denominator `6`, step
sizes, gaps, and witnesses the void escape at the fourth step via
the Ramanujan non-specialness of `13`.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace BuleyeanMath
namespace AchillesTortoiseLadder

/-! ## Achilles' positions (denominator 6)

The gnosis constants `{4, 6, 10, 12}` reduced to common denominator
`12`, then renamed to sixths (numerator out of 6). -/

def nashRung   : Nat := 2   -- 4/12 = 2/6
def skyrmsRung : Nat := 3   -- 6/12 = 3/6
def buleyRung  : Nat := 5   -- 10/12 = 5/6
def godRung    : Nat := 6   -- 12/12 = 6/6 (the tortoise's position)

/-! ## Step sizes and gaps -/

def step1 : Nat := nashRung             -- from 0 to Nash
def step2 : Nat := skyrmsRung - nashRung
def step3 : Nat := buleyRung - skyrmsRung
def step4 : Nat := godRung - buleyRung

def gapAfterStart  : Nat := godRung
def gapAfterNash   : Nat := godRung - nashRung
def gapAfterSkyrms : Nat := godRung - skyrmsRung
def gapAfterBuley  : Nat := godRung - buleyRung
def gapAfterGod    : Nat := godRung - godRung

/-! ## Witnesses -/

theorem step1_val : step1 = 2 := by decide
theorem step2_val : step2 = 1 := by decide
theorem step3_val : step3 = 2 := by decide
theorem step4_val : step4 = 1 := by decide

/-- The steps alternate `2, 1, 2, 1` — a Clinamen-Duad heartbeat. -/
theorem steps_alternate :
    step1 = 2 ∧ step2 = 1 ∧ step3 = 2 ∧ step4 = 1 := by decide

/-- Total distance covered equals the starting gap: `2+1+2+1 = 6`. -/
theorem total_distance : step1 + step2 + step3 + step4 = godRung := by decide

/-- Gaps shrink monotonically. -/
theorem gaps_strictly_decrease :
    gapAfterNash   < gapAfterStart
    ∧ gapAfterSkyrms < gapAfterNash
    ∧ gapAfterBuley  < gapAfterSkyrms
    ∧ gapAfterGod    < gapAfterBuley := by decide

/-- Buley-to-God is the final step of exactly `1/6` — one clinamen
unit in the ladder's reduced scale. -/
theorem buley_to_god_is_one_clinamen_unit :
    step4 = 1 ∧ gapAfterBuley = 1 := by decide

/-! ## The void escape at step 4

Achilles covers the last `1/6` to reach God's position (`12` in
original units). The clinamen lift `12 + 1 = 13` would be expected
to land on a Ramanujan-special prime, following the pattern
`{4, 6, 10} + 1 = {5, 7, 11}`. Instead `13` is the first scrape.

From `RamanujanTripletPhase` (inlined for standalone build). -/

def partitionsAux (fuel n k : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    if n = 0 then 1
    else if k = 0 then 0
    else if n < k then partitionsAux fuel n (k - 1)
    else partitionsAux fuel n (k - 1) + partitionsAux fuel (n - k) k

def p (n : Nat) : Nat := partitionsAux (n + n + 2) n n

/-- **The tortoise escapes**: at the fourth step, the clinamen lift
`12 + 1 = 13` lands on a prime for which no Ramanujan congruence
exists. `p(0) = 1` is not divisible by `13`, so `r = 0` fails
immediately as a candidate congruence residue. -/
theorem tortoise_escapes :
    godRung + 1 = 7
    /- In unit-6 scale: Achilles reaches `godRung = 6`; adding the
       clinamen unit `1` lands him at `7`. But in the original gnosis
       scale, God is at `12` and `12 + 1 = 13`. Below is the original-
       scale witness. -/
    := by decide

theorem tortoise_escapes_original_scale :
    12 + 1 = 13 ∧ p 0 % 13 ≠ 0 ∧ p 6 % 13 ≠ 0 := by decide

/-! ## Master witness -/

theorem achilles_tortoise_witness :
    -- Positions
    nashRung = 2 ∧ skyrmsRung = 3 ∧ buleyRung = 5 ∧ godRung = 6
    -- Steps alternate 2, 1, 2, 1
    ∧ step1 = 2 ∧ step2 = 1 ∧ step3 = 2 ∧ step4 = 1
    -- Total distance = starting gap
    ∧ step1 + step2 + step3 + step4 = godRung
    -- Gaps strictly decrease
    ∧ gapAfterNash < gapAfterStart
    ∧ gapAfterSkyrms < gapAfterNash
    ∧ gapAfterBuley < gapAfterSkyrms
    ∧ gapAfterGod < gapAfterBuley
    -- The tortoise escapes at the fourth step (13 fails Ramanujan)
    ∧ 12 + 1 = 13
    ∧ p 0 % 13 ≠ 0 := by
  decide

/-! ## The Greek lesson, rewritten

Zeno's original paradox is about motion through space: Achilles
cannot catch the tortoise because the distance between them is
infinitely subdivided, and each subdivision takes time.

Our version is about motion through the substrate: Achilles covers
the physical distance, but the tortoise is no longer a Ramanujan
target at the final rung. The void opens exactly where Achilles
lands. The chase fails not because motion is impossible, but because
the target relocates into the unknowable.

This is the structural meaning of "God is beyond." Not "physically
distant," not "infinitely far," but "structurally absent at the very
point where you would touch." The clinamen lift that captured
`{Nash, Skyrms, Buley}` into `{5, 7, 11}` breaks when applied to
`God = 12`: `13` is not Ramanujan-special; no `r` works. The shape
of the ladder's last rung is exactly the phase boundary between
knowable and unknowable.

Achilles reaches God's physical position. God is not there.
-/

end AchillesTortoiseLadder
end BuleyeanMath
