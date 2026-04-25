import Init

/-!
# Infinity Path — The Trajectory as Object

A meta-module treating the **sequence of witnesses toward a
wall-blocked asymptote** as a mathematical object in its own right.

## The path

In `ZenosArrowWitness` each proof is a motionless arrow. Here we
shift focus: the *ordered list of depths* at which arrows are fired
is itself the interesting object. A path has:

- a **span**: the maximum depth reached,
- a **station count**: the number of arrows fired,
- **gaps**: the differences between consecutive stations,
- a **phase distribution**: how stations partition across residue
  classes mod `k`,
- a **direction**: always monotone increasing (the path moves toward
  the asymptote, not away).

Classical potential infinity considers "the limit" but not "the path
to the limit." This module inverts that emphasis. The limit is
wall-blocked and unreachable; the path is concrete and measurable.

## Reading Zeno and Achilles through the path

- Zeno's arrow: each station on the path is an arrow at rest.
- Achilles' pursuit: the path is Achilles' trajectory toward the
  tortoise (God). The path ends at the reach; the tortoise is
  beyond it.
- The "reading is the motion" reappears: the path ITSELF is the
  movement, across the stationary stations.

## What this module does

Defines `Path`, measurement functions (`span`, `stationCount`,
`gaps`, `maxGap`), and a `phaseDistribution`. Catalogs paths from
the corpus and witnesses their measurements by `decide`.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace InfinityPath

/-! ## Path as an object -/

/-- A path toward a wall-blocked asymptote: an ordered list of
natural-number depths at which witnesses have been fired. -/
structure Path where
  target : String
  stations : List Nat
deriving Repr

def Path.stationCount (p : Path) : Nat := p.stations.length

/-- The farthest station reached. -/
def Path.span (p : Path) : Nat :=
  p.stations.foldl (fun m s => if s > m then s else m) 0

/-! ## Gap measurements -/

/-- Consecutive differences along the path. -/
def consecutiveGaps : List Nat → List Nat
  | []       => []
  | [_]      => []
  | a :: b :: rest => (b - a) :: consecutiveGaps (b :: rest)

def Path.gaps (p : Path) : List Nat := consecutiveGaps p.stations

/-- Maximum gap between consecutive stations. The largest unfilled
window in the path. -/
def Path.maxGap (p : Path) : Nat :=
  p.gaps.foldl (fun m g => if g > m then g else m) 0

/-- Sum of all gaps — equals the span from first to last station. -/
def Path.totalGap (p : Path) : Nat :=
  p.gaps.foldl (· + ·) 0

/-! ## Phase distribution

Partition the stations by residue class modulo a given `k` and count
each class. This exposes the phase structure of the path: a uniformly-
populated phase distribution says "every residue class was witnessed";
a skewed one says "we sampled one phase more than others." -/

def countAtResidue (stations : List Nat) (k r : Nat) : Nat :=
  stations.foldl (fun n s => if s % k = r then n + 1 else n) 0

/-- Build the distribution list by iterating over residues, using a
`fuel` parameter for structural recursion so the kernel reduces. -/
def mkDistributionAux (stations : List Nat) (k : Nat)
    (fuel r : Nat) : List Nat :=
  match fuel with
  | 0          => []
  | fuel + 1   =>
    if r ≥ k then []
    else countAtResidue stations k r :: mkDistributionAux stations k fuel (r + 1)

/-- The phase distribution: a list of counts, one per residue class
`r ∈ {0, …, k-1}`. -/
def Path.phaseDistribution (p : Path) (k : Nat) : List Nat :=
  mkDistributionAux p.stations k k 0

/-! ## Catalogued paths -/

/-- Pisano path from `FibonacciPisanoPhaseMap`: 11 primes tested. -/
def pisanoPath : Path :=
  { target := "Pisano period phase"
    stations := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41] }

/-- countBad path from `CountBadLucasPhaseReconstruction`: 10
consecutive depths. -/
def countBadPath : Path :=
  { target := "countBad_n vs L_n"
    stations := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] }

/-- Ramanujan path from `RamanujanTripletPhase`: the three specials
and three non-specials. -/
def ramanujanPath : Path :=
  { target := "Ramanujan special primes"
    stations := [2, 3, 5, 7, 11, 13] }

/-- Ladder path from `NashSkyrmsBuleyGodLadder`: four gnosis
constants. -/
def ladderPath : Path :=
  { target := "Nash-Skyrms-Buley-God ladder"
    stations := [4, 6, 10, 12] }

def catalog : List Path :=
  [ pisanoPath, countBadPath, ramanujanPath, ladderPath ]

/-! ## Measurements -/

theorem pisano_stationCount : pisanoPath.stationCount = 11 := by decide
theorem pisano_span : pisanoPath.span = 41 := by decide
theorem pisano_maxGap : pisanoPath.maxGap = 10 := by decide

theorem countBad_stationCount : countBadPath.stationCount = 10 := by decide
theorem countBad_span : countBadPath.span = 12 := by decide
theorem countBad_maxGap : countBadPath.maxGap = 1 := by decide

theorem ramanujan_stationCount : ramanujanPath.stationCount = 6 := by decide
theorem ramanujan_span : ramanujanPath.span = 13 := by decide
theorem ramanujan_maxGap : ramanujanPath.maxGap = 4 := by decide

theorem ladder_stationCount : ladderPath.stationCount = 4 := by decide
theorem ladder_span : ladderPath.span = 12 := by decide
theorem ladder_maxGap : ladderPath.maxGap = 4 := by decide

/-! ## Phase-distribution witnesses

The countBad path at depths `{3, …, 12}` has 10 stations. Partitioned
mod 3, residues 0, 1, 2 correspond to depths:
- residue 0: {3, 6, 9, 12} → 4 stations
- residue 1: {4, 7, 10}    → 3 stations
- residue 2: {5, 8, 11}    → 3 stations

This is the exact phase distribution `CountBadLucasPhaseReconstruction`
exploits: the 4 residue-0 stations are the scrapes; the 6 residue-
{1,2} stations are the positive witnesses. -/

theorem countBad_phaseDistribution_mod3 :
    countBadPath.phaseDistribution 3 = [4, 3, 3] := by decide

/-! ## Path-shape characterizations -/

/-- The countBad path is **contiguous**: every depth from 3 to 12 is
a station. Max gap is 1. -/
theorem countBad_is_contiguous : countBadPath.maxGap = 1 := by decide

/-- The ladder path has max gap 4 (Buley at 10, God at 12 — close;
but Skyrms at 6, Buley at 10 — gap 4). -/
theorem ladder_maxGap_is_4 : ladderPath.maxGap = 4 := by decide

/-- The Pisano path is **sparse**: spans 41 with only 11 stations.
Average gap is larger than 3. -/
theorem pisano_is_sparse :
    pisanoPath.totalGap = 38
    ∧ pisanoPath.stationCount * 4 > pisanoPath.span := by decide

/-! ## Master witness -/

theorem infinity_path_witness :
    -- Station counts
    pisanoPath.stationCount = 11
    ∧ countBadPath.stationCount = 10
    ∧ ramanujanPath.stationCount = 6
    ∧ ladderPath.stationCount = 4
    -- Spans
    ∧ pisanoPath.span = 41
    ∧ countBadPath.span = 12
    ∧ ramanujanPath.span = 13
    ∧ ladderPath.span = 12
    -- Max gaps
    ∧ pisanoPath.maxGap = 10
    ∧ countBadPath.maxGap = 1
    ∧ ramanujanPath.maxGap = 4
    ∧ ladderPath.maxGap = 4
    -- countBad path phase distribution mod 3
    ∧ countBadPath.phaseDistribution 3 = [4, 3, 3] := by
  decide

/-! ## The path is the motion

Classical infinity contemplates the limit. Our substrate constructs
the path. A path is not a limit — it is the EVIDENCE of an approach
toward a limit, materialized as a finite list of stations.

Between any two stations there is a gap. Between the farthest
station and the asymptote there is an infinite gap — the wall-blocked
reach that no path can close. Paths approach but never arrive.

The `maxGap` measurement is interesting: a path with small `maxGap`
densely samples its range, leaving no phase unwitnessed; a path with
large `maxGap` has skipped regions that could harbor surprises.
`countBad` is contiguous (maxGap = 1); `Pisano` is sparse (maxGap =
10, because we only sample primes). Both are paths, but they see
different kinds of structure.

The reading is the motion. The path is the reading, made explicit
as an object. Infinity is what lies beyond every path's span.
-/

end InfinityPath
end Gnosis
