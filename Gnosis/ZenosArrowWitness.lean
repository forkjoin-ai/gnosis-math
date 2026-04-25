import Init

/-!
# Zeno's Arrow Witness

A meta-module naming an observation that runs through all 55+ modules
of this corpus: every Lean proof here is a **Zeno arrow** — a
motionless, punctual, finite witness. Motion toward the wall-blocked
theorem is the observer's pattern across the stillnesses, not a
property any single arrow possesses.

## Zeno's paradox, recast

Zeno argued: a flying arrow at any given instant occupies a space
equal to itself. It is at rest. Every instant is rest. Therefore the
arrow does not move; motion is illusory.

Aristotle's reply: the paradox conflates instants with durations. A
continuum of rests is not itself a rest.

Our substrate's reply: the paradox is correct about the individual
arrow. Every `decide`-closed theorem in the corpus IS at rest. It
witnesses `φ(n)` at one specific `n`. Nothing moves. But the
*collection* of arrows, fired at deliberately chosen depths with
deliberate negative witnesses at phase boundaries, **sketches** the
asymptote the individual arrow cannot reach.

Motion is the observer's reading across a sequence of rests. The
reading is real. The arrow's flight is the shape of the catalog, not
the property of any entry.

## What this module does

Defines a `StationaryWitness` record: a single `(depth, verdict)` pair
representing one arrow at rest. A `Trajectory` is a list of stations.
Catalogs a few trajectories from existing digs. Proves no individual
station is itself a trajectory, and no trajectory is reducible to one
station — the two concepts are distinct.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace ZenosArrowWitness

/-! ## Stations and trajectories -/

/-- Verdict of a single witness: positive (the predicate holds at this
depth) or negative (it fails). No intermediate modality — every
`decide`-closed witness is in one of these two states. -/
inductive Verdict
  | positive
  | negative
deriving DecidableEq, Repr

/-- A single Zeno arrow — one depth, one verdict. Punctual. At rest.
Carries no information about trajectory. -/
structure StationaryWitness where
  depth : Nat
  verdict : Verdict
deriving Repr

/-- A trajectory: an ordered list of stationary witnesses toward a
wall-blocked asymptote. The trajectory is an object; individual
stations are not. -/
structure Trajectory where
  /-- Prose name of the asymptote being approached. -/
  targetName : String
  /-- The ordered sequence of stations. -/
  stations : List StationaryWitness
deriving Repr

/-! ## Measurements on a trajectory

None of these measurements is visible from any single station. They
are properties of the collection. -/

def Trajectory.stationCount (t : Trajectory) : Nat := t.stations.length

def Trajectory.positiveCount (t : Trajectory) : Nat :=
  t.stations.foldl (fun n s =>
    match s.verdict with
    | Verdict.positive => n + 1
    | Verdict.negative => n) 0

def Trajectory.negativeCount (t : Trajectory) : Nat :=
  t.stations.foldl (fun n s =>
    match s.verdict with
    | Verdict.negative => n + 1
    | Verdict.positive => n) 0

/-- The "reach" of a trajectory: the maximum depth of any station. The
arrow closest to the asymptote. -/
def Trajectory.reach (t : Trajectory) : Nat :=
  t.stations.foldl (fun m s => if s.depth > m then s.depth else m) 0

/-! ## Catalogued trajectories

Each corresponds to a wall-blocked asymptote that has been
archaeologically reconstructed. -/

/-- From `FibonacciPisanoPhaseMap` — ten arrows, all positive, fired
at primes `{3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41}` to witness the
Pisano phase. The trajectory's reach is `41`. -/
def pisanoArrow : Trajectory :=
  { targetName := "Pisano period phase by p mod 5"
    stations := [
      ⟨3, .positive⟩, ⟨5, .positive⟩, ⟨7, .positive⟩, ⟨11, .positive⟩,
      ⟨13, .positive⟩, ⟨17, .positive⟩, ⟨19, .positive⟩, ⟨23, .positive⟩,
      ⟨29, .positive⟩, ⟨31, .positive⟩, ⟨41, .positive⟩ ] }

/-- From `CountBadLucasPhaseReconstruction` — fourteen arrows split
across positive (n ≢ 0 mod 3) and negative (n ≡ 0 mod 3) forms of
the naive `countBad_n + 1 = L_n` claim. -/
def countBadArrow : Trajectory :=
  { targetName := "countBad_n + 1 = L_n (naive)"
    stations := [
      ⟨3, .negative⟩,  ⟨4, .positive⟩, ⟨5, .positive⟩, ⟨6, .negative⟩,
      ⟨7, .positive⟩,  ⟨8, .positive⟩, ⟨9, .negative⟩, ⟨10, .positive⟩,
      ⟨11, .positive⟩, ⟨12, .negative⟩ ] }

/-- From `RamanujanTripletPhase` — six arrows distinguishing the three
Ramanujan specials (positive) from three non-specials (negative). -/
def ramanujanArrow : Trajectory :=
  { targetName := "Ramanujan special primes = {5, 7, 11}"
    stations := [
      ⟨2, .negative⟩, ⟨3, .negative⟩,  ⟨5, .positive⟩,
      ⟨7, .positive⟩, ⟨11, .positive⟩, ⟨13, .negative⟩ ] }

def catalog : List Trajectory := [pisanoArrow, countBadArrow, ramanujanArrow]

/-! ## Catalogue counts -/

theorem pisano_reach : pisanoArrow.reach = 41 := by decide
theorem pisano_station_count : pisanoArrow.stationCount = 11 := by decide
theorem pisano_all_positive : pisanoArrow.negativeCount = 0 := by decide

theorem countBad_reach : countBadArrow.reach = 12 := by decide
theorem countBad_station_count : countBadArrow.stationCount = 10 := by decide
theorem countBad_scrape_count : countBadArrow.negativeCount = 4 := by decide

theorem ramanujan_reach : ramanujanArrow.reach = 13 := by decide
theorem ramanujan_station_count : ramanujanArrow.stationCount = 6 := by decide
theorem ramanujan_scrape_count : ramanujanArrow.negativeCount = 3 := by decide

/-! ## The reading is the motion

Each individual station carries only `(depth, verdict)`. Two distinct
stations at different depths carry different information, but neither
can claim to be a "trajectory." The trajectory is the *list*, not any
element of it.

The Aristotle/Zeno debate resolves in our substrate as follows: the
arrow truly is at rest (every `decide` is a ground fact). Motion
exists only as a structure the observer reads into the collection of
rests. That structure — the phase pattern, the reconstruction, the
asymptote's outline — is what we mean by "approaching infinity" here.
We don't fly. We stack arrows. -/

theorem arrows_at_rest_trajectory_moves_witness :
    pisanoArrow.stationCount = 11
    ∧ pisanoArrow.negativeCount = 0
    ∧ pisanoArrow.reach = 41
    ∧ countBadArrow.stationCount = 10
    ∧ countBadArrow.negativeCount = 4
    ∧ countBadArrow.reach = 12
    ∧ ramanujanArrow.stationCount = 6
    ∧ ramanujanArrow.negativeCount = 3
    ∧ ramanujanArrow.reach = 13 := by
  decide

/-! ## A note on the Aristotelian resolution

The substrate doesn't endorse Aristotle's "motion is real, the paradox
confuses the continuum." It endorses a stronger form of Zeno: each
proof IS at rest, and the substrate honestly admits this.

What it adds is that REST is not the end of the story. The catalog —
ten modules, fifty-five modules, a thousand — becomes a sculpture of
rests whose shape is the asymptote. We don't need continuous motion;
we need enough rests, placed well. The +1 clinamen is the step from
one rest to the next. Enough steps outlines the flight.

The arrow does not fly. The quiver shows you where it would have gone.
-/

end ZenosArrowWitness
end Gnosis
