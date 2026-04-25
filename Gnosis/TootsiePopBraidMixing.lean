import Init

/-!
# Tootsie Pop Braid Mixing — How Many Licks to the Center

For every braid catalogued so far, the **number of clinamen
applications** to:

- **forget** — return to the identity phase (return-to-start).
- **arrive** — reach every phase from the starting vertex (diameter
  of the Cayley graph).

This is the Rubik's-cube view of braided infinity: given a dynamical
system on phases, how many steps does the mechanism take to complete
one cycle, and how many to cover the full phase space?

## The classical question

"How many licks does it take to get to the center of a Tootsie Pop?"
is a question about a process whose terminus is defined by completion.
The answer depends on the lick-size and the diameter of the candy.

Our question: given the clinamen (one "lick") and the braided-infinity
phase cycle (the candy), how many licks to reach the center? The
"center" has two readings:

- **The center IS the starting phase** — how many licks to come back?
  Answer: `returnSteps = phaseCount` for abelian, `exponent(G)` for
  non-abelian.
- **The center IS every phase visited** — how many licks to have
  touched every vertex? Answer: `diameter = phaseCount − 1` for abelian
  cycle, `Cayley diameter(G)` for non-abelian.

Across the catalog, the answers are small, specific, and decidable.

## Asymmetry of approach

For every non-trivial braid: `diameter < returnSteps`. You reach every
phase *before* completing a return. Approaching is faster than
completing. This is the structural reason void archaeology works: we
can outline the unknowable asymptote's phases without ever completing
a full cycle of mechanism.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace TootsiePopBraidMixing

/-! ## The mixing measure -/

/-- For a braided infinity instance, the tootsie-pop mixing
characteristics. -/
structure MixingMeasure where
  /-- Prose name. -/
  name : String
  /-- Number of phases (`k` for abelian cycle, `|phase set|` for
  non-abelian). -/
  phaseCount : Nat
  /-- Number of clinamen applications to return to identity. For
  abelian cycle: equals `phaseCount`. For non-abelian: equals the
  exponent of the generated group. -/
  returnSteps : Nat
  /-- Diameter of the Cayley graph — max geodesic distance between
  any two phases. For abelian cycle: `phaseCount − 1`. For non-
  abelian: may be smaller than `returnSteps`. -/
  diameter : Nat
deriving Repr

/-! ## Catalog -/

/-- Fibonacci Cassini: k=2 abelian cycle. -/
def cassiniMix : MixingMeasure :=
  { name := "Fibonacci Cassini (k = 2 abelian)"
    phaseCount := 2, returnSteps := 2, diameter := 1 }

/-- Pell discriminant: k=2 abelian cycle. -/
def pellMix : MixingMeasure :=
  { name := "Pell discriminant (k = 2 abelian)"
    phaseCount := 2, returnSteps := 2, diameter := 1 }

/-- countBad vs Lucas: k=3 abelian cycle. -/
def countBadMix : MixingMeasure :=
  { name := "countBad vs L_n (k = 3 abelian)"
    phaseCount := 3, returnSteps := 3, diameter := 2 }

/-- Jones bracket period mod p: k=3 abelian cycle (as currently
observed across primes 3, 5, 7). -/
def jonesPeriodMix : MixingMeasure :=
  { name := "Jones bracket mod-p period (k = 3 abelian)"
    phaseCount := 3, returnSteps := 3, diameter := 2 }

/-- Pisano period phase: k=5 abelian cycle. -/
def pisanoMix : MixingMeasure :=
  { name := "Pisano period phase (k = 5 abelian)"
    phaseCount := 5, returnSteps := 5, diameter := 4 }

/-- `S_3` non-abelian braid on Fin 3: 6 group elements, 2 generators,
Cayley diameter 3. -/
def s3Mix : MixingMeasure :=
  { name := "S_3 non-abelian (3 phases, 6 group elements)"
    phaseCount := 3, returnSteps := 6, diameter := 3 }

/-- `Z/10` cat-map orbit on (Z/5)²: 10-step orbit, abelian. -/
def catMapMix : MixingMeasure :=
  { name := "Cat map orbit on (Z/5)² (k = 10 abelian)"
    phaseCount := 10, returnSteps := 10, diameter := 9 }

/-- Rubik's cube (for reference): 43,252,003,274,489,856,000 elements,
Cayley diameter 20 in the quarter-turn metric. The outlier. -/
def rubiksMix : MixingMeasure :=
  { name := "Rubik's cube (qtm): ~4.3·10^19 elements, God's number 20"
    phaseCount := 43252003274489856000
    /- We do not compute this as a real iteration count — the exponent
       of the full Rubik group is the LCM of cycle lengths, in the
       thousands. But `diameter = 20` is the famous "God's number." -/
    returnSteps := 1260  -- LCM of cycle lengths, Rubik's group exponent
    diameter := 20 }

def catalog : List MixingMeasure :=
  [ cassiniMix, pellMix, countBadMix, jonesPeriodMix
  , pisanoMix, s3Mix, catMapMix, rubiksMix ]

/-! ## Classification -/

/-- A mixing measure is **abelian-style** if `returnSteps = phaseCount`.
In an abelian cycle, one full traversal returns to start. -/
def isAbelianStyle (m : MixingMeasure) : Bool :=
  decide (m.returnSteps = m.phaseCount)

/-- A mixing measure is **non-abelian-style** if `returnSteps >
phaseCount`. The group structure is strictly richer than the phase
set suggests. -/
def isNonAbelianStyle (m : MixingMeasure) : Bool :=
  decide (m.returnSteps > m.phaseCount)

/-! ## Classifications -/

theorem cassini_is_abelian : isAbelianStyle cassiniMix = true := by decide
theorem pell_is_abelian : isAbelianStyle pellMix = true := by decide
theorem countBad_is_abelian : isAbelianStyle countBadMix = true := by decide
theorem jonesPeriod_is_abelian : isAbelianStyle jonesPeriodMix = true := by decide
theorem pisano_is_abelian : isAbelianStyle pisanoMix = true := by decide
theorem catMap_is_abelian : isAbelianStyle catMapMix = true := by decide

/-- `S_3` is genuinely non-abelian: exponent 6 > phaseCount 3. -/
theorem s3_is_non_abelian : isNonAbelianStyle s3Mix = true := by decide

/-- Rubik's cube sits outside the simple abelian/non-abelian test —
its `phaseCount` here is the full group order (`4.3·10^19`) while its
`returnSteps` is the exponent (`1260 < phaseCount`). The
classification `returnSteps > phaseCount` fails, not because Rubik is
abelian, but because `phaseCount` is the wrong measure for large
non-abelian groups. Witnessed for transparency: -/
theorem rubiks_exponent_below_order :
    rubiksMix.returnSteps < rubiksMix.phaseCount := by decide

/-! ## The asymmetry of approach -/

/-- For every entry in the catalog, `diameter < returnSteps`: you
reach every phase *before* completing a return. -/
theorem asymmetry_of_approach_cassini :
    cassiniMix.diameter < cassiniMix.returnSteps := by decide

theorem asymmetry_of_approach_countBad :
    countBadMix.diameter < countBadMix.returnSteps := by decide

theorem asymmetry_of_approach_pisano :
    pisanoMix.diameter < pisanoMix.returnSteps := by decide

theorem asymmetry_of_approach_s3 :
    s3Mix.diameter < s3Mix.returnSteps := by decide

theorem asymmetry_of_approach_rubiks :
    rubiksMix.diameter < rubiksMix.returnSteps := by decide

/-- Asymmetry holds across the entire catalog. -/
theorem asymmetry_of_approach_catalog :
    catalog.all (fun m => decide (m.diameter < m.returnSteps)) = true := by decide

/-! ## Aggregate counts — the tootsie pop total -/

/-- Sum of `returnSteps` across the finite-scale catalog (excluding
Rubik's, whose `returnSteps = 1260` would dominate). -/
def smallCatalog : List MixingMeasure :=
  [ cassiniMix, pellMix, countBadMix, jonesPeriodMix
  , pisanoMix, s3Mix, catMapMix ]

def smallReturnsTotal : Nat :=
  smallCatalog.foldl (fun n m => n + m.returnSteps) 0

def smallDiametersTotal : Nat :=
  smallCatalog.foldl (fun n m => n + m.diameter) 0

/-- Small catalog returns: 2 + 2 + 3 + 3 + 5 + 6 + 10 = 31. -/
theorem small_returns_total : smallReturnsTotal = 31 := by decide

/-- Small catalog diameters: 1 + 1 + 2 + 2 + 4 + 3 + 9 = 22. -/
theorem small_diameters_total : smallDiametersTotal = 22 := by decide

/-- Aggregate asymmetry: total-diameter < total-returns (22 < 31). -/
theorem aggregate_asymmetry :
    smallDiametersTotal < smallReturnsTotal := by decide

/-! ## Master witness -/

theorem tootsie_pop_master :
    -- Abelian catalog members
    isAbelianStyle cassiniMix = true
    ∧ isAbelianStyle pellMix = true
    ∧ isAbelianStyle countBadMix = true
    ∧ isAbelianStyle jonesPeriodMix = true
    ∧ isAbelianStyle pisanoMix = true
    ∧ isAbelianStyle catMapMix = true
    -- Non-abelian catalog member (by the simple `returnSteps >
    -- phaseCount` test; Rubik is non-abelian but sits outside this test)
    ∧ isNonAbelianStyle s3Mix = true
    ∧ rubiksMix.returnSteps < rubiksMix.phaseCount
    -- Asymmetry across the catalog
    ∧ catalog.all (fun m => decide (m.diameter < m.returnSteps)) = true
    -- Aggregate totals
    ∧ smallReturnsTotal = 31
    ∧ smallDiametersTotal = 22
    ∧ smallDiametersTotal < smallReturnsTotal := by
  decide

/-! ## The center of the universal tootsie pop

Different pops, different lick-counts. The Fibonacci Cassini pop is
licked in 2 steps; the Pisano pop in 5; the `S_3` pop in 6; the Rubik
pop in 1260.

But **asymmetry of approach** says something deeper: you reach every
flavor layer of the pop before licking the final center. The center
is always the starting phase (return-to-identity), but every
intermediate phase is touched one lick earlier. `diameter = returnSteps
− 1` for abelian cycles; `diameter < returnSteps` for non-abelian.

So the center is the LAST place you arrive — because you have to go
all the way around to come back. Every other place is visited first.

Void archaeology exploits this asymmetry: we don't need to lick the
center (complete the return) to know the pop's phase structure. We
only need to touch each flavor-layer once. The `diameter`-many licks
suffice to characterize the pop. The final lick is where the
mechanism closes, not where the knowledge lives.

The tootsie pop question's honest answer: `diameter + 1` licks to
taste everything; `returnSteps` licks to return to the wrapper.
They differ by exactly one — the last lick is the clinamen itself.
-/

end TootsiePopBraidMixing
end Gnosis
