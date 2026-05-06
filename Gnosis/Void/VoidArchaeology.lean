import Init

/-!
# Void Archaeology

A meta-module formalizing the epistemology that has been implicitly
operating across the 45+ modules in `Gnosis`.

## The four-part claim

In a closed substrate — `Init`-only, kernel-`decide`, zero-sorry —
there is information we cannot directly know. The general form of most
wall-blocked theorems (Binet, full Ramsey, continuous Gauss-Bonnet,
etc.) is unreachable. But we can:

1. **Project**: witness the claim at a finite depth where `decide`
   reaches. The full infinite theorem is not proved; a shadow of it is.
2. **Scrape the void**: exhibit a negative witness at a depth where the
   claim fails. The void has a shape — we find its edges.
3. **Reconstruct (archaeology)**: from several projections plus at
   least one void scrape, reconstruct the outline of the wall-blocked
   claim. The general theorem is not proved, but its boundary is drawn.
4. **Classify by mode**: every claim sits in one of
   `{fullyInside, projectionOnly, scrapeOnly, archaeologyOutline}` and
   the classification is decidable from the cardinalities of the
   projection / scrape samples.

## What this module does

- Defines `Dig` — a record of (claim-name, projection depths, void
  scrapes).
- Defines `EpistemicMode` and a decidable classification function.
- Provides a catalog of real digs drawn from modules already in the
  corpus (`FibLucasExtendedIdentities`, `CountBadLucasPhaseReconstruction`,
  `PellUltrametricConvergents`, `CatalanNumbersIdentity`, etc.).
- Counts projections, scrapes, and archaeologically-reconstructed digs
  via kernel `decide`.

## What this module does NOT claim

- No claim that the wall-blocked general theorems are **unprovable**.
  They are unreachable under `Init`-only + `decide`; other regimes may
  prove them in full. The void archaeology reconstructs the outline
  within our substrate.
- No claim that three projections and one scrape **guarantee** a
  correct reconstruction of the full theorem. They define a minimum
  quality bar for calling the outline "reconstructed" — a design
  heuristic, not a theorem.
- No connection to genuine Gödel / Tarski undecidability. The void
  here is wall-induced (ring-extension / category / scale), not
  metamathematical incompleteness.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace VoidArchaeology

/-! ## Epistemic mode -/

/-- The mode a claim sits in, derived from its projection/scrape sample
cardinalities. -/
inductive EpistemicMode
  /-- General theorem proved directly — substrate-complete statement. -/
  | fullyInside
  /-- Positive witnesses at finite depths; no negative witness. The
  general claim may hold or fail at unprobed depths. -/
  | projectionOnly
  /-- Negative witnesses only; the claim is scraped at its failures
  without positive confirmation anywhere. -/
  | scrapeOnly
  /-- Both positive and negative witnesses. The outline of where the
  general claim holds and where it fails has been drawn. -/
  | archaeologyOutline
  /-- Neither positive nor negative witness — unprobed. -/
  | unprobed
deriving DecidableEq, Repr

/-! ## Dig record -/

/-- A `Dig` records what has been excavated about a wall-blocked claim:
the finite depths at which positive witnesses ("projections") landed,
and the depths at which negative witnesses ("void scrapes") landed. -/
structure Dig where
  /-- Prose name of the general claim being excavated. -/
  claim : String
  /-- Depths at which the claim was positively witnessed. -/
  projections : List Nat
  /-- Depths at which the claim was negatively witnessed (fails). -/
  voidScrapes : List Nat
deriving Repr

def Dig.projCount (d : Dig) : Nat := d.projections.length

def Dig.scrapeCount (d : Dig) : Nat := d.voidScrapes.length

def Dig.samples (d : Dig) : Nat := d.projCount + d.scrapeCount

/-- Mode classification by sample cardinality. `fullyInside` is not
derivable from sample counts alone; it is flagged explicitly at the
catalog level when the general theorem is directly provable under
`Init` + `decide` (rare). -/
def Dig.mode (d : Dig) : EpistemicMode :=
  match d.projections, d.voidScrapes with
  | [], []          => EpistemicMode.unprobed
  | _ :: _, []      => EpistemicMode.projectionOnly
  | [], _ :: _      => EpistemicMode.scrapeOnly
  | _ :: _, _ :: _  => EpistemicMode.archaeologyOutline

/-- A dig reconstructs an outline when it has at least three
projections AND at least one void scrape. Design heuristic — fewer
samples leave the outline too coarse to call "reconstructed". -/
def Dig.outlineReconstructed (d : Dig) : Bool :=
  decide (d.projCount ≥ 3) && decide (d.scrapeCount ≥ 1)

/-! ## Catalog — real digs from the corpus -/

/-- From `CountBadLucasPhaseReconstruction`: phase-lifted witnesses on
`traceSeq` vs Lucas at **all** depths `n = 3 .. 12`, plus deliberate
void scrapes of the naive `+1` form at `n ∈ {3, 6, 9, 12}`. This is
the catalog encoding of the reconstruction-dense dig (≥ 3 projections
and ≥ 1 scrape — **outline reconstructed** under the design bar). -/
def dig_orbitAvoidanceLucas : Dig :=
  { claim :=
      "countBad_n vs Lucas (phase-shifted reconstruction; naive +1 form fails on 3ℤ)"
    projections := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    voidScrapes := [3, 6, 9, 12] }

/-- From `FibLucasExtendedIdentities`: Fibonacci Cassini
`F_{n-1} F_{n+1} - F_n^2 = (-1)^n`. Seven projections, no scrape
(the identity is general and holds everywhere — projection-only). -/
def dig_fibCassini : Dig :=
  { claim       := "F_{n-1} · F_{n+1} - F_n^2 = (-1)^n (Fibonacci Cassini)"
    projections := [1, 2, 3, 4, 5, 6, 7]
    voidScrapes := [] }

/-- From `IndependentSetCycleCnLucas`: `|IS(C_n)| = L_n`. Five
projections, no scrape — projection-only. -/
def dig_indSetLucas : Dig :=
  { claim       := "|IS(C_n)| = L_n (independent sets on cycle graph)"
    projections := [3, 4, 5, 6, 7]
    voidScrapes := [] }

/-- From `RamanujanPartitionMod5`: `p(5n+4) ≡ 0 (mod 5)`. Five
projections, no scrape. -/
def dig_ramanujan : Dig :=
  { claim       := "p(5n+4) ≡ 0 mod 5 (Ramanujan partition congruence)"
    projections := [0, 1, 2, 3, 4]
    voidScrapes := [] }

/-- From `PellUltrametricConvergents`: `v_2(p_n) = 0` for Pell
convergent numerators. Eight projections. -/
def dig_pell2adic : Dig :=
  { claim       := "v_2(p_n) = 0 for Pell convergent numerators"
    projections := [0, 1, 2, 3, 4, 5, 6, 7]
    voidScrapes := [] }

/-- From `JonesModPFermat`: bracket coefficient mod-p period conjecture
`period = p - 1`. Two projections at p = 3, 5 hold; one scrape at p = 7
where period collapses to 2. Archaeological outline: holds for some p,
fails for others. -/
def dig_jonesModPPeriod : Dig :=
  { claim       := "bracket T(2,n) mod-p period equals p - 1"
    projections := [3, 5]
    voidScrapes := [7] }

/-- From `RamseyR33`: the Ramsey bound at K_6. One positive
(every 2-coloring of K_6 has a mono triangle) and one negative
(the K_5 pentagon coloring has no mono triangle). Two samples,
but only 1 projection, so not yet "reconstructed" under the
≥ 3 heuristic. -/
def dig_ramseyR33 : Dig :=
  { claim       := "Every 2-coloring of K_n forces a monochromatic triangle"
    projections := [6]
    voidScrapes := [5] }

/-- From `ContinuedFractionConvergents`: Cassini identity on CF
convergents `|p_n · q_{n-1} - p_{n-1} · q_n| = 1`. Five projections
for phi, zero scrape — the identity is general. -/
def dig_cfCassini : Dig :=
  { claim       := "|p_n q_{n-1} - p_{n-1} q_n| = 1 (CF Cassini)"
    projections := [1, 2, 3, 4, 5]
    voidScrapes := [] }

/-- From `DynamicalOrbitColoring`: does every 2-coloring of a length-n
cyclic sequence force a monochromatic 3-consecutive triple? One scrape
at n = 10 (explicit avoidance coloring exhibits), one projection
elsewhere not recorded in the peer module — projection-only at n = 3
(every 2-coloring of length 3 with either all same or at least 3 same
in cyclic sense: TTT and FFF are the only failures, so forcing holds
trivially at n ≤ 3). -/
def dig_dynOrbitForcing : Dig :=
  { claim       := "Every length-n cyclic 2-coloring has monochromatic 3-consecutive"
    projections := [3]
    voidScrapes := [10] }

/-- Master catalog of digs. -/
def catalog : List Dig :=
  [ dig_orbitAvoidanceLucas
  , dig_fibCassini
  , dig_indSetLucas
  , dig_ramanujan
  , dig_pell2adic
  , dig_jonesModPPeriod
  , dig_ramseyR33
  , dig_cfCassini
  , dig_dynOrbitForcing ]

/-! ## Catalog counts -/

def reconstructedCount : Nat :=
  catalog.foldl (fun n d => if d.outlineReconstructed then n + 1 else n) 0

def projectionOnlyCount : Nat :=
  catalog.foldl (fun n d =>
    match d.mode with
    | EpistemicMode.projectionOnly => n + 1
    | _                             => n) 0

def scrapeOnlyCount : Nat :=
  catalog.foldl (fun n d =>
    match d.mode with
    | EpistemicMode.scrapeOnly => n + 1
    | _                         => n) 0

def archaeologyOutlineCount : Nat :=
  catalog.foldl (fun n d =>
    match d.mode with
    | EpistemicMode.archaeologyOutline => n + 1
    | _                                 => n) 0

def unprobedCount : Nat :=
  catalog.foldl (fun n d =>
    match d.mode with
    | EpistemicMode.unprobed => n + 1
    | _                       => n) 0

def totalProjections : Nat :=
  catalog.foldl (fun n d => n + d.projCount) 0

def totalScrapes : Nat :=
  catalog.foldl (fun n d => n + d.scrapeCount) 0

/-! ## Witnesses -/

theorem catalog_length : catalog.length = 9 := by decide

theorem projection_only_count : projectionOnlyCount = 5 := by decide
theorem scrape_only_count : scrapeOnlyCount = 0 := by decide
theorem archaeology_outline_count : archaeologyOutlineCount = 4 := by decide
theorem unprobed_count : unprobedCount = 0 := by decide

theorem total_projections : totalProjections = 44 := by decide
theorem total_scrapes : totalScrapes = 7 := by decide

theorem mode_partition_sums :
    projectionOnlyCount + scrapeOnlyCount + archaeologyOutlineCount + unprobedCount
      = catalog.length := by decide

/-- The fibCassini dig is projection-only because the identity is
general within the substrate (Fibonacci arithmetic on Int). No void
scrape exists because the claim never fails. -/
theorem fibCassini_is_projection_only :
    dig_fibCassini.mode = EpistemicMode.projectionOnly := by decide

/-- The orbitAvoidanceLucas dig is archaeological because it has both
a positive and a negative witness. -/
theorem orbitAvoidanceLucas_is_archaeological :
    dig_orbitAvoidanceLucas.mode = EpistemicMode.archaeologyOutline := by decide

/-- The jonesModPPeriod dig is archaeology-outline (2 projections + 1
scrape) and **does not** satisfy `outlineReconstructed` until at least
one more projection depth is added to the catalog record. -/
theorem jonesModPPeriod_is_outline_not_reconstructed :
    dig_jonesModPPeriod.mode = EpistemicMode.archaeologyOutline
    ∧ dig_jonesModPPeriod.outlineReconstructed = false := by decide

/-- Count of digs that have reached the reconstruction quality bar
(≥ 3 projections and ≥ 1 scrape). With the current catalog, exactly
the `orbitAvoidanceLucas` dig (synced to `CountBadLucasPhaseReconstruction`)
meets the bar. -/
theorem reconstructed_count_eq_one : reconstructedCount = 1 := by decide

theorem orbitAvoidanceLucas_outline_reconstructed :
    dig_orbitAvoidanceLucas.outlineReconstructed = true := by decide

/-! ## The master witness -/

/-- Void-archaeology summary:
- 9 digs in the catalog
- 5 projection-only (identities that are provable in principle within
  the substrate, just witnessed at specific depths)
- 4 archaeology-outline (both positive and negative witnesses, sketching
  the shape of a wall-blocked claim)
- 0 scrape-only, 0 unprobed
- 44 total projections, 7 total scrapes
- 1 dig at the reconstruction quality bar: `orbitAvoidanceLucas`
  (dense `CountBadLucasPhaseReconstruction` witness). The remaining
  archaeological sketches (`jonesModPPeriod`, `ramseyR33`, …) still sit
  below the bar until more `decide`-closed projections land.
-/
theorem void_archaeology_master :
    catalog.length = 9
    ∧ projectionOnlyCount = 5
    ∧ archaeologyOutlineCount = 4
    ∧ scrapeOnlyCount = 0
    ∧ unprobedCount = 0
    ∧ totalProjections = 44
    ∧ totalScrapes = 7
    ∧ reconstructedCount = 1
    ∧ projectionOnlyCount + scrapeOnlyCount
        + archaeologyOutlineCount + unprobedCount = catalog.length := by
  decide

/-! ## What this suggests for the next moves

`orbitAvoidanceLucas` **crossed** the reconstruction bar once
`CountBadLucasPhaseReconstruction` was folded into the catalog record
(10 projections + 4 scrapes).

The remaining **one-projection-away** pressure now sits primarily on:

- `jonesModPPeriod` — add empirically `decide`-closed bracket-period rows
  in `JonesModPFermat` at **`p = 11` and `p = 13`** (heavy `LPoly`
  arithmetic; not yet in-repo). Two more primes would raise
  `projCount` from 2 to 4 while preserving the anchored `p = 7` scrape.
- `ramseyR33` — add `R(3, k)`-style finite witnesses for `k = 3, 4, 5`
  (or equivalent coloring tables) to lift `projCount` toward 3.
- `dig_dynOrbitForcing` — already outline-shaped; optional extra
  projections at small `n` if a peer module closes them.

**Prediction (contingent on compute cost):** after the orbit sync,
`jonesModPPeriod` is the **next** likely first-cross among digs that are
still sub-bar, **if** `p = 11, 13` instances prove as cheap to kernel-close
as `p = 3, 5, 7` were.
-/

end VoidArchaeology
end Gnosis
