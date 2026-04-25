import Init

/-!
# Archaeological Infinity Access (Medium Reading)

A meta-module characterizing the epistemic mode under which wall-blocked
classical `∀`-statements are approached in this substrate.

## The medium claim

The same classical limit `∀ n, φ(n)` can be accessed in different ways
depending on the shape of the witness collection. The infinity itself
is classical — we are not inventing a new limit object. What is new is
the **access mode**.

Three modes:

- **Uniform**: every sampled depth yields a positive witness. The
  asymptote is approached from below, no phase structure revealed.
- **Archaeological**: sampled depths split between positive and
  negative witnesses. Phase structure becomes visible; the outline of
  the limit is drawn by both sides.
- **Unknowable**: no witnesses yet. The asymptote exists in principle;
  no dig has been undertaken.

"Archaeological infinity" under this reading is not a new type of
infinity — it's a new *access mode* to the same classical potential
infinity, revealing structure that uniform approach would miss.

## What this module does

Defines `Access` and `AccessMode`, catalogs digs from the corpus, and
witnesses that each sits in a specific mode. Decidable.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace BuleyeanMath
namespace ArchaeologicalInfinityAccess

inductive AccessMode
  | uniform
  | archaeological
  | unknowable
deriving DecidableEq, Repr

structure Access where
  claim : String
  positiveSamples : List Nat
  negativeSamples : List Nat
deriving Repr

def Access.mode (a : Access) : AccessMode :=
  match a.positiveSamples, a.negativeSamples with
  | [], [] => AccessMode.unknowable
  | _ :: _, [] => AccessMode.uniform
  | [], _ :: _ => AccessMode.archaeological
  | _ :: _, _ :: _ => AccessMode.archaeological

/-! ## Catalogued accesses -/

def fibCassiniAccess : Access :=
  { claim := "Fibonacci Cassini: F_{n-1}·F_{n+1} − F_n² = (−1)^n"
    positiveSamples := [1, 2, 3, 4, 5, 6, 7]
    negativeSamples := [] }

def pisanoPhaseAccess : Access :=
  { claim := "Pisano period phase by p mod 5"
    positiveSamples := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41]
    negativeSamples := [] }

def orbitAvoidanceAccess : Access :=
  { claim := "countBad_n + 1 = L_n (naive form)"
    positiveSamples := [4, 5, 7, 8, 10, 11]
    negativeSamples := [3, 6, 9, 12] }

def ramanujanTripletAccess : Access :=
  { claim := "Exactly {5, 7, 11} are Ramanujan-special primes"
    positiveSamples := [5, 7, 11]
    negativeSamples := [2, 3, 13] }

def godBoundaryAccess : Access :=
  { claim := "Aeon + Clinamen lands on 13, not a Ramanujan special"
    positiveSamples := [4, 6, 10]
    negativeSamples := [12] }

def catalog : List Access :=
  [ fibCassiniAccess
  , pisanoPhaseAccess
  , orbitAvoidanceAccess
  , ramanujanTripletAccess
  , godBoundaryAccess ]

/-! ## Mode witnesses -/

theorem fibCassini_uniform : fibCassiniAccess.mode = AccessMode.uniform := by decide
theorem pisano_uniform : pisanoPhaseAccess.mode = AccessMode.uniform := by decide
theorem orbitAvoidance_archaeological : orbitAvoidanceAccess.mode = AccessMode.archaeological := by decide
theorem ramanujan_archaeological : ramanujanTripletAccess.mode = AccessMode.archaeological := by decide
theorem godBoundary_archaeological : godBoundaryAccess.mode = AccessMode.archaeological := by decide

/-! ## Counts -/

def countUniform : Nat :=
  catalog.foldl (fun n a =>
    match a.mode with
    | AccessMode.uniform => n + 1
    | _ => n) 0

def countArchaeological : Nat :=
  catalog.foldl (fun n a =>
    match a.mode with
    | AccessMode.archaeological => n + 1
    | _ => n) 0

def countUnknowable : Nat :=
  catalog.foldl (fun n a =>
    match a.mode with
    | AccessMode.unknowable => n + 1
    | _ => n) 0

theorem count_uniform : countUniform = 2 := by decide
theorem count_archaeological : countArchaeological = 3 := by decide
theorem count_unknowable : countUnknowable = 0 := by decide

theorem mode_partition :
    countUniform + countArchaeological + countUnknowable = catalog.length := by decide

/-! ## Master witness -/

theorem archaeological_access_witness :
    fibCassiniAccess.mode = AccessMode.uniform
    ∧ pisanoPhaseAccess.mode = AccessMode.uniform
    ∧ orbitAvoidanceAccess.mode = AccessMode.archaeological
    ∧ ramanujanTripletAccess.mode = AccessMode.archaeological
    ∧ godBoundaryAccess.mode = AccessMode.archaeological
    ∧ catalog.length = 5
    ∧ countUniform + countArchaeological + countUnknowable = catalog.length := by
  decide

/-! ## Epistemic stance

The archaeological access mode is not more powerful than uniform — it
doesn't prove anything uniform couldn't. Its advantage is that it
*reveals phase structure*. A uniform approach to "Fibonacci Cassini"
never needs to scrape, because the identity holds at every `n`. A
uniform approach to "Ramanujan specials" would miss the point: the
statement "only {5,7,11}" cannot be witnessed positively — it is
witnessed by scraping every other candidate.

Some truths require negative witnesses to be seen. Archaeological
access is the mode that uses them deliberately.
-/

end ArchaeologicalInfinityAccess
end BuleyeanMath
