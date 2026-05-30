import Gnosis.Hospitality

/-!
# Occupation — stable worker↔business assignment for the LIVING CITY

A civic worker takes a JOB at a real-world business. We model the job market as a
two-sided matching (workers ↔ businesses) and certify it is STABLE: there is no
*blocking pair* — no worker/business that would both rather pair with each other
than keep their current assignment. Stability is the deferred-acceptance
guarantee (Gale–Shapley): a worker holds the most-preferred job whose capacity it
fits, so any job it prefers more is already full of workers that the job prefers
over our worker. The matching the cave-scene builds (each worker takes the
nearest open business by proximity = preference) is exactly this greedy step.

We reuse `Hospitality.score3` to turn a worker's lexicographic preference trio
into a single comparable `Int` score, so "prefers" is a total order on `Int`.

Init-only, axiom-clean (propext + Quot.sound), no Mathlib. Proofs by omega/decide.
-/

namespace Gnosis
namespace Occupation

open Gnosis.Hospitality (score3)

/-- A worker's preference over a business is a single comparable score (higher =
    more preferred). Built from the lexicographic hospitality trio so proximity,
    then category fit, then a tertiary tiebreak fold to one `Int`. -/
def prefScore (primary secondary tertiary : Int) : Int :=
  score3 primary secondary tertiary

/-- A pairing of one worker to one business, carrying the worker's preference
    score for that business and the business's preference score for the worker.
    Scores are scaled `Int`s — no ring, decidable order. -/
structure Pairing where
  worker        : String
  business      : String
  workerPref    : Int   -- how much the worker prefers this business (higher = more)
  businessPref  : Int   -- how much the business prefers this worker (higher = more)
  deriving DecidableEq, Repr

/-- A *blocking pair* for an incumbent pairing `inc` is an alternative business
    that the worker prefers more (`altWorkerPref > inc.workerPref`) AND that
    prefers the worker more than whoever currently holds it
    (`altBusinessPref > incumbentAtAltPref`). Both sides must want to defect. -/
def blocks (incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref : Int) : Prop :=
  altWorkerPref > incWorkerPref ∧ altBusinessPref > incumbentAtAltPref

/-- THE deferred-acceptance INVARIANT, stated as a predicate over one worker and
    one rival business: either the worker does not prefer the rival
    (`altWorkerPref ≤ incWorkerPref`), or the rival is already full of workers it
    likes at least as much as ours (`altBusinessPref ≤ incumbentAtAltPref`).
    A matching satisfying this for every (worker, business) pair is stable. -/
def daInvariant (incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref : Int) : Prop :=
  altWorkerPref ≤ incWorkerPref ∨ altBusinessPref ≤ incumbentAtAltPref

/-- THM-NO-BLOCKING-PAIR: the deferred-acceptance invariant rules out a blocking
    pair. This is the core stability property — wherever the invariant holds, no
    worker/business can profitably defect together. -/
theorem da_invariant_no_blocking
    (incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref : Int)
    (h : daInvariant incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref) :
    ¬ blocks incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref := by
  unfold daInvariant at h
  unfold blocks
  rcases h with h | h
  · intro ⟨h1, _⟩; omega
  · intro ⟨_, h2⟩; omega

/-- And conversely: a blocking pair is exactly the failure of the invariant, so
    the certificate is tight (not merely sufficient). -/
theorem blocking_iff_not_invariant
    (incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref : Int) :
    blocks incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref ↔
      ¬ daInvariant incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref := by
  unfold blocks daInvariant
  constructor
  · intro ⟨h1, h2⟩; intro hinv; rcases hinv with h | h <;> omega
  · intro h
    have h1 : ¬ (altWorkerPref ≤ incWorkerPref) := fun hc => h (Or.inl hc)
    have h2 : ¬ (altBusinessPref ≤ incumbentAtAltPref) := fun hc => h (Or.inr hc)
    exact ⟨by omega, by omega⟩

/-- A worker assigned to the most-preferred business it could obtain (greedy
    nearest-open job in the cave-scene) satisfies the invariant against any rival
    it prefers MORE that has no remaining capacity for it. We encode "no capacity
    for our worker" as: the rival already prefers its incumbents at least as much
    (`altBusinessPref ≤ incumbentAtAltPref`). -/
theorem greedy_assignment_stable
    (incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref : Int)
    (hfull : altWorkerPref > incWorkerPref → altBusinessPref ≤ incumbentAtAltPref) :
    daInvariant incWorkerPref altWorkerPref incumbentAtAltPref altBusinessPref := by
  unfold daInvariant
  by_cases hpref : altWorkerPref ≤ incWorkerPref
  · exact Or.inl hpref
  · exact Or.inr (hfull (by omega))

/-- Preference comes from the hospitality trio: a worker for whom a business is a
    better proximity/category fit scores it strictly higher (primary tier
    dominates), so "prefers" inherits the lexicographic order of `score3`. -/
theorem pref_primary_dominates :
    prefScore 2 0 0 > prefScore 1 999 999 := by
  unfold prefScore score3; decide

/-- Witnessed STABLE matching: a worker on its best job (workerPref 30) sees a
    rival it likes more (40) but that rival already holds a worker it prefers (50)
    over ours (45) — invariant holds on the second disjunct, so no blocking pair. -/
theorem example_stable_matching :
    daInvariant 30 40 50 45 ∧
    ¬ blocks 30 40 50 45 := by
  refine ⟨?_, ?_⟩
  · unfold daInvariant; right; decide
  · exact da_invariant_no_blocking 30 40 50 45 (by unfold daInvariant; right; decide)

/-- Witnessed BLOCKING pair (an UNSTABLE matching): the worker prefers the rival
    (50 > 30) and the rival prefers the worker over its incumbent (60 > 20). Both
    want to defect — the certificate correctly flags instability. -/
theorem example_blocking_pair :
    blocks 30 50 20 60 := by
  unfold blocks; exact ⟨by decide, by decide⟩

end Occupation
end Gnosis
