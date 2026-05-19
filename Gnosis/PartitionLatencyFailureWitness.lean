import Init

/-
  PartitionLatencyFailureWitness.lean
  ==================================

  Partition / refugee correspondence as latency-failure witness: message,
  recognition, care, or correction arrives after the repair window has closed.

  Cultural floor: this file uses partitioned families, refugee letters, missing
  persons, delayed permits, and late recognitions as the operator register. The
  relevant failure is not silence alone. The signal may arrive, but too late to
  restore the state it names.

  Formal reading in this repository:

  * latency failure maps to `lateSignalCannotRepairState`.
  * displacement maps to `routeBreaksKinshipGraph`.
  * grief register maps to `recognitionAfterWindowClosed`.

  This file does not adjudicate any single partition history. It names the
  categorical machine failure: delayed truth is not equivalent to timely repair.

  Repo cousins: `BeckettUnnamableWitness` (loop after data/context loss);
  `GoyaSleepOfReasonWitness` (maintenance failure); `OrwellNineteenEightyFourWitness`
  (truth speech); `ThucydidesMelianDialogueWitness` (force settlement);
  `TraumaAsStandingWave` (trauma persistence, different formal surface).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace PartitionLatencyFailureWitness

/-- Tag: a true signal arrives too late to repair the damaged state. -/
abbrev lateSignalCannotRepairState (claim : Prop) : Prop :=
  claim

/-- Tag: displacement breaks routes in the kinship / care graph. -/
abbrev routeBreaksKinshipGraph (claim : Prop) : Prop :=
  claim

/-- Tag: recognition after the repair window has closed. -/
abbrev recognitionAfterWindowClosed (claim : Prop) : Prop :=
  claim

/--
  Latency failure bundle: late signal + broken route + closed repair window.
-/
structure LatencyFailureWitness (late route recognition : Prop) where
  tooLate : lateSignalCannotRepairState late
  routeBroken : routeBreaksKinshipGraph route
  windowClosed : recognitionAfterWindowClosed recognition

theorem latency_failure_conjuncts
    (L R W : Prop) (w : LatencyFailureWitness L R W) : L ∧ R ∧ W :=
  And.intro w.tooLate (And.intro w.routeBroken w.windowClosed)

def buildLatencyFailureWitness
    (L R W : Prop) (hL : L) (hR : R) (hW : W) : LatencyFailureWitness L R W :=
  ⟨hL, hR, hW⟩

end PartitionLatencyFailureWitness
