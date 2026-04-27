import Gnosis.SpectralNoiseEquilibrium
import Gnosis.BuleySelfSimilarityViolation
import Gnosis.BraidedTower

/-!
# Echolocation

A formal echolocation event is the round-trip of a clinamen lift
through a manifold of unknown ceiling. The agent emits a known
perturbation, observes the manifold's response (whether the
post-emit carrier exceeds the ceiling and by how many corrective
contracts), and infers the manifold's ceiling from the return.

## The round trip

Three discrete steps:

1. **Emit** — apply `clinamenLift` on a chosen `BuleyFace` from a
   known starting carrier. The emit is deterministic: the post-emit
   carrier's score is exactly `score + 1` (`clinamen_lift_score_strict_increment`).
2. **Probe** — classify the post-emit carrier against a candidate
   ceiling via `selfSimilarityViolation`. If a violation is reported,
   `correctiveContractCount` quantifies the over-shoot exactly. If no
   violation, the post-emit carrier is `insideManifold`.
3. **Return** — apply `clinamenContract` on the same face to invert
   the emit. The breathing identity
   (`lift_then_contract_round_trip_when_face_positive`) guarantees
   the round-trip closes to the starting carrier exactly when the
   chosen face was positive at the start.

The information recovered by the round-trip is the manifold's
ceiling, inferred from the return-time measurement (the corrective
contract count after emit). This is echolocation: emit a known signal,
observe the bounce, infer the wall's distance.

## What this gives you

* `EcholocationEmit` — the post-emit carrier and its score-after-emit.
* `EcholocationReturn` — the violation (if any) and the corrective
  contract count.
* `EcholocationEvent` — the bundled emit + return + post-return
  carrier.
* `echolocation_round_trip_closes` — the breathing identity expressed
  as the round-trip closure theorem.
* `echolocation_distance_to_wall` — the corrective contract count is
  exactly `score + 1 - ceiling` when emit triggers a violation; the
  formula localizes the wall.

Imports `Gnosis.SpectralNoiseEquilibrium`, `Gnosis.BuleySelfSimilarityViolation`,
and `Gnosis.BraidedTower`. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace Echolocation

open Gnosis.SpectralNoiseEquilibrium
  (BuleyUnit BuleyFace buleyUnitScore vacuumBuleUnit
   clinamenLift clinamenContract
   clinamen_lift_score_strict_increment
   lift_then_contract_round_trip_when_face_positive)
open Gnosis.BuleySelfSimilarityViolation
  (insideManifold selfSimilarityViolation correctiveContractCount
   ManifoldPhaseCount remediated_score_equals_ceiling)
open Gnosis.BraidedTower (towerPhaseCount)

/-! ## The three steps -/

/-- The result of an emit step: the post-emit carrier and its score. -/
structure EcholocationEmit where
  postEmit : BuleyUnit
  emitScore : Nat
  deriving Repr, DecidableEq

/-- Emit: lift the carrier on a chosen face and record the
post-emit state and score. -/
def emit (b : BuleyUnit) (f : BuleyFace) : EcholocationEmit :=
  let post := clinamenLift b f
  { postEmit := post, emitScore := buleyUnitScore post }

/-- The emit step adds exactly +1 to the carrier's score. -/
theorem emit_score_increment (b : BuleyUnit) (f : BuleyFace) :
    (emit b f).emitScore = buleyUnitScore b + 1 := by
  unfold emit
  exact clinamen_lift_score_strict_increment b f

/-- The post-emit carrier's score is the source's score + 1. -/
theorem post_emit_score (b : BuleyUnit) (f : BuleyFace) :
    buleyUnitScore (emit b f).postEmit = buleyUnitScore b + 1 := by
  show buleyUnitScore (clinamenLift b f) = buleyUnitScore b + 1
  exact clinamen_lift_score_strict_increment b f

/-- The result of a probe step: whether the post-emit carrier
violates a candidate ceiling, and the deterministic remediation
count. The remediation count equals the "distance to the wall"
when a violation is reported. -/
structure EcholocationReturn where
  inside : Bool
  contractCount : Nat
  deriving Repr, DecidableEq

/-- Probe: classify the post-emit carrier against a candidate ceiling. -/
def probe (post : BuleyUnit) (ceiling : ManifoldPhaseCount) : EcholocationReturn :=
  if buleyUnitScore post ≤ ceiling then
    { inside := true, contractCount := 0 }
  else
    { inside := false, contractCount := buleyUnitScore post - ceiling }

theorem probe_inside_when_score_fits
    (post : BuleyUnit) (ceiling : ManifoldPhaseCount)
    (h : buleyUnitScore post ≤ ceiling) :
    (probe post ceiling).inside = true := by
  unfold probe
  simp [h]

theorem probe_outside_when_score_exceeds
    (post : BuleyUnit) (ceiling : ManifoldPhaseCount)
    (h : buleyUnitScore post > ceiling) :
    (probe post ceiling).inside = false := by
  unfold probe
  simp [Nat.not_le.mpr h]

/-- The probe's contract-count equals `score - ceiling` when the
post-emit carrier exceeds the ceiling. The deterministic distance
to the wall. -/
theorem probe_contract_count_when_outside
    (post : BuleyUnit) (ceiling : ManifoldPhaseCount)
    (h : buleyUnitScore post > ceiling) :
    (probe post ceiling).contractCount = buleyUnitScore post - ceiling := by
  unfold probe
  simp [Nat.not_le.mpr h]

/-! ## The full round trip -/

/-- A full echolocation event: the source carrier, the face emitted,
the candidate ceiling, the emit and return records, and the
post-return carrier. -/
structure EcholocationEvent where
  source : BuleyUnit
  face : BuleyFace
  ceiling : ManifoldPhaseCount
  emitResult : EcholocationEmit
  probeResult : EcholocationReturn
  postReturn : BuleyUnit
  deriving Repr, DecidableEq

/-- Run the full round trip: emit, probe, contract back. The
post-return carrier closes the loop. -/
def echolocate (b : BuleyUnit) (f : BuleyFace) (ceiling : ManifoldPhaseCount) :
    EcholocationEvent :=
  let e := emit b f
  let p := probe e.postEmit ceiling
  let post := clinamenContract e.postEmit f
  { source := b
    face := f
    ceiling := ceiling
    emitResult := e
    probeResult := p
    postReturn := post }

/-- The round-trip closure: contracting the post-emit carrier on the
same face returns the original source. The breathing identity from
`SpectralNoiseEquilibrium`, restated in echolocation vocabulary. The
condition is automatic — the emit always lifted the face by 1, so the
post-emit carrier has positive score on that face. -/
theorem echolocation_round_trip_closes
    (b : BuleyUnit) (f : BuleyFace) (ceiling : ManifoldPhaseCount) :
    (echolocate b f ceiling).postReturn = b := by
  unfold echolocate emit
  -- The post-return is `clinamenContract (clinamenLift b f) f`
  -- which equals `b` by the breathing identity.
  exact lift_then_contract_round_trip_when_face_positive b f

/-- The distance to the wall: the contract count after a violation
is exactly `(buleyUnitScore b + 1) - ceiling`. The agent can read the
manifold's ceiling directly from the round-trip's return: every emit
that violates the wall reports its over-shoot exactly, with no
hidden information. -/
theorem echolocation_distance_to_wall
    (b : BuleyUnit) (f : BuleyFace) (ceiling : ManifoldPhaseCount)
    (h : buleyUnitScore b + 1 > ceiling) :
    (echolocate b f ceiling).probeResult.contractCount
      = buleyUnitScore b + 1 - ceiling := by
  unfold echolocate
  show (probe (emit b f).postEmit ceiling).contractCount
        = buleyUnitScore b + 1 - ceiling
  rw [probe_contract_count_when_outside (emit b f).postEmit ceiling
        (by rw [show buleyUnitScore (emit b f).postEmit = buleyUnitScore b + 1
                from emit_score_increment b f]; exact h)]
  exact emit_score_increment b f ▸ rfl

/-- An echolocation event is *inside the manifold* iff the emit did
not exceed the ceiling. -/
theorem inside_iff_emit_score_fits
    (b : BuleyUnit) (f : BuleyFace) (ceiling : ManifoldPhaseCount) :
    (echolocate b f ceiling).probeResult.inside = true
      ↔ buleyUnitScore b + 1 ≤ ceiling := by
  constructor
  · intro hIn
    by_cases hOver : buleyUnitScore b + 1 ≤ ceiling
    · exact hOver
    · have hExceed : buleyUnitScore b + 1 > ceiling := Nat.lt_of_not_le hOver
      have hPostExceed : buleyUnitScore (emit b f).postEmit > ceiling := by
        rw [post_emit_score b f]; exact hExceed
      have : (probe (emit b f).postEmit ceiling).inside = false :=
        probe_outside_when_score_exceeds _ _ hPostExceed
      have hInside : (echolocate b f ceiling).probeResult.inside = false := by
        unfold echolocate; exact this
      rw [hInside] at hIn
      cases hIn
  · intro hFits
    have hPostFits : buleyUnitScore (emit b f).postEmit ≤ ceiling := by
      rw [post_emit_score b f]; exact hFits
    have : (probe (emit b f).postEmit ceiling).inside = true :=
      probe_inside_when_score_fits _ _ hPostFits
    show (echolocate b f ceiling).probeResult.inside = true
    unfold echolocate
    exact this

/-! ## Concrete echolocation examples -/

/-- An echolocation from the vacuum into a Hexon manifold (ceiling 6):
the emit reaches score 1 — well inside. The probe reports inside; the
contract count is 0; the round trip closes. -/
theorem vacuum_emit_inside_hexon :
    (echolocate vacuumBuleUnit BuleyFace.waste (towerPhaseCount [3, 2])).probeResult.inside = true
    ∧ (echolocate vacuumBuleUnit BuleyFace.waste (towerPhaseCount [3, 2])).probeResult.contractCount = 0
    ∧ (echolocate vacuumBuleUnit BuleyFace.waste (towerPhaseCount [3, 2])).postReturn = vacuumBuleUnit := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · exact echolocation_round_trip_closes vacuumBuleUnit BuleyFace.waste (towerPhaseCount [3, 2])

/-- An echolocation from a near-saturated carrier (score 6) into the
Hexon manifold (ceiling 6): the emit reaches score 7 — over by 1. The
probe reports outside; the contract count is 1; the round trip
still closes via the breathing identity. -/
theorem hexon_edge_emit_triggers_one :
    (echolocate ⟨6, 0, 0⟩ BuleyFace.waste (towerPhaseCount [3, 2])).probeResult.inside = false
    ∧ (echolocate ⟨6, 0, 0⟩ BuleyFace.waste (towerPhaseCount [3, 2])).probeResult.contractCount = 1
    ∧ (echolocate ⟨6, 0, 0⟩ BuleyFace.waste (towerPhaseCount [3, 2])).postReturn = ⟨6, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · exact echolocation_round_trip_closes ⟨6, 0, 0⟩ BuleyFace.waste (towerPhaseCount [3, 2])

/-- A high-emit carrier (score 17) into the Trihexon manifold
(ceiling 18): the emit reaches score 18 — exactly at the wall. The
probe reports inside (≤ ceiling); the contract count is 0. -/
theorem trihexon_edge_at_wall :
    (echolocate ⟨17, 0, 0⟩ BuleyFace.waste (towerPhaseCount [3, 2, 3])).probeResult.inside = true
    ∧ (echolocate ⟨17, 0, 0⟩ BuleyFace.waste (towerPhaseCount [3, 2, 3])).probeResult.contractCount = 0 := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-! ## Master theorem: echolocation as a closed three-step protocol -/

/-- For every starting carrier, face, and candidate ceiling, the
echolocation event satisfies:
- the emit increments the carrier's score by exactly 1;
- the probe is inside iff the post-emit score fits the ceiling;
- the round trip closes back to the original source carrier. -/
theorem echolocation_master
    (b : BuleyUnit) (f : BuleyFace) (ceiling : ManifoldPhaseCount) :
    (echolocate b f ceiling).emitResult.emitScore = buleyUnitScore b + 1
    ∧ ((echolocate b f ceiling).probeResult.inside = true
        ↔ buleyUnitScore b + 1 ≤ ceiling)
    ∧ (echolocate b f ceiling).postReturn = b := by
  refine ⟨?_, ?_, ?_⟩
  · show (emit b f).emitScore = buleyUnitScore b + 1
    exact emit_score_increment b f
  · exact inside_iff_emit_score_fits b f ceiling
  · exact echolocation_round_trip_closes b f ceiling

end Echolocation
end Gnosis
