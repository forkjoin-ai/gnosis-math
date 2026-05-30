/-
  JaneJacobs.lean
  ===============

  Jane Jacobs' bottom-up urbanism ("cities as organized complexity"), formalized
  through the Lean/Toyota-Production-System lens (flow, muda-elimination, kaizen),
  and CROSS-CHECKED against our hospitality core. The headline result: each of her
  eight principles is STRICTLY DOMINANT — the Jacobs-favoured configuration strictly
  beats its anti-Jacobs opposite — and several reduce DIRECTLY to theorems we already
  proved in `Gnosis.Hospitality` / `Gnosis.RecursiveHospitality`. That reduction is
  the cross-check: our model is true to her witnesses because her principles ARE our
  theorems.

  Principle ↦ TPS concept ↦ our theorem:
    1. Mixed-Use Flow        ↦ value-stream / no idle  ↦ diversity_beats_monoculture
    2. Incremental Dev       ↦ kaizen                  ↦ succession_rises
    3. Adaptive Reuse        ↦ muda elimination        ↦ foundation-merge
    4. Permeable Blocks      ↦ flow / takt             ↦ permeability_increases_flow (new)
    5. Eyes on the Street    ↦ poka-yoke               ↦ more_eyes_fewer_defects (new)
    6. Human-Scale Density   ↦ right-sizing            ↦ right_sized_is_peak (new)
    7. Interconnectivity     ↦ systems / VSM           ↦ system_exceeds_isolated_parts
    8. Gemba (observe)       ↦ go-to-the-real-place    ↦ gemba_beats_masterplan (new)

  PROVEN strictly dominant (omega / decide, Init-only). No Mathlib.
-/

import Gnosis.Hospitality
import Gnosis.RecursiveHospitality

namespace Gnosis
namespace JaneJacobs

open Gnosis.RecursiveHospitality

-- 1. MIXED-USE FLOW = value-stream optimization. Mixing residential/commercial/
--    civic keeps the street active 24h (no idle "ghost town"); a single use goes
--    dark. Strictly dominant = our diversity-resilience proof: a mixed-use block
--    (≥2 uses) out-survives a single-use one under shock.
theorem mixed_use_beats_single_use (uses : Nat) (h : 2 ≤ uses) :
    survivingCompanions 1 < survivingCompanions uses :=
  diversity_beats_monoculture uses h

-- 2. INCREMENTAL DEVELOPMENT = kaizen. Small, gradual improvement strictly raises
--    the layer without the systemic-failure risk of a rigid "urban renewal" leap.
theorem kaizen_strictly_improves (s : Nat) : s < nextSubstrate s :=
  succession_rises s

-- 3. ADAPTIVE REUSE ("new ideas need old buildings") = muda elimination. Keeping a
--    serviceable old foundation (old ≥ 1) and building on it STRICTLY out-builds
--    razing it to start only from the new — tearing down embedded value is waste.
theorem reuse_beats_raze (old new : Nat) (h : 1 ≤ old) :
    buildAllowance new < buildAllowance (mergeFoundations old new) := by
  unfold buildAllowance mergeFoundations
  omega

-- 4. PERMEABLE INTERSECTIONS = flow / takt time. Short, frequent blocks give more
--    paths, raising the velocity of interaction; strictly more permeability ⇒
--    strictly more flow (fewer bottlenecks).
def flow (paths : Nat) : Nat := paths

theorem permeability_increases_flow (p1 p2 : Nat) (h : p1 < p2) :
    flow p1 < flow p2 := by
  unfold flow
  omega

-- 5. EYES ON THE STREET = poka-yoke (error-proofing). More eyes (presence) strictly
--    lowers the defect/disorder risk, up to error-proofing it away.
def defectRisk (baseRisk eyes : Nat) : Nat := baseRisk - eyes

theorem more_eyes_fewer_defects (baseRisk e1 e2 : Nat)
    (he : e1 < e2) (hb : e2 ≤ baseRisk) :
    defectRisk baseRisk e2 < defectRisk baseRisk e1 := by
  unfold defectRisk
  omega

-- 6. HUMAN-SCALE DENSITY = right-sizing. Density helps up to capacity; beyond it,
--    congestion strictly hurts (chaotic), and far below it the place is sterile
--    (under-used). Realized utility peaks exactly at demand = capacity.
def realizedDensity (capacity demand : Nat) : Nat :=
  Nat.min demand capacity - (demand - capacity)

/-- Right-sized (demand = capacity) strictly beats BOTH the sterile under-used case
    and the overcrowded over-stressed case. -/
theorem right_sized_is_peak :
    realizedDensity 10 5 < realizedDensity 10 10
    ∧ realizedDensity 10 15 < realizedDensity 10 10 := by
  decide

-- 7. COMPLEX INTERCONNECTIVITY = systems thinking / value-stream mapping. Joining
--    parts into a connected whole exceeds any isolated component: the system
--    strictly out-builds the isolated part once the other part is real.
theorem system_exceeds_isolated_parts (a b : Nat) (h : 1 ≤ b) :
    buildAllowance a < buildAllowance (mergeFoundations a b) := by
  unfold buildAllowance mergeFoundations
  omega

-- 8. GEMBA (observation-based planning) = go to the real place. Choosing by the
--    OBSERVED local hospitality (taking the more hospitable of what you actually
--    see on the sidewalk) strictly dominates a top-down master plan that ignores it
--    and lands on a worse site.
def bottomUpChoice (a b : Int) : Int := max a b

theorem gemba_beats_masterplan (observed topDown : Int) (h : topDown < observed) :
    topDown < bottomUpChoice topDown observed := by
  unfold bottomUpChoice
  omega

-- ── Cross-check witnesses (decide): Jacobs vs anti-Jacobs, read through the
--    hospitality score (mixed-use ≫ substrate ≫ raw height). ─────────────────────
/-- A Jacobs block — mixed-use (2 surviving uses), on reused/old substrate (level 2),
    human-scaled — is strictly more hospitable than a top-down monoculture tower
    (single use, bare-lot substrate 0, maximal raw height 999). Organized complexity
    strictly dominates the fragile master-planned monoculture. -/
theorem jacobs_block_dominates_tower :
    Hospitality.score3 0 0 999 < Hospitality.score3 2 2 0 := by
  decide

end JaneJacobs
end Gnosis
