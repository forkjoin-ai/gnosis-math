import Init
import Gnosis.AchillesTortoiseLadder
import Gnosis.AtOneMentMath
import Gnosis.AeonGamutToneShift
import Gnosis.AeonTwelveBraid
import Gnosis.AeonTwelveUnboundedClosure
import Gnosis.DiscreteModulusTactic

/-!
# Gnosis.Civil.QuasicrystalStoplightTiming

Discrete stoplight timing witnesses for a lonely car on a Gnosis clock.

The engineering formulas are encoded with integer-scaled inputs.  The green
wave model is modular: each downstream light contributes one condition,
`arrivalPhase < green`.  Adding the `(n+1)`-th light preserves the wave exactly
when the new modular condition is also green.
-/

namespace Gnosis.Civil
namespace QuasicrystalStoplightTiming

/-! ## Aeon 12-level / 10-stage traffic clock -/

/-- The stoplight reading of the Aeon level count. -/
def aeonTrafficLevels : Nat := 12

/-- The stoplight reading of the ten gnosis stages/subchapters. -/
def aeonTrafficStages : Nat := 10

/-- The product grid has 120 stations, matching `AtOneMentMath`. -/
def aeonTrafficStationCount : Nat :=
  aeonTrafficLevels * aeonTrafficStages

/-- A single diagonal tick over `(level mod 12, stage mod 10)` closes after
    60 ticks because `gcd(12,10)=2`. -/
def aeonTrafficDiagonalCycle : Nat := 60

/-- The traffic phase seen by a diagonal Aeon clock tick. -/
def aeonTrafficPhase (tick : Nat) : Nat × Nat :=
  (tick % aeonTrafficLevels, tick % aeonTrafficStages)

def aeonTrafficPhaseTrace : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => aeonTrafficPhaseTrace n ++ [aeonTrafficPhase n]

theorem aeon_traffic_station_count_matches_atonement :
    aeonTrafficStationCount = 120
    ∧ (4 * 3 * aeonTrafficStages : Nat) = aeonTrafficStationCount := by
  decide

theorem aeon_traffic_diagonal_returns_at_sixty :
    aeonTrafficPhase aeonTrafficDiagonalCycle = (0, 0) := by
  decide

theorem aeon_traffic_diagonal_not_return_at_twelve_or_ten :
    aeonTrafficPhase 12 ≠ (0, 0)
    ∧ aeonTrafficPhase 10 ≠ (0, 0) := by
  decide

/-- The diagonal 12-by-10 clock does not enumerate the whole 120-station grid
    in one pass; station `(0,1)` is already missing from the first 60 ticks. -/
theorem aeon_traffic_diagonal_misses_station_zero_one :
    (aeonTrafficPhaseTrace aeonTrafficDiagonalCycle).any (· = (0, 1)) = false := by
  decide

/-- The underlying Aeon-12 braid still returns on the twelve lattice.  The
    10-stage traffic layer refines it to the 60-tick diagonal clock above. -/
theorem aeon_twelve_braid_anchor_still_returns :
    Gnosis.AeonTwelveBraid.iterateAeon 12 (0, 0) = (0, 0) := by
  exact Gnosis.AeonTwelveBraid.aeon_12

/-- A fixed-time signal as seen by a lonely car.  Units are discrete ticks. -/
structure Stoplight where
  cycle : Nat
  green : Nat
  offset : Nat
  distance : Nat
  speed : Nat
  deriving Repr, DecidableEq

/-- Integer travel time.  A zero speed is treated as no motion. -/
def travelTime (l : Stoplight) : Nat :=
  if l.speed = 0 then 0 else l.distance / l.speed

/-- Arrival phase on the light's cycle.  A zero cycle is treated as phase 0. -/
def arrivalPhase (start : Nat) (l : Stoplight) : Nat :=
  if l.cycle = 0 then 0 else (start + travelTime l + l.offset) % l.cycle

/-- The lonely car sees green iff its arrival phase lands inside the green
    window. -/
def seesGreen (start : Nat) (l : Stoplight) : Bool :=
  decide (arrivalPhase start l < l.green)

/-- A corridor lines up when every light is green at the car's arrival. -/
def corridorAllGreen (start : Nat) (lights : List Stoplight) : Bool :=
  lights.all (seesGreen start)

/-- Count how many green windows the car hits. -/
def alignedCount (start : Nat) (lights : List Stoplight) : Nat :=
  (lights.filter (seesGreen start)).length

/-- Adding one light preserves the green wave exactly when that light is green
    and the old corridor was already green. -/
theorem add_one_light_preserves_green_wave
    (start : Nat) (lights : List Stoplight) (next : Stoplight) :
    corridorAllGreen start (lights ++ [next]) = true ↔
      corridorAllGreen start lights = true ∧ seesGreen start next = true := by
  unfold corridorAllGreen
  simp

/-- If a new light is red at arrival, the extended corridor cannot remain a
    full green wave. -/
theorem red_next_light_breaks_green_wave
    (start : Nat) (lights : List Stoplight) (next : Stoplight)
    (hRed : seesGreen start next = false) :
    corridorAllGreen start (lights ++ [next]) = false := by
  unfold corridorAllGreen
  simp [hRed]

/-- Discrete yellow-change interval:
    `Y = reaction + velocity / (2 * decel + 2 * gradeGravity)`.
    Inputs are already scaled into compatible integer units. -/
def yellowChangeInterval
    (reaction velocity decel gradeGravity : Nat) : Nat :=
  reaction + velocity / (2 * decel + 2 * gradeGravity)

/-- Discrete pedestrian clearance:
    `startup + crosswalkLength / walkSpeed + densityFactor * pedestrians`. -/
def pedestrianClearance
    (startup crosswalkLength walkSpeed densityFactor pedestrians : Nat) : Nat :=
  startup + crosswalkLength / walkSpeed + densityFactor * pedestrians

/-- Saturation flow adjusted by integer factors.  Factors are per-thousand
    multipliers, so 1000 means no adjustment. -/
def adjustedSaturationFlow
    (base laneWidth heavyVehicles grade parking : Nat) : Nat :=
  base * laneWidth * heavyVehicles * grade * parking / 1000 / 1000 / 1000 / 1000

/-- Lane capacity under effective green `g` and cycle `C`: `s * g / C`. -/
def laneCapacity (saturationFlow effectiveGreen cycleLength : Nat) : Nat :=
  if cycleLength = 0 then 0 else saturationFlow * effectiveGreen / cycleLength

/-- Webster optimum cycle length in integer-scaled form:
    `(15 * lost + 50) / (10 - sumCriticalRatioTenths)`.
    The denominator is in tenths, so `sumCriticalRatioTenths = 7` means 0.7. -/
def websterCycleLengthTenths (lostTime sumCriticalRatioTenths : Nat) : Nat :=
  if 10 ≤ sumCriticalRatioTenths then 0
  else (15 * lostTime + 50) / (10 - sumCriticalRatioTenths)

/-- Offset for a green wave: travel time plus queue clearance. -/
def greenWaveOffset (distance speed queueClearance : Nat) : Nat :=
  if speed = 0 then queueClearance else distance / speed + queueClearance

/-- Fibonacci distances give a discrete quasicrystal spacing scaffold.  They do
    not guarantee green waves by themselves; offsets still have to compensate
    for travel time modulo the cycle. -/
def phiCorridor : List Stoplight :=
  [ { cycle := 60, green := 15, offset := 5, distance := 55, speed := 1 }
  , { cycle := 60, green := 15, offset := 31, distance := 89, speed := 1 }
  , { cycle := 60, green := 15, offset := 36, distance := 144, speed := 1 }
  , { cycle := 60, green := 15, offset := 7, distance := 233, speed := 1 } ]

/-- With offsets chosen to compensate each Fibonacci travel time modulo 60, the
    lonely car hits all four green windows at start tick 0. -/
theorem phi_corridor_lines_up_at_zero :
    corridorAllGreen 0 phiCorridor = true := by
  decide

/-- Without the compensating offset, the `(n+1)`-th Fibonacci light can break
    the wave even though its spacing is still Fibonacci-like. -/
def uncompensatedNextPhiLight : Stoplight :=
  { cycle := 60, green := 15, offset := 0, distance := 377, speed := 1 }

theorem phi_spacing_alone_does_not_force_alignment :
    seesGreen 0 uncompensatedNextPhiLight = false := by
  decide

theorem uncompensated_next_phi_light_breaks_corridor :
    corridorAllGreen 0 (phiCorridor ++ [uncompensatedNextPhiLight]) = false := by
  exact red_next_light_breaks_green_wave 0 phiCorridor
    uncompensatedNextPhiLight phi_spacing_alone_does_not_force_alignment

/-- A compensated `(n+1)`-th light restores the wave: 377 mod 60 = 17, so
    offset 43 returns the arrival phase to 0. -/
def compensatedNextPhiLight : Stoplight :=
  { cycle := 60, green := 15, offset := 43, distance := 377, speed := 1 }

theorem compensated_next_phi_light_is_green :
    seesGreen 0 compensatedNextPhiLight = true := by
  decide

theorem compensated_next_phi_light_preserves_corridor :
    corridorAllGreen 0 (phiCorridor ++ [compensatedNextPhiLight]) = true := by
  decide

/-! ## Equal distance is not equal phase -/

/-- Four lights equally spaced by 60 ticks on a shared 60-tick clock.  Because
    travel time is also a multiple of the cycle, all arrivals have phase 0. -/
def equalStepAlignedCorridor : List Stoplight :=
  [ { cycle := 60, green := 15, offset := 0, distance := 60, speed := 1 }
  , { cycle := 60, green := 15, offset := 0, distance := 120, speed := 1 }
  , { cycle := 60, green := 15, offset := 0, distance := 180, speed := 1 }
  , { cycle := 60, green := 15, offset := 0, distance := 240, speed := 1 } ]

theorem equal_step_can_align_when_step_is_cycle_multiple :
    corridorAllGreen 0 equalStepAlignedCorridor = true := by
  decide

/-- Four lights equally spaced by 50 ticks on the same 60-tick clock.  Equal
    distance alone does not align phases: the second light is phase 40, outside
    the 15-tick green band. -/
def equalStepMisalignedCorridor : List Stoplight :=
  [ { cycle := 60, green := 15, offset := 0, distance := 50, speed := 1 }
  , { cycle := 60, green := 15, offset := 0, distance := 100, speed := 1 }
  , { cycle := 60, green := 15, offset := 0, distance := 150, speed := 1 }
  , { cycle := 60, green := 15, offset := 0, distance := 200, speed := 1 } ]

theorem equal_step_does_not_force_alignment :
    corridorAllGreen 0 equalStepMisalignedCorridor = false := by
  decide

/-- With a fixed shared clock and fixed speed, the required offset is the
    modular complement of travel time.  This is the discrete version of
    `Offset = D / V ± queue clearance`. -/
def phaseCompensatingOffset (cycle distance speed desiredPhase : Nat) : Nat :=
  if cycle = 0 then 0
  else
    let t := if speed = 0 then 0 else distance / speed
    (cycle + desiredPhase - (t % cycle)) % cycle

def compensatedLightForPhase
    (cycle green distance speed desiredPhase : Nat) : Stoplight :=
  { cycle := cycle
  , green := green
  , offset := phaseCompensatingOffset cycle distance speed desiredPhase
  , distance := distance
  , speed := speed }

/-- Equal 50-tick physical spacing can be made all-green by changing offsets,
    which is the real degree of freedom on a fixed shared clock. -/
def equalStepCompensatedCorridor : List Stoplight :=
  [ compensatedLightForPhase 60 15 50 1 0
  , compensatedLightForPhase 60 15 100 1 0
  , compensatedLightForPhase 60 15 150 1 0
  , compensatedLightForPhase 60 15 200 1 0 ]

theorem equal_step_compensated_offsets :
    equalStepCompensatedCorridor.map (fun l => l.offset) = [10, 20, 30, 40] := by
  decide

theorem equal_step_with_compensating_offsets_aligns :
    corridorAllGreen 0 equalStepCompensatedCorridor = true := by
  decide

theorem phase_compensating_offset_hits_desired_phase_closed_witness :
    arrivalPhase 0 (compensatedLightForPhase 60 15 377 1 0) = 0 := by
  decide

/-- Gnosis-clock finite theorem: for every first-120 integer distance, the
    shared 60-tick compensating offset lands the car at phase 0. -/
theorem phase_compensation_covers_first_120_distances :
    (List.range aeonTrafficStationCount).all
      (fun distance =>
        decide (arrivalPhase 0 (compensatedLightForPhase 60 15 distance 1 0) = 0))
      = true := by
  discrete_modulus

/-- The same finite clock check holds for every desired phase in the 60-tick
    cycle, sampled against the first 120 distances. -/
theorem phase_compensation_covers_all_sixty_phases_on_first_120_distances :
    (List.range aeonTrafficDiagonalCycle).all
      (fun phase =>
        (List.range aeonTrafficStationCount).all
          (fun distance =>
            decide (arrivalPhase 0
              (compensatedLightForPhase 60 60 distance 1 phase) = phase)))
      = true := by
  discrete_modulus

/-- The finite clock proof is explicit search over `60 × 120` closed cases.
    A fully parametric proof would have to reason inductively/casewise over
    residues instead of enumerating the Gnosis clock. -/
def finiteClockSearchSpace : Nat :=
  aeonTrafficDiagonalCycle * aeonTrafficStationCount

theorem finite_clock_search_space_is_sixty_by_one_twenty :
    finiteClockSearchSpace = 7200 := by
  decide

theorem finite_clock_search_witnesses_not_parametric_modular_arithmetic :
    finiteClockSearchSpace = aeonTrafficDiagonalCycle * aeonTrafficStationCount
    ∧ finiteClockSearchSpace = 7200 := by
  decide

/-! ## Gamut run up the Achilles-style traffic tower -/

/-- The Achilles ladder rungs projected onto the 60-tick diagonal traffic
    clock: unit-six positions scaled by ten ticks. -/
def achillesTrafficRungTicks : List Nat :=
  [ Gnosis.AchillesTortoiseLadder.nashRung * 10
  , Gnosis.AchillesTortoiseLadder.skyrmsRung * 10
  , Gnosis.AchillesTortoiseLadder.buleyRung * 10
  , Gnosis.AchillesTortoiseLadder.godRung * 10 ]

/-- The gamut tone shift contributes the decomposition-gate offset `7`. -/
def gamutTrafficShift : Nat :=
  Gnosis.AeonGamutToneShift.decompositionGate

/-- Run the gamut shift up each Achilles rung. -/
def gamutAchillesTrafficTicks : List Nat :=
  achillesTrafficRungTicks.map (fun tick => tick + gamutTrafficShift)

/-- Does the whole corridor read green at each tick in a run? -/
def runSeesAllGreenLights (ticks : List Nat) : Bool :=
  ticks.all (fun tick => corridorAllGreen tick phiCorridor)

theorem gamut_achilles_ticks_are_shifted :
    gamutTrafficShift = 7
    ∧ achillesTrafficRungTicks = [20, 30, 50, 60]
    ∧ gamutAchillesTrafficTicks = [27, 37, 57, 67] := by
  decide

/-- The gamut/Achilles run does not see all green lights on this corridor:
    the first three shifted rungs land outside the 15-tick green band. -/
theorem gamut_achilles_run_does_not_see_all_green_lights :
    runSeesAllGreenLights gamutAchillesTrafficTicks = false := by
  decide

theorem gamut_achilles_green_visibility_profile :
    corridorAllGreen 27 phiCorridor = false
    ∧ corridorAllGreen 37 phiCorridor = false
    ∧ corridorAllGreen 57 phiCorridor = false
    ∧ corridorAllGreen 67 phiCorridor = true := by
  decide

/-- On the compensated corridor, a 15-tick green window inside a 60-tick
    diagonal clock gives a one-quarter full-corridor green band. -/
theorem compensated_corridor_green_band_is_quarter_cycle :
    ((List.range aeonTrafficDiagonalCycle).filter
      (fun tick => corridorAllGreen tick phiCorridor)).length = 15 := by
  decide

/-! ## Prism-style alarm relay -/

/-- A relay state for the alarm interpretation of prismatic refraction:
    a message has bounced `bounce` times and currently carries `tick`. -/
structure PrismAlarmState where
  tick : Nat
  bounce : Nat
  deriving Repr, DecidableEq

/-- One refracted relay hop advances the carried clock by `stride`. -/
def prismAlarmRelay (stride : Nat) (s : PrismAlarmState) : PrismAlarmState :=
  { tick := s.tick + stride, bounce := s.bounce + 1 }

def iteratePrismAlarmRelay (stride : Nat) : Nat → PrismAlarmState → PrismAlarmState
  | 0, s => s
  | n + 1, s => iteratePrismAlarmRelay stride n (prismAlarmRelay stride s)

/-- The alarm is ready once the carried tick has reached the desired time. -/
def prismAlarmReady (desiredTime : Nat) (s : PrismAlarmState) : Bool :=
  decide (desiredTime ≤ s.tick)

def prismAlarmTrace (stride : Nat) (start : PrismAlarmState) : Nat → List PrismAlarmState
  | 0 => []
  | n + 1 => prismAlarmTrace stride start n ++
      [iteratePrismAlarmRelay stride n start]

/-- First relay state in a bounded trace whose carried time reaches the target. -/
def firstReadyRelay
    (stride desiredTime fuel : Nat)
    (start : PrismAlarmState) : Option PrismAlarmState :=
  (prismAlarmTrace stride start fuel).find? (prismAlarmReady desiredTime)

/-- Closed alarm witness: bouncing by the gamut shift (`7`) wakes after nine
    relays when the desired time is the 60-tick diagonal Gnosis clock. -/
theorem gamut_prism_alarm_first_ready :
    firstReadyRelay gamutTrafficShift aeonTrafficDiagonalCycle 12
      { tick := 0, bounce := 0 }
      = some { tick := 63, bounce := 9 } := by
  decide

theorem gamut_prism_alarm_not_ready_before_crossing :
    prismAlarmReady aeonTrafficDiagonalCycle
      (iteratePrismAlarmRelay gamutTrafficShift 8 { tick := 0, bounce := 0 }) = false
    ∧ prismAlarmReady aeonTrafficDiagonalCycle
      (iteratePrismAlarmRelay gamutTrafficShift 9 { tick := 0, bounce := 0 }) = true := by
  decide

theorem prism_alarm_relay_matches_gnosis_clock_crossing :
    (iteratePrismAlarmRelay gamutTrafficShift 9 { tick := 0, bounce := 0 }).tick
      = 63
    ∧ aeonTrafficDiagonalCycle ≤
      (iteratePrismAlarmRelay gamutTrafficShift 9 { tick := 0, bounce := 0 }).tick := by
  decide

/-! ## Self-similar corridor scaling -/

/-- Build a corridor by applying the same local compensation rule to each
    distance.  This is the self-similar fold: every new light is the same
    one-light construction at a new position. -/
def compensatedCorridorFromDistances
    (cycle green speed desiredPhase : Nat)
    (distances : List Nat) : List Stoplight :=
  distances.map (fun distance =>
    compensatedLightForPhase cycle green distance speed desiredPhase)

/-- Materializing the compensated corridor is linear in the number of supplied
    distances: one local compensated light per distance. -/
theorem compensated_corridor_length_scales_linearly
    (cycle green speed desiredPhase : Nat)
    (distances : List Nat) :
    (compensatedCorridorFromDistances cycle green speed desiredPhase distances).length
      = distances.length := by
  unfold compensatedCorridorFromDistances
  rw [List.length_map]

/-- The next-light construction is local: appending one compensated light is
    exactly the old corridor plus the one new local compensation. -/
theorem compensated_corridor_append_one_is_local
    (cycle green speed desiredPhase : Nat)
    (distances : List Nat)
    (nextDistance : Nat) :
    compensatedCorridorFromDistances cycle green speed desiredPhase
      (distances ++ [nextDistance])
    =
    compensatedCorridorFromDistances cycle green speed desiredPhase distances
      ++ [compensatedLightForPhase cycle green nextDistance speed desiredPhase] := by
  unfold compensatedCorridorFromDistances
  rw [List.map_append]
  rfl

/-- Closed 120-station clock witness: the self-similar compensated corridor
    over the first 120 distances has 120 lights. -/
theorem compensated_120_corridor_has_120_lights :
    (compensatedCorridorFromDistances 60 15 1 0
      (List.range aeonTrafficStationCount)).length = 120 := by
  decide

/-- Closed 120-station clock witness: every compensated light in the first
    120-distance corridor lands at the requested phase 0. -/
theorem compensated_120_corridor_all_phase_zero :
    (compensatedCorridorFromDistances 60 15 1 0
      (List.range aeonTrafficStationCount)).all
      (fun light => decide (arrivalPhase 0 light = 0)) = true := by
  decide

/-- Cost-shape summary for the shared-clock fold.  Local extension is one
    compensated light; whole-corridor materialization scales with `n`. -/
theorem self_similar_clock_fold_cost_shape :
    aeonTrafficStationCount = 120
    ∧ (compensatedCorridorFromDistances 60 15 1 0
        (List.range aeonTrafficStationCount)).length = aeonTrafficStationCount := by
  decide

/-! ## Modulus admission certificate -/

/-- Conditions that make it honest to turn a stoplight timing problem into a
    modular-clock problem. -/
structure ModulusAdmissionCertificate where
  cycle : Nat
  green : Nat
  speed : Nat
  desiredPhase : Nat
  cyclePositive : 0 < cycle
  speedPositive : 0 < speed
  greenWithinCycle : green ≤ cycle
  desiredInsideGreen : desiredPhase < green

/-- A light is admitted to the modular model when its physical timing inputs
    satisfy the clock conditions and its compensated offset lands in the green
    window. -/
def admittedByModulus
    (cert : ModulusAdmissionCertificate)
    (distance : Nat) : Bool :=
  let light :=
    compensatedLightForPhase cert.cycle cert.green distance cert.speed
      cert.desiredPhase
  decide (arrivalPhase 0 light = cert.desiredPhase)
    && decide (arrivalPhase 0 light < cert.green)

/-- The 60-tick Gnosis traffic clock with a 15-tick green window is admissible
    for modular reasoning at desired phase 0. -/
def gnosisTrafficModulusCertificate : ModulusAdmissionCertificate :=
  { cycle := 60
  , green := 15
  , speed := 1
  , desiredPhase := 0
  , cyclePositive := by decide
  , speedPositive := by decide
  , greenWithinCycle := by decide
  , desiredInsideGreen := by decide }

theorem gnosis_modulus_certificate_admits_first_120_distances :
    (List.range aeonTrafficStationCount).all
      (admittedByModulus gnosisTrafficModulusCertificate) = true := by
  decide

theorem modulus_admission_conditions_are_load_bearing :
    gnosisTrafficModulusCertificate.cycle = 60
    ∧ gnosisTrafficModulusCertificate.green = 15
    ∧ gnosisTrafficModulusCertificate.desiredPhase = 0
    ∧ gnosisTrafficModulusCertificate.green ≤ gnosisTrafficModulusCertificate.cycle
    ∧ gnosisTrafficModulusCertificate.desiredPhase <
      gnosisTrafficModulusCertificate.green := by
  decide

/-- Closed engineering sanity check using the formulas from the prompt. -/
theorem timing_formula_sanity_witness :
    yellowChangeInterval 1 88 10 0 = 5
    ∧ pedestrianClearance 32 140 35 0 12 = 36
    ∧ laneCapacity 1900 30 120 = 475
    ∧ websterCycleLengthTenths 12 7 = 76
    ∧ greenWaveOffset 1320 88 4 = 19 := by
  decide

end QuasicrystalStoplightTiming
end Gnosis.Civil
