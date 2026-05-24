import Init
-- ServerTimingHeaderLeakRisk.lean
-- Anti-thesis: the Server-Timing HTTP header is a debugging aid that exposes
-- only coarse performance metrics; the information (e.g., "db;dur=12.4") is
-- too imprecise to be useful to an attacker and is only visible to developers
-- with access to browser DevTools, not to arbitrary external requesters.
-- Refutation: Server-Timing is visible to any HTTP client, not just browsers.
-- Internal service latency values create timing oracles: cache-hit vs cache-miss
-- durations (e.g., <1ms vs >50ms) reveal whether specific resources are cached,
-- enabling cache deception confirmation. Per-query database timings reveal
-- whether injected SQL predicates matched. Differential latency across endpoints
-- enables internal microservice topology enumeration without authentication.
-- In cloud environments, timing data may reveal co-resident tenant activity
-- patterns, amplifying side-channel attacks.

namespace Gnosis.Security.ServerTimingHeaderLeakRisk

-- Timing oracle: Server-Timing reveals cache-hit vs cache-miss to any HTTP client
def timingOracleRisk (serverTimingHeaderPresent : Bool) (timingHeaderStrippedAtEdge : Bool)
    (authRequiredToViewTiming : Bool) : Bool :=
  serverTimingHeaderPresent && !timingHeaderStrippedAtEdge && !authRequiredToViewTiming

theorem timing_stripped_at_edge_safe (present auth : Bool) :
    timingOracleRisk present true auth = false := by { simp [timingOracleRisk]

theorem timing_requires_auth_safe (present stripped : Bool) :
    timingOracleRisk present stripped true = false := by
  simp [timingOracleRisk]

theorem no_timing_header_safe (stripped auth : Bool) :
    timingOracleRisk false stripped auth = false := by
  simp [timingOracleRisk]

theorem present_unstripped_public_risky :
    timingOracleRisk true false false = true := by
  simp [timingOracleRisk]

-- Internal latency disclosure: per-service timing reveals microservice topology
def internalLatencyDisclosureRisk (internalServiceTimingExposed : Bool)
    (timingAggregatedOnly : Bool) : Bool :=
  internalServiceTimingExposed && !timingAggregatedOnly

theorem aggregated_only_safe (exposed : Bool) :
    internalLatencyDisclosureRisk exposed true = false := by
  simp [internalLatencyDisclosureRisk]

theorem not_exposed_safe (aggregated : Bool) :
    internalLatencyDisclosureRisk false aggregated = false := by
  simp [internalLatencyDisclosureRisk]

theorem exposed_granular_risky :
    internalLatencyDisclosureRisk true false = true := by
  simp [internalLatencyDisclosureRisk]

-- Cache-hit disclosure: timing difference confirms specific resource is cached
def cacheHitDisclosureRisk (cacheTimingIncluded : Bool) (timingVarianceMs : Nat)
    (detectableVarianceThresholdMs : Nat) : Bool :=
  cacheTimingIncluded && (detectableVarianceThresholdMs < timingVarianceMs)

theorem no_cache_timing_safe (variance threshold : Nat) :
    cacheHitDisclosureRisk false variance threshold = false := by
  simp [cacheHitDisclosureRisk]

theorem variance_within_threshold_safe (variance threshold : Nat) (h : variance ≤ threshold) :
    cacheHitDisclosureRisk true variance threshold = false := by
  simp [cacheHitDisclosureRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem variance_exceeds_threshold_risky (variance threshold : Nat)
    (h : threshold < variance) :
    cacheHitDisclosureRisk true variance threshold = true := by { simp [cacheHitDisclosureRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Endpoint enumeration: timing patterns reveal existence of internal endpoints
def endpointEnumerationRisk (timingDiffersPerEndpoint : Bool)
    (endpointExistenceConfidential : Bool)
    (timingNormalized : Bool) : Bool :=
  timingDiffersPerEndpoint && endpointExistenceConfidential && !timingNormalized

theorem timing_normalized_prevents_enum (differs confidential : Bool) :
    endpointEnumerationRisk differs confidential true = false := by { simp [endpointEnumerationRisk]

theorem endpoint_not_confidential_low_risk (differs norm : Bool) :
    endpointEnumerationRisk differs false norm = false := by
  simp [endpointEnumerationRisk]

theorem no_timing_diff_safe (confidential norm : Bool) :
    endpointEnumerationRisk false confidential norm = false := by
  simp [endpointEnumerationRisk]

theorem differs_confidential_unnormalized_risky :
    endpointEnumerationRisk true true false = true := by
  simp [endpointEnumerationRisk]

-- SQL injection timing confirmation: db;dur reveals predicate match in blind SQLi
def sqlTimingConfirmationRisk (dbTimingInServerTiming : Bool)
    (queryTimeUniform : Bool) : Bool :=
  dbTimingInServerTiming && !queryTimeUniform

theorem uniform_query_time_safe (dbTiming : Bool) :
    sqlTimingConfirmationRisk dbTiming true = false := by
  simp [sqlTimingConfirmationRisk]

theorem no_db_timing_safe (uniform : Bool) :
    sqlTimingConfirmationRisk false uniform = false := by
  simp [sqlTimingConfirmationRisk]

theorem db_timing_non_uniform_risky :
    sqlTimingConfirmationRisk true false = true := by
  simp [sqlTimingConfirmationRisk]

-- Aggregate server timing header leak risk
def aggregateServerTimingLeakRisk
    (timingPresent stripped authRequired : Bool)
    (internalExposed aggregatedOnly : Bool)
    (cacheTimingIncluded : Bool) (variance threshold : Nat)
    (differsPerEndpoint confidential normalized : Bool) : Nat :=
  (if timingOracleRisk timingPresent stripped authRequired then 1 else 0) +
  (if internalLatencyDisclosureRisk internalExposed aggregatedOnly then 1 else 0) +
  (if cacheHitDisclosureRisk cacheTimingIncluded variance threshold then 1 else 0) +
  (if endpointEnumerationRisk differsPerEndpoint confidential normalized then 1 else 0)

theorem fully_hardened_zero_timing_leak :
    aggregateServerTimingLeakRisk false true true false true false 0 10 false false true = 0 := by
  simp [aggregateServerTimingLeakRisk, timingOracleRisk, internalLatencyDisclosureRisk,
        cacheHitDisclosureRisk, endpointEnumerationRisk]

theorem all_timing_vectors_max_risk :
    aggregateServerTimingLeakRisk true false false true false true 100 5 true true false = 4 := by
  simp [aggregateServerTimingLeakRisk, timingOracleRisk, internalLatencyDisclosureRisk,
        cacheHitDisclosureRisk, endpointEnumerationRisk]

-- Economic: server timing leak scanner detection value
def serverTimingLeakDetectionValueCents (infoLeakBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (infoLeakBreachCostCents : Int) - (scannerCostCents : Int)

theorem timing_detection_profitable (breach scan : Nat) (h : scan < breach) :
    0 < serverTimingLeakDetectionValueCents breach scan := by
  simp [serverTimingLeakDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem timing_break_even (cost : Nat) :
    0 ≤ serverTimingLeakDetectionValueCents cost cost := by
  simp [serverTimingLeakDetectionValueCents]

-- Fleet ROI: server timing scan across HTTP-serving endpoints
def serverTimingFleetROI (detectionValue : Nat) (httpEndpoints : Nat) : Nat :=
  detectionValue * httpEndpoints

theorem timing_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    serverTimingFleetROI v s1 ≤ serverTimingFleetROI v s2 := by
  simp [serverTimingFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_timing_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < serverTimingFleetROI v s := by
  simp [serverTimingFleetROI]
  exact Nat.mul_pos hv hs

end ServerTimingHeaderLeakRisk
