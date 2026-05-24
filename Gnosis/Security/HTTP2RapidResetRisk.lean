import Init
-- HTTP2RapidResetRisk.lean
-- Anti-thesis: HTTP/2 stream multiplexing is a performance feature and RST_STREAM
-- is a standard mechanism for cancelling requests; servers handle RST_STREAM
-- gracefully via stream state machines and concurrent stream limits prevent any
-- meaningful amplification, making rapid-reset a non-issue in compliant
-- HTTP/2 implementations.
-- Refutation: CVE-2023-44487 (HTTP/2 Rapid Reset) demonstrated that sending
-- HEADERS followed by RST_STREAM in rapid succession bypasses SETTINGS-based
-- concurrent stream limits, because work is initiated before the RST arrives.
-- A single client can sustain millions of requests/second with zero concurrent
-- streams at any moment. HPACK header compression tables can be bombed with
-- large dynamic table entries. Pseudo-header injection ($method, $path) in
-- malformed frames bypasses some WAF rules. The attack was exploited against
-- major cloud providers in August 2023 at record DDoS scale (398M rps).

namespace Gnosis.Security.HTTP2RapidResetRisk

-- RST_STREAM flood: HEADERS+RST_STREAM cycling bypasses stream concurrency limits
def rstStreamFloodRisk (rapidResetMitigated : Bool) (maxPendingResetStreams : Nat)
    (safeResetThreshold : Nat) : Bool :=
  !rapidResetMitigated && (safeResetThreshold < maxPendingResetStreams)

theorem rapid_reset_mitigated_safe (pending threshold : Nat) :
    rstStreamFloodRisk true pending threshold = false := by { simp [rstStreamFloodRisk]

theorem pending_within_threshold_safe (pending threshold : Nat) (h : pending ≤ threshold) :
    rstStreamFloodRisk false pending threshold = false := by
  simp [rstStreamFloodRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem unmitigated_excess_pending_streams_risky (pending threshold : Nat)
    (h : threshold < pending) :
    rstStreamFloodRisk false pending threshold = true := by { simp [rstStreamFloodRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Concurrent stream amplification: work initiated before RST arrives
def concurrentStreamAmplificationRisk (streamInitiationBeforeRSTCheck : Bool)
    (serverSideRSTThrottling : Bool) : Bool :=
  streamInitiationBeforeRSTCheck && !serverSideRSTThrottling

theorem rst_throttling_prevents_amplification (initFirst : Bool) :
    concurrentStreamAmplificationRisk initFirst true = false := by { simp [concurrentStreamAmplificationRisk]

theorem no_initiation_before_check_safe (throttle : Bool) :
    concurrentStreamAmplificationRisk false throttle = false := by
  simp [concurrentStreamAmplificationRisk]

theorem initiation_before_check_no_throttle_risky :
    concurrentStreamAmplificationRisk true false = true := by
  simp [concurrentStreamAmplificationRisk]

-- HPACK bomb: large dynamic table entries exhaust server memory
def hpackBombRisk (dynamicTableSizeLimited : Bool) (maxHeaderTableBytes : Nat)
    (safeHeaderTableBytes : Nat) : Bool :=
  !dynamicTableSizeLimited || (safeHeaderTableBytes < maxHeaderTableBytes)

theorem dynamic_table_limited_within_safe (max safe : Nat) (h : max ≤ safe) :
    hpackBombRisk true max safe = false := by
  simp [hpackBombRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem table_not_limited_risky (max safe : Nat) :
    hpackBombRisk false max safe = true := by { simp [hpackBombRisk]

theorem table_exceeds_safe_limit_risky (max safe : Nat) (h : safe < max) :
    hpackBombRisk true max safe = true := by
  simp [hpackBombRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem table_at_safe_limit_ok (n : Nat) :
    hpackBombRisk true n n = false := by { simp [hpackBombRisk]

-- Pseudo-header injection: malformed :method/:path bypass WAF/routing rules
def pseudoHeaderInjectionRisk (pseudoHeaderValidated : Bool)
    (http2AwareParsing : Bool) : Bool :=
  !pseudoHeaderValidated || !http2AwareParsing

theorem validated_and_aware_safe :
    pseudoHeaderInjectionRisk true true = false := by
  simp [pseudoHeaderInjectionRisk]

theorem not_validated_risky (aware : Bool) :
    pseudoHeaderInjectionRisk false aware = true := by
  simp [pseudoHeaderInjectionRisk]

theorem not_http2_aware_risky (validated : Bool) :
    pseudoHeaderInjectionRisk validated false = true := by
  simp [pseudoHeaderInjectionRisk]

-- Stream window exhaustion: WINDOW_UPDATE starvation halts legitimate streams
def streamWindowExhaustionRisk (flowControlEnforced : Bool)
    (perStreamWindowBytes : Nat) (minWindowThreshold : Nat) : Bool :=
  !flowControlEnforced || (perStreamWindowBytes < minWindowThreshold)

theorem flow_control_with_adequate_window (window min : Nat) (h : min ≤ window) :
    streamWindowExhaustionRisk true window min = false := by
  simp [streamWindowExhaustionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem no_flow_control_risky (window min : Nat) :
    streamWindowExhaustionRisk false window min = true := by { simp [streamWindowExhaustionRisk]

theorem window_below_minimum_risky (window min : Nat) (h : window < min) :
    streamWindowExhaustionRisk true window min = true := by
  simp [streamWindowExhaustionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Aggregate HTTP/2 rapid reset risk
def aggregateHTTP2RapidResetRisk
    (mitigated : Bool) (pending threshold : Nat)
    (initFirst throttle : Bool)
    (tableLimited : Bool) (tableMax tableSafe : Nat)
    (pseudoValidated http2Aware : Bool) : Nat :=
  (if rstStreamFloodRisk mitigated pending threshold then 1 else 0) +
  (if concurrentStreamAmplificationRisk initFirst throttle then 1 else 0) +
  (if hpackBombRisk tableLimited tableMax tableSafe then 1 else 0) +
  (if pseudoHeaderInjectionRisk pseudoValidated http2Aware then 1 else 0)

theorem fully_hardened_zero_http2_risk :
    aggregateHTTP2RapidResetRisk true 0 100 false true true 1000 4096 true true = 0 := by { simp [aggregateHTTP2RapidResetRisk, rstStreamFloodRisk, concurrentStreamAmplificationRisk,
        hpackBombRisk, pseudoHeaderInjectionRisk]

theorem all_http2_vectors_max_risk :
    aggregateHTTP2RapidResetRisk false 500 10 true false false 65536 4096 false false = 4 := by
  simp [aggregateHTTP2RapidResetRisk, rstStreamFloodRisk, concurrentStreamAmplificationRisk,
        hpackBombRisk, pseudoHeaderInjectionRisk]

-- Economic: HTTP/2 rapid reset scanner detection value (DoS prevention)
def http2RapidResetDetectionValueCents (downtimeCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (downtimeCostCents : Int) - (scannerCostCents : Int)

theorem http2_detection_profitable (downtime scan : Nat) (h : scan < downtime) :
    0 < http2RapidResetDetectionValueCents downtime scan := by
  simp [http2RapidResetDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem http2_break_even (cost : Nat) :
    0 ≤ http2RapidResetDetectionValueCents cost cost := by
  simp [http2RapidResetDetectionValueCents]

-- Fleet ROI: HTTP/2 rapid reset scan across HTTP/2-enabled services
def http2FleetROI (detectionValue : Nat) (http2Services : Nat) : Nat :=
  detectionValue * http2Services

theorem http2_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    http2FleetROI v s1 ≤ http2FleetROI v s2 := by
  simp [http2FleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_http2_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < http2FleetROI v s := by
  simp [http2FleetROI]
  exact Nat.mul_pos hv hs

end HTTP2RapidResetRisk
