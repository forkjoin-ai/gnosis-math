import Init
-- RateLimitingBypassRisk.lean
-- Anti-thesis: Rate limiting at the API gateway protects all back-end endpoints
-- uniformly; because limits are enforced on the authenticated user identity, IP
-- rotation cannot bypass them, and a 429 response is sufficient to stop
-- automated attacks such as credential stuffing and scraping.
-- Refutation: Rate limits keyed only on IP address are trivially bypassed by
-- residential proxy rotation. The X-Forwarded-For / X-Real-IP headers can be
-- spoofed to present a different client IP if the application trusts these
-- headers without validation against the known proxy chain. Distributed botnets
-- spread requests across thousands of IPs, each staying below per-IP thresholds.
-- Token-bucket implementations that reset on each request window allow bursting.
-- Rate limits applied per-endpoint may miss aggregate abuse across many endpoints.

namespace Gnosis.Security.RateLimitingBypassRisk

-- IP rotation bypass: rate limit keyed on IP only, proxy rotation defeats it
def ipRotationBypassRisk (rateLimitKeyedOnIPOnly : Bool)
    (proxyRotationAvailable : Bool) : Bool :=
  rateLimitKeyedOnIPOnly && proxyRotationAvailable

theorem keyed_on_identity_safe (proxyAvail : Bool) :
    ipRotationBypassRisk false proxyAvail = false := by { simp [ipRotationBypassRisk]

theorem no_proxy_rotation_available_safe (ipKeyed : Bool) :
    ipRotationBypassRisk ipKeyed false = false := by
  simp [ipRotationBypassRisk]

theorem ip_keyed_with_proxy_rotation_risky :
    ipRotationBypassRisk true true = true := by
  simp [ipRotationBypassRisk]

-- Header spoofing: X-Forwarded-For trusted without proxy chain validation
def headerSpoofingBypassRisk (xffHeaderTrusted : Bool) (proxyChainValidated : Bool) : Bool :=
  xffHeaderTrusted && !proxyChainValidated

theorem xff_not_trusted_safe (validated : Bool) :
    headerSpoofingBypassRisk false validated = false := by
  simp [headerSpoofingBypassRisk]

theorem proxy_chain_validated_safe (trusted : Bool) :
    headerSpoofingBypassRisk trusted true = false := by
  simp [headerSpoofingBypassRisk]

theorem xff_trusted_unvalidated_risky :
    headerSpoofingBypassRisk true false = true := by
  simp [headerSpoofingBypassRisk]

-- Distributed flood: botnet spreads requests across IPs below per-IP threshold
def distributedFloodBypassRisk (perIPThreshold : Nat) (botnetSize : Nat)
    (globalRateLimitEnforced : Bool) : Bool :=
  !globalRateLimitEnforced && 1 < botnetSize

theorem global_rate_limit_prevents_distributed_flood (perIP botnet : Nat) :
    distributedFloodBypassRisk perIP botnet true = false := by
  simp [distributedFloodBypassRisk]

theorem single_source_no_botnet_safe (perIP : Nat) (global : Bool) :
    distributedFloodBypassRisk perIP 1 global = false := by
  simp [distributedFloodBypassRisk]

theorem no_global_limit_large_botnet_risky (perIP : Nat) (botnet : Nat)
    (h : 1 < botnet) :
    distributedFloodBypassRisk perIP botnet false = true := by
  simp [distributedFloodBypassRisk, h]

-- Token bucket burst: reset-on-window allows burst at window boundary
def tokenBucketBurstRisk (windowResetAllowsBurst : Bool) (burstSizeExceedsLimit : Bool) : Bool :=
  windowResetAllowsBurst && burstSizeExceedsLimit

theorem sliding_window_no_burst_safe (burstExceeds : Bool) :
    tokenBucketBurstRisk false burstExceeds = false := by
  simp [tokenBucketBurstRisk]

theorem burst_within_limit_safe (windowReset : Bool) :
    tokenBucketBurstRisk windowReset false = false := by
  simp [tokenBucketBurstRisk]

theorem window_reset_burst_exceeds_risky :
    tokenBucketBurstRisk true true = true := by
  simp [tokenBucketBurstRisk]

-- Per-endpoint blind spots: aggregate abuse undetected across many endpoints
def endpointBlindSpotRisk (rateLimitPerEndpointOnly : Bool)
    (aggregateAbusePatternDetected : Bool) : Bool :=
  rateLimitPerEndpointOnly && !aggregateAbusePatternDetected

theorem aggregate_detection_safe (perEndpoint : Bool) :
    endpointBlindSpotRisk perEndpoint true = false := by
  simp [endpointBlindSpotRisk]

theorem global_rate_limit_not_per_endpoint_safe (detected : Bool) :
    endpointBlindSpotRisk false detected = false := by
  simp [endpointBlindSpotRisk]

theorem per_endpoint_only_undetected_aggregate_risky :
    endpointBlindSpotRisk true false = true := by
  simp [endpointBlindSpotRisk]

-- Aggregate rate limiting bypass risk count
def aggregateRateLimitBypassRisk
    (ipKeyedOnly proxyAvail : Bool)
    (xffTrusted proxyValidated : Bool)
    (perIPThreshold botnetSize : Nat) (globalLimit : Bool)
    (windowReset burstExceeds : Bool)
    (perEndpointOnly aggregateDetected : Bool) : Nat :=
  (if ipRotationBypassRisk ipKeyedOnly proxyAvail then 1 else 0) +
  (if headerSpoofingBypassRisk xffTrusted proxyValidated then 1 else 0) +
  (if distributedFloodBypassRisk perIPThreshold botnetSize globalLimit then 1 else 0) +
  (if tokenBucketBurstRisk windowReset burstExceeds then 1 else 0) +
  (if endpointBlindSpotRisk perEndpointOnly aggregateDetected then 1 else 0)

theorem fully_hardened_zero_rate_limit_risk :
    aggregateRateLimitBypassRisk
      false false
      false true
      100 1 true
      false false
      false true = 0 := by
  simp [aggregateRateLimitBypassRisk, ipRotationBypassRisk, headerSpoofingBypassRisk,
        distributedFloodBypassRisk, tokenBucketBurstRisk, endpointBlindSpotRisk]

theorem all_rate_limit_vectors_max_risk :
    aggregateRateLimitBypassRisk
      true true
      true false
      100 2 false
      true true
      true false = 5 := by
  simp [aggregateRateLimitBypassRisk, ipRotationBypassRisk, headerSpoofingBypassRisk,
        distributedFloodBypassRisk, tokenBucketBurstRisk, endpointBlindSpotRisk]

theorem rate_limit_risk_bounded
    (ipKeyedOnly proxyAvail : Bool)
    (xffTrusted proxyValidated : Bool)
    (perIPThreshold botnetSize : Nat) (globalLimit : Bool)
    (windowReset burstExceeds : Bool)
    (perEndpointOnly aggregateDetected : Bool) :
    aggregateRateLimitBypassRisk
      ipKeyedOnly proxyAvail xffTrusted proxyValidated
      perIPThreshold botnetSize globalLimit
      windowReset burstExceeds
      perEndpointOnly aggregateDetected ≤ 5 := by
  simp [aggregateRateLimitBypassRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: rate limit bypass detection prevents credential-stuffing breach
def rateLimitDetectionValueCents (credStuffingBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (credStuffingBreachCostCents : Int) - (scannerCostCents : Int)

theorem rate_limit_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < rateLimitDetectionValueCents breach scan := by
  simp [rateLimitDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem rate_limit_scanner_break_even (cost : Nat) :
    0 ≤ rateLimitDetectionValueCents cost cost := by
  simp [rateLimitDetectionValueCents]

-- Fleet ROI: rate limit audit across all API surfaces
def rateLimitFleetROI (detectionValueCents : Nat) (apiSurfaces : Nat) : Nat :=
  detectionValueCents * apiSurfaces

theorem rate_limit_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    rateLimitFleetROI v s1 ≤ rateLimitFleetROI v s2 := by
  simp [rateLimitFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_rate_limit_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < rateLimitFleetROI v s := by
  simp [rateLimitFleetROI]
  exact Nat.mul_pos hv hs

end RateLimitingBypassRisk
