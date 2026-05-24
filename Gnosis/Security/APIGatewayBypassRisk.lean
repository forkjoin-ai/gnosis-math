import Init
-- APIGatewayBypassRisk.lean
-- Anti-thesis: API gateways centralise authentication and rate limiting so
-- backend services are inherently protected; if the gateway enforces auth,
-- direct backend access is impossible from the internet.
-- Refutation: Backends with reachable IPs, path-confusion in upstream routing,
-- auth-header stripping by misconfigured proxies, and gateway-specific rate-
-- limit bypass techniques all allow reaching backends without gateway controls.

namespace Gnosis.Security.APIGatewayBypassRisk

-- Direct backend access: backend IP exposed without gateway in path
def directBackendRisk (backendIPPublic : Bool) (networkSegmented : Bool) : Bool :=
  backendIPPublic && !networkSegmented

theorem segmented_backend_safe (pub : Bool) :
    directBackendRisk pub true = false := by { simp [directBackendRisk]
  cases pub <;> simp

theorem private_backend_safe (seg : Bool) :
    directBackendRisk false seg = false := by
  simp [directBackendRisk]

theorem exposed_unsegmented_backend_risky :
    directBackendRisk true false = true := by
  simp [directBackendRisk]

-- Path confusion: alternate path bypasses gateway routing rules
def pathConfusionRisk (pathNormalized : Bool) (encodingValidated : Bool) : Bool :=
  !pathNormalized || !encodingValidated

theorem normalized_and_validated_safe :
    pathConfusionRisk true true = false := by
  simp [pathConfusionRisk]

theorem unnormalized_path_risky (enc : Bool) :
    pathConfusionRisk false enc = true := by
  simp [pathConfusionRisk]

theorem unvalidated_encoding_risky (norm : Bool) :
    pathConfusionRisk norm false = true := by
  simp [pathConfusionRisk]
  cases norm <;> simp

-- Auth header stripping: proxy removes auth headers before backend
def authHeaderStrippingRisk (gatewayAddsAuthHeader : Bool)
    (backendTrustsGateway : Bool) : Bool :=
  !gatewayAddsAuthHeader && backendTrustsGateway

theorem gateway_adds_header_safe (trust : Bool) :
    authHeaderStrippingRisk true trust = false := by
  simp [authHeaderStrippingRisk]

theorem backend_not_trusting_gateway_safe (adds : Bool) :
    authHeaderStrippingRisk adds false = false := by
  simp [authHeaderStrippingRisk]
  cases adds <;> simp

theorem stripped_header_with_trusting_backend_risky :
    authHeaderStrippingRisk false true = true := by
  simp [authHeaderStrippingRisk]

-- Rate limit bypass: requests sent directly skip gateway throttle
def rateLimitBypassRisk (rateLimitAtGateway : Bool)
    (rateLimitAtBackend : Bool) : Bool :=
  rateLimitAtGateway && !rateLimitAtBackend

theorem no_gateway_rate_limit_no_bypass_risk (backend : Bool) :
    rateLimitBypassRisk false backend = false := by
  simp [rateLimitBypassRisk]

theorem backend_also_rate_limited_safe (gateway : Bool) :
    rateLimitBypassRisk gateway true = false := by
  simp [rateLimitBypassRisk]
  cases gateway <;> simp

theorem gateway_only_rate_limit_bypassable :
    rateLimitBypassRisk true false = true := by
  simp [rateLimitBypassRisk]

-- Upstream routing: misconfigured upstream exposes internal routes
def upstreamRoutingRisk (routesValidated : Bool) (internalRoutesExposed : Bool) : Bool :=
  !routesValidated && internalRoutesExposed

theorem validated_routes_safe (exposed : Bool) :
    upstreamRoutingRisk true exposed = false := by
  simp [upstreamRoutingRisk]

theorem no_internal_routes_safe (validated : Bool) :
    upstreamRoutingRisk validated false = false := by
  simp [upstreamRoutingRisk]
  cases validated <;> simp

theorem unvalidated_internal_routes_risky :
    upstreamRoutingRisk false true = true := by
  simp [upstreamRoutingRisk]

-- mTLS enforcement: mutual TLS between gateway and backend prevents direct access
def mtlsEnforcementRisk (mtlsEnabled : Bool) (certPinned : Bool) : Nat :=
  if mtlsEnabled && certPinned then 0 else 1

theorem mtls_pinned_safe :
    mtlsEnforcementRisk true true = 0 := by
  simp [mtlsEnforcementRisk]

theorem no_mtls_risky (pinned : Bool) :
    0 < mtlsEnforcementRisk false pinned := by
  simp [mtlsEnforcementRisk]
  cases pinned <;> simp

theorem unpinned_mtls_risky (enabled : Bool) :
    0 < mtlsEnforcementRisk enabled false := by
  simp [mtlsEnforcementRisk]
  cases enabled <;> simp

-- Aggregate API gateway bypass risk
def apiGatewayTotalRisk (backendPrivate : Bool) (segmented : Bool)
    (pathNorm : Bool) (encValidated : Bool)
    (gatewayAddsAuth : Bool) (backendTrusts : Bool)
    (backendRateLimited : Bool) (routesValidated : Bool)
    (mtlsEnabled : Bool) (certPinned : Bool) : Nat :=
  (if directBackendRisk (!backendPrivate) segmented then 1 else 0) +
  (if pathConfusionRisk pathNorm encValidated then 1 else 0) +
  (if authHeaderStrippingRisk gatewayAddsAuth backendTrusts then 1 else 0) +
  (if upstreamRoutingRisk routesValidated false then 1 else 0) +
  mtlsEnforcementRisk mtlsEnabled certPinned

theorem api_gateway_risk_zero_full_controls :
    apiGatewayTotalRisk true true true true true false true true true true = 0 := by
  simp [apiGatewayTotalRisk, directBackendRisk, pathConfusionRisk,
        authHeaderStrippingRisk, upstreamRoutingRisk, mtlsEnforcementRisk]

theorem api_gateway_risk_positive_no_segmentation :
    0 < apiGatewayTotalRisk false false true true true false true true true true := by
  simp [apiGatewayTotalRisk, directBackendRisk, pathConfusionRisk,
        authHeaderStrippingRisk, upstreamRoutingRisk, mtlsEnforcementRisk]

-- Defence: mTLS is an independent layer that reduces bypass risk
theorem mtls_reduces_risk (bp seg pn ev ga bt brl rv : Bool) :
    apiGatewayTotalRisk bp seg pn ev ga bt brl rv true true ≤
    apiGatewayTotalRisk bp seg pn ev ga bt brl rv false false := by
  simp [apiGatewayTotalRisk, mtlsEnforcementRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Defence: both gateway and backend controls are required
theorem defence_in_depth_required :
    authHeaderStrippingRisk false true = true ∧
    authHeaderStrippingRisk true false = false := by
  simp [authHeaderStrippingRisk]

end APIGatewayBypassRisk
