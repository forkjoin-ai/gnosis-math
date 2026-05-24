import Init
-- APIVersioningRisk.lean
-- Anti-thesis: API versioning is a routine software engineering practice for
-- backwards compatibility; deprecated endpoints remain available only to help
-- existing clients migrate, and because they are documented as deprecated they
-- receive the same security scrutiny as current endpoints.
-- Refutation: Deprecated API endpoints routinely lack the security controls
-- added to current versions (authentication, rate limiting, input validation).
-- Shadow APIs (undocumented or forgotten routes) bypass gateway policies
-- entirely. Version skipping (going from v1 to v3 while leaving v2 accessible)
-- exposes intermediate security states. Unauthenticated v1 endpoints often
-- expose the full data model via /api/v1/admin or /api/v1/internal paths.
-- Missing Sunset headers leave clients and security teams unaware that an
-- endpoint is scheduled for removal, delaying migration and audit.

namespace Gnosis.Security.APIVersioningRisk

-- Deprecated endpoint: old API version lacks security controls of current version
def deprecatedEndpointRisk (deprecatedVersionAccessible : Bool)
    (securityControlsOnCurrentOnly : Bool) : Bool :=
  deprecatedVersionAccessible && securityControlsOnCurrentOnly

theorem deprecated_version_removed_safe (securityOnCurrent : Bool) :
    deprecatedEndpointRisk false securityOnCurrent = false := by { simp [deprecatedEndpointRisk]

theorem security_controls_on_all_versions_safe (accessible : Bool) :
    deprecatedEndpointRisk accessible false = false := by
  simp [deprecatedEndpointRisk]

theorem accessible_deprecated_with_missing_controls_risky :
    deprecatedEndpointRisk true true = true := by
  simp [deprecatedEndpointRisk]

-- Shadow API: undocumented or forgotten route bypasses gateway policy
def shadowAPIRisk (undocumentedRouteExists : Bool) (gatewayPolicyApplied : Bool) : Bool :=
  undocumentedRouteExists && !gatewayPolicyApplied

theorem gateway_policy_on_all_routes_safe (undocumented : Bool) :
    shadowAPIRisk undocumented true = false := by
  simp [shadowAPIRisk]

theorem no_undocumented_routes_safe (gatewayApplied : Bool) :
    shadowAPIRisk false gatewayApplied = false := by
  simp [shadowAPIRisk]

theorem shadow_api_bypasses_gateway_risky :
    shadowAPIRisk true false = true := by
  simp [shadowAPIRisk]

-- Version skipping: intermediate version accessible exposes security gaps
def versionSkippingRisk (intermediateVersionAccessible : Bool)
    (intermediateVersionAudited : Bool) : Bool :=
  intermediateVersionAccessible && !intermediateVersionAudited

theorem intermediate_version_inaccessible_safe (audited : Bool) :
    versionSkippingRisk false audited = false := by
  simp [versionSkippingRisk]

theorem intermediate_version_audited_safe (accessible : Bool) :
    versionSkippingRisk accessible true = false := by
  simp [versionSkippingRisk]

theorem accessible_unaudited_intermediate_risky :
    versionSkippingRisk true false = true := by
  simp [versionSkippingRisk]

-- Unauthenticated v1 endpoint: early API version lacks authentication requirement
def unauthenticatedV1Risk (v1EndpointExists : Bool) (v1RequiresAuth : Bool) : Bool :=
  v1EndpointExists && !v1RequiresAuth

theorem v1_requires_auth_safe (v1Exists : Bool) :
    unauthenticatedV1Risk v1Exists true = false := by
  simp [unauthenticatedV1Risk]

theorem v1_endpoint_removed_safe (requiresAuth : Bool) :
    unauthenticatedV1Risk false requiresAuth = false := by
  simp [unauthenticatedV1Risk]

theorem v1_exists_no_auth_risky :
    unauthenticatedV1Risk true false = true := by
  simp [unauthenticatedV1Risk]

-- Missing Sunset header: clients unaware of deprecation, audit delayed
def missingSunsetHeaderRisk (endpointDeprecated : Bool) (sunsetHeaderPresent : Bool) : Bool :=
  endpointDeprecated && !sunsetHeaderPresent

theorem sunset_header_present_safe (deprecated : Bool) :
    missingSunsetHeaderRisk deprecated true = false := by
  simp [missingSunsetHeaderRisk]

theorem endpoint_not_deprecated_safe (sunsetPresent : Bool) :
    missingSunsetHeaderRisk false sunsetPresent = false := by
  simp [missingSunsetHeaderRisk]

theorem deprecated_without_sunset_header_risky :
    missingSunsetHeaderRisk true false = true := by
  simp [missingSunsetHeaderRisk]

-- Aggregate API versioning risk count
def aggregateAPIVersioningRisk
    (deprecatedAccessible securityOnCurrent : Bool)
    (undocumentedRoute gatewayApplied : Bool)
    (intermediateAccessible intermediateAudited : Bool)
    (v1Exists v1AuthRequired : Bool)
    (deprecated sunsetPresent : Bool) : Nat :=
  (if deprecatedEndpointRisk deprecatedAccessible securityOnCurrent then 1 else 0) +
  (if shadowAPIRisk undocumentedRoute gatewayApplied then 1 else 0) +
  (if versionSkippingRisk intermediateAccessible intermediateAudited then 1 else 0) +
  (if unauthenticatedV1Risk v1Exists v1AuthRequired then 1 else 0) +
  (if missingSunsetHeaderRisk deprecated sunsetPresent then 1 else 0)

theorem fully_hardened_zero_api_versioning_risk :
    aggregateAPIVersioningRisk
      false false
      false true
      false true
      false true
      false true = 0 := by
  simp [aggregateAPIVersioningRisk, deprecatedEndpointRisk, shadowAPIRisk,
        versionSkippingRisk, unauthenticatedV1Risk, missingSunsetHeaderRisk]

theorem all_api_versioning_vectors_max_risk :
    aggregateAPIVersioningRisk
      true true
      true false
      true false
      true false
      true false = 5 := by
  simp [aggregateAPIVersioningRisk, deprecatedEndpointRisk, shadowAPIRisk,
        versionSkippingRisk, unauthenticatedV1Risk, missingSunsetHeaderRisk]

theorem api_versioning_risk_bounded
    (deprecatedAccessible securityOnCurrent : Bool)
    (undocumentedRoute gatewayApplied : Bool)
    (intermediateAccessible intermediateAudited : Bool)
    (v1Exists v1AuthRequired : Bool)
    (deprecated sunsetPresent : Bool) :
    aggregateAPIVersioningRisk
      deprecatedAccessible securityOnCurrent
      undocumentedRoute gatewayApplied
      intermediateAccessible intermediateAudited
      v1Exists v1AuthRequired
      deprecated sunsetPresent ≤ 5 := by
  simp [aggregateAPIVersioningRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: API versioning gap detection prevents data-exposure breach
def apiVersioningDetectionValueCents (dataExposureBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (dataExposureBreachCostCents : Int) - (scannerCostCents : Int)

theorem api_versioning_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < apiVersioningDetectionValueCents breach scan := by
  simp [apiVersioningDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem api_versioning_scanner_break_even (cost : Nat) :
    0 ≤ apiVersioningDetectionValueCents cost cost := by
  simp [apiVersioningDetectionValueCents]

-- Fleet ROI: API versioning scan across all API versions
def apiVersioningFleetROI (detectionValueCents : Nat) (apiVersions : Nat) : Nat :=
  detectionValueCents * apiVersions

theorem api_versioning_fleet_roi_monotone (v n1 n2 : Nat) (h : n1 ≤ n2) :
    apiVersioningFleetROI v n1 ≤ apiVersioningFleetROI v n2 := by
  simp [apiVersioningFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_api_versioning_fleet_roi (v n : Nat) (hv : 0 < v) (hn : 0 < n) :
    0 < apiVersioningFleetROI v n := by
  simp [apiVersioningFleetROI]
  exact Nat.mul_pos hv hn

end APIVersioningRisk
