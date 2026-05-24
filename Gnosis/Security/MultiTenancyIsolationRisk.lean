import Init
-- MultiTenancyIsolationRisk.lean
-- Anti-thesis: Multi-tenancy isolation is a solved problem in SaaS platforms;
-- each tenant gets a separate database schema or row-level security policy,
-- and because the application always filters by the authenticated tenant ID,
-- cross-tenant data access is impossible by construction.
-- Refutation: Tenant ID read from a user-controlled request parameter rather
-- than the authenticated session allows horizontal escalation. Missing row-level
-- security on database views or materialised views leaks aggregated data across
-- tenants. Shared caches (Redis, Memcached) without tenant-specific key prefixes
-- allow cross-tenant cache reads. Bulk export_ or reporting endpoints that
-- iterate over internal IDs rather than tenant-scoped_ IDs expose other tenants'
-- data. Privilege boundaries between tenant admin and super-admin roles are
-- frequently collapsed in code that reuses the same permission check helper.

namespace Gnosis.Security.MultiTenancyIsolationRisk

-- Tenant ID from request: attacker supplies arbitrary tenant ID in request
def tenantIDFromRequestRisk (tenantIDFromRequest : Bool)
    (tenantIDFromAuthSession : Bool) : Bool :=
  tenantIDFromRequest && !tenantIDFromAuthSession

theorem tenant_id_from_session_safe (fromRequest : Bool) :
    tenantIDFromRequestRisk fromRequest true = false := by { simp [tenantIDFromRequestRisk]

theorem tenant_id_not_from_request_safe (fromSession : Bool) :
    tenantIDFromRequestRisk false fromSession = false := by
  simp [tenantIDFromRequestRisk]

theorem tenant_id_request_no_session_check_risky :
    tenantIDFromRequestRisk true false = true := by
  simp [tenantIDFromRequestRisk]

-- Data leakage via views: missing RLS on DB view exposes cross-tenant aggregate
def viewDataLeakageRisk (viewWithoutRLS : Bool) (viewContainsCrossTenantData : Bool) : Bool :=
  viewWithoutRLS && viewContainsCrossTenantData

theorem rls_on_view_safe (crossTenantData : Bool) :
    viewDataLeakageRisk false crossTenantData = false := by
  simp [viewDataLeakageRisk]

theorem view_scoped_to_single_tenant_safe (noRLS : Bool) :
    viewDataLeakageRisk noRLS false = false := by
  simp [viewDataLeakageRisk]

theorem view_without_rls_cross_tenant_data_risky :
    viewDataLeakageRisk true true = true := by
  simp [viewDataLeakageRisk]

-- Shared cache: cache key lacks tenant prefix allowing cross-tenant read
def sharedCacheLeakRisk (cacheKeyIncludesTenantID : Bool)
    (cacheSharedAcrossTenants : Bool) : Bool :=
  !cacheKeyIncludesTenantID && cacheSharedAcrossTenants

theorem cache_key_scoped_to_tenant_safe (shared : Bool) :
    sharedCacheLeakRisk true shared = false := by
  simp [sharedCacheLeakRisk]

theorem cache_per_tenant_safe (tenantInKey : Bool) :
    sharedCacheLeakRisk tenantInKey false = false := by
  simp [sharedCacheLeakRisk]

theorem shared_cache_without_tenant_key_risky :
    sharedCacheLeakRisk false true = true := by
  simp [sharedCacheLeakRisk]

-- Cross-tenant query: bulk endpoint iterates by internal ID not tenant-scoped_ ID
def crossTenantQueryRisk (queryUsesInternalID : Bool)
    (internalIDScopedToTenant : Bool) : Bool :=
  queryUsesInternalID && !internalIDScopedToTenant

theorem internal_id_scoped_to_tenant_safe (usesInternal : Bool) :
    crossTenantQueryRisk usesInternal true = false := by
  simp [crossTenantQueryRisk]

theorem query_does_not_use_internal_id_safe (scoped_ : Bool) :
    crossTenantQueryRisk false scoped_ = false := by
  simp [crossTenantQueryRisk]

theorem internal_id_unscoped_cross_tenant_risky :
    crossTenantQueryRisk true false = true := by
  simp [crossTenantQueryRisk]

-- Privilege boundary collapse: tenant admin role can escalate to super-admin
def privilegeBoundaryCollapseRisk (tenantAdminCanCallSuperAdminAPI : Bool)
    (superAdminAPIRequiresSeparateAuth : Bool) : Bool :=
  tenantAdminCanCallSuperAdminAPI && !superAdminAPIRequiresSeparateAuth

theorem separate_auth_for_super_admin_safe (tenantAdminAccess : Bool) :
    privilegeBoundaryCollapseRisk tenantAdminAccess true = false := by
  simp [privilegeBoundaryCollapseRisk]

theorem tenant_admin_cannot_call_super_admin_api_safe (separateAuth : Bool) :
    privilegeBoundaryCollapseRisk false separateAuth = false := by
  simp [privilegeBoundaryCollapseRisk]

theorem tenant_admin_super_admin_no_separate_auth_risky :
    privilegeBoundaryCollapseRisk true false = true := by
  simp [privilegeBoundaryCollapseRisk]

-- Aggregate multi-tenancy isolation risk count
def aggregateMultiTenancyIsolationRisk
    (tenantIDFromReq tenantIDFromSession : Bool)
    (viewNoRLS viewCrossData : Bool)
    (cacheKeyHasTenant cacheShared : Bool)
    (queryInternalID internalScoped : Bool)
    (tenantAdminSuperAPI superAdminSeparateAuth : Bool) : Nat :=
  (if tenantIDFromRequestRisk tenantIDFromReq tenantIDFromSession then 1 else 0) +
  (if viewDataLeakageRisk viewNoRLS viewCrossData then 1 else 0) +
  (if sharedCacheLeakRisk cacheKeyHasTenant cacheShared then 1 else 0) +
  (if crossTenantQueryRisk queryInternalID internalScoped then 1 else 0) +
  (if privilegeBoundaryCollapseRisk tenantAdminSuperAPI superAdminSeparateAuth then 1 else 0)

theorem fully_hardened_zero_multitenancy_risk :
    aggregateMultiTenancyIsolationRisk
      false true
      false false
      true false
      false true
      false true = 0 := by
  simp [aggregateMultiTenancyIsolationRisk, tenantIDFromRequestRisk, viewDataLeakageRisk,
        sharedCacheLeakRisk, crossTenantQueryRisk, privilegeBoundaryCollapseRisk]

theorem all_multitenancy_vectors_max_risk :
    aggregateMultiTenancyIsolationRisk
      true false
      true true
      false true
      true false
      true false = 5 := by
  simp [aggregateMultiTenancyIsolationRisk, tenantIDFromRequestRisk, viewDataLeakageRisk,
        sharedCacheLeakRisk, crossTenantQueryRisk, privilegeBoundaryCollapseRisk]

theorem multitenancy_risk_bounded
    (tenantIDFromReq tenantIDFromSession : Bool)
    (viewNoRLS viewCrossData : Bool)
    (cacheKeyHasTenant cacheShared : Bool)
    (queryInternalID internalScoped : Bool)
    (tenantAdminSuperAPI superAdminSeparateAuth : Bool) :
    aggregateMultiTenancyIsolationRisk
      tenantIDFromReq tenantIDFromSession
      viewNoRLS viewCrossData
      cacheKeyHasTenant cacheShared
      queryInternalID internalScoped
      tenantAdminSuperAPI superAdminSeparateAuth ≤ 5 := by
  simp [aggregateMultiTenancyIsolationRisk]
  split <;> split <;> split <;> split <;> split <;> decide

-- Scanner ROI: multi-tenancy isolation flaw detection prevents cross-tenant breach
def multiTenancyDetectionValueCents (crossTenantBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (crossTenantBreachCostCents : Int) - (scannerCostCents : Int)

theorem multitenancy_scanner_profitable (breach scan : Nat) (h : scan < breach) :
    0 < multiTenancyDetectionValueCents breach scan := by
  simp [multiTenancyDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem multitenancy_scanner_break_even (cost : Nat) :
    0 ≤ multiTenancyDetectionValueCents cost cost := by
  simp [multiTenancyDetectionValueCents]

-- Fleet ROI: multi-tenancy isolation scan across all SaaS tenants
def multiTenancyFleetROI (detectionValueCents : Nat) (saasTenants : Nat) : Nat :=
  detectionValueCents * saasTenants

theorem multitenancy_fleet_roi_monotone (v t1 t2 : Nat) (h : t1 ≤ t2) :
    multiTenancyFleetROI v t1 ≤ multiTenancyFleetROI v t2 := by
  simp [multiTenancyFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_multitenancy_fleet_roi (v t : Nat) (hv : 0 < v) (ht : 0 < t) :
    0 < multiTenancyFleetROI v t := by
  simp [multiTenancyFleetROI]
  exact Nat.mul_pos hv ht

-- Per-tenant breach cost scales with tenant count under shared-infrastructure failure
theorem multitenancy_breach_scales_with_tenants (breachPerTenant tenants : Nat)
    (hv : 0 < breachPerTenant) (ht : 0 < tenants) :
    0 < multiTenancyFleetROI breachPerTenant tenants := by
  simp [multiTenancyFleetROI]
  exact Nat.mul_pos hv ht

end MultiTenancyIsolationRisk
