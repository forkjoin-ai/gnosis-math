import Init
-- WebCacheDeceptionRisk.lean
-- Anti-thesis: web cache deception is theoretical; CDNs cache only static assets
-- by extension (.css, .js, .png), and authenticated dynamic responses are always
-- served with Cache-Control: no-store, making cache deception impossible in
-- properly configured environments.
-- Refutation: Path confusion (e.g., /account/profile.css) causes CDNs to cache
-- authenticated responses when the application ignores the extra path segment.
-- Vary headers are often stripped by intermediaries, collapsing per-user cache
-- keys. Purging cached user data is rarely atomic. Cache deception has been used
-- to steal session tokens, OAuth tokens, and PII from major SaaS providers.

namespace Gnosis.Security.WebCacheDeceptionRisk

-- Path confusion: CDN caches /api/profile/evil.css as static despite dynamic content
def pathConfusionCacheDeception (cdnCachesStaticExt : Bool) (appIgnoresPathSuffix : Bool)
    (cacheControlNoStore : Bool) : Bool :=
  cdnCachesStaticExt && appIgnoresPathSuffix && !cacheControlNoStore

theorem cache_control_no_store_prevents_deception (cdn app : Bool) :
    pathConfusionCacheDeception cdn app true = false := by { simp [pathConfusionCacheDeception]

theorem cdn_not_caching_static_prevents_deception (app noStore : Bool) :
    pathConfusionCacheDeception false app noStore = false := by
  simp [pathConfusionCacheDeception]

theorem app_validates_path_prevents_deception (cdn noStore : Bool) :
    pathConfusionCacheDeception cdn false noStore = false := by
  simp [pathConfusionCacheDeception]

theorem all_conditions_met_path_deception :
    pathConfusionCacheDeception true true false = true := by
  simp [pathConfusionCacheDeception]

-- Static extension triggers: .css/.js/.png suffix causes CDN to cache response
def staticExtensionTriggerRisk (fileExtCacheable : Bool) (varyHeaderRespected : Bool)
    (authorizationInVary : Bool) : Bool :=
  fileExtCacheable && (!varyHeaderRespected || !authorizationInVary)

theorem vary_header_with_auth_prevents_trigger (ext : Bool) :
    staticExtensionTriggerRisk ext true true = false := by
  simp [staticExtensionTriggerRisk]

theorem not_cacheable_ext_no_trigger (vary auth : Bool) :
    staticExtensionTriggerRisk false vary auth = false := by
  simp [staticExtensionTriggerRisk]

theorem cacheable_without_vary_risky (auth : Bool) :
    staticExtensionTriggerRisk true false auth = true := by
  simp [staticExtensionTriggerRisk]

theorem cacheable_vary_without_auth_risky :
    staticExtensionTriggerRisk true true false = true := by
  simp [staticExtensionTriggerRisk]

-- Vary header stripping: CDN intermediaries strip Vary headers collapsing cache keys
def varyHeaderStrippingRisk (varyHeaderPresent : Bool) (cdnStripsVary : Bool)
    (cacheKeyIncludesAuth : Bool) : Bool :=
  varyHeaderPresent && cdnStripsVary && !cacheKeyIncludesAuth

theorem no_vary_no_stripping_issue (strips auth : Bool) :
    varyHeaderStrippingRisk false strips auth = false := by
  simp [varyHeaderStrippingRisk]

theorem cdn_preserves_vary_no_collapse (present auth : Bool) :
    varyHeaderStrippingRisk present false auth = false := by
  simp [varyHeaderStrippingRisk]

theorem auth_in_cache_key_safe (present strips : Bool) :
    varyHeaderStrippingRisk present strips true = false := by
  simp [varyHeaderStrippingRisk]

theorem vary_stripped_no_auth_key_collapsed :
    varyHeaderStrippingRisk true true false = true := by
  simp [varyHeaderStrippingRisk]

-- Cache purging: stale authenticated data lingers if purge is not atomic/complete
def cachePurgingRisk (purgeMechanism : Bool) (purgeAtomic : Bool)
    (ttlExpired : Bool) : Bool :=
  !purgeMechanism || (!purgeAtomic && !ttlExpired)

theorem purge_mechanism_present_and_atomic_safe (ttl : Bool) :
    cachePurgingRisk true true ttl = false := by
  simp [cachePurgingRisk]

theorem no_purge_mechanism_always_risky (atomic ttl : Bool) :
    cachePurgingRisk false atomic ttl = true := by
  simp [cachePurgingRisk]

theorem ttl_expired_compensates_non_atomic (present : Bool) :
    cachePurgingRisk present false true = false := by
  simp [cachePurgingRisk]
  cases present <;> simp

theorem non_atomic_purge_active_ttl_risky :
    cachePurgingRisk true false false = true := by
  simp [cachePurgingRisk]

-- Aggregate web cache deception risk
def aggregateWebCacheDeceptionRisk
    (cdnCaches appIgnores noStore : Bool)
    (extCacheable varyRespected authInVary : Bool)
    (varyPresent cdnStrips authKey : Bool) : Nat :=
  (if pathConfusionCacheDeception cdnCaches appIgnores noStore then 1 else 0) +
  (if staticExtensionTriggerRisk extCacheable varyRespected authInVary then 1 else 0) +
  (if varyHeaderStrippingRisk varyPresent cdnStrips authKey then 1 else 0)

theorem fully_hardened_zero_cache_deception :
    aggregateWebCacheDeceptionRisk false false true true true true false false true = 0 := by
  simp [aggregateWebCacheDeceptionRisk, pathConfusionCacheDeception,
        staticExtensionTriggerRisk, varyHeaderStrippingRisk]

theorem all_vectors_max_cache_deception :
    aggregateWebCacheDeceptionRisk true true false true false false true true false = 3 := by
  simp [aggregateWebCacheDeceptionRisk, pathConfusionCacheDeception,
        staticExtensionTriggerRisk, varyHeaderStrippingRisk]

-- Economic: cache deception scanner detection value
def cacheDeceptionDetectionValueCents (breachCostCents : Nat) (scannerCostCents : Nat) : Int :=
  (breachCostCents : Int) - (scannerCostCents : Int)

theorem cache_deception_detection_profitable (breach scan : Nat) (h : scan < breach) :
    0 < cacheDeceptionDetectionValueCents breach scan := by
  simp [cacheDeceptionDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem cache_deception_break_even (cost : Nat) :
    0 ≤ cacheDeceptionDetectionValueCents cost cost := by
  simp [cacheDeceptionDetectionValueCents]

-- Fleet ROI: cache deception detections across CDN-backed services
def cacheDeceptionFleetROI (detectionValue : Nat) (cdnServices : Nat) : Nat :=
  detectionValue * cdnServices

theorem cache_deception_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    cacheDeceptionFleetROI v s1 ≤ cacheDeceptionFleetROI v s2 := by
  simp [cacheDeceptionFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_cache_deception_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < cacheDeceptionFleetROI v s := by
  simp [cacheDeceptionFleetROI]
  exact Nat.mul_pos hv hs

end WebCacheDeceptionRisk
