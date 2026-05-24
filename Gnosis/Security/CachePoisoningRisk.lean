import Init
-- CachePoisoningRisk.lean
-- Anti-thesis: CDN and reverse-proxy caches are safe because they only
-- cache responses that are explicitly marked as cacheable by the origin.
-- Refutation: Unkeyed headers, host header injection, and request smuggling
-- can cause a poisoned response to be stored and served to all subsequent
-- requesters, yielding a strictly positive blast radius proportional to
-- cache hit rate.

namespace Gnosis.Security.CachePoisoningRisk

-- Unkeyed header injection: X-Forwarded-Host reflected in response and cached
def unkeyedHeaderRisk (headerIncludedInCacheKey : Bool) (headerReflected : Bool) : Nat :=
  if headerIncludedInCacheKey || !headerReflected then 0 else 1

theorem cache_keyed_header_safe (reflected : Bool) :
    unkeyedHeaderRisk true reflected = 0 := by { simp [unkeyedHeaderRisk]

theorem cache_unkeyed_reflected_risk :
    0 < unkeyedHeaderRisk false true := by
  simp [unkeyedHeaderRisk]

-- Host header injection: poisoned cache entry served to all users on vhost
def hostHeaderPoisonRisk (hostValidated : Bool) (cacheEnabled : Bool) : Nat :=
  if hostValidated || !cacheEnabled then 0 else 1

theorem cache_host_validated_safe (cached : Bool) :
    hostHeaderPoisonRisk true cached = 0 := by
  simp [hostHeaderPoisonRisk]

theorem cache_host_unvalidated_cached_risk :
    0 < hostHeaderPoisonRisk false true := by
  simp [hostHeaderPoisonRisk]

-- Cache deception: attacker tricks victim into caching their authenticated response
def cacheDeceptionRisk (pathNormalized : Bool) (varyOnCookie : Bool) : Nat :=
  if pathNormalized && varyOnCookie then 0
  else if pathNormalized || varyOnCookie then 1
  else 2

theorem cache_path_normalized_and_vary_safe :
    cacheDeceptionRisk true true = 0 := by
  simp [cacheDeceptionRisk]

theorem cache_neither_control_max_risk :
    cacheDeceptionRisk false false = 2 := by
  simp [cacheDeceptionRisk]

-- Request smuggling + cache: desync causes poisoned response cached for next request
def requestSmugglingCacheRisk (frontBackSyncEnabled : Bool) : Nat :=
  if frontBackSyncEnabled then 0 else 1

theorem cache_sync_enabled_safe :
    requestSmugglingCacheRisk true = 0 := by
  simp [requestSmugglingCacheRisk]

theorem cache_desync_risk :
    0 < requestSmugglingCacheRisk false := by
  simp [requestSmugglingCacheRisk]

-- Blast radius: poisoned entry served to n users multiplies impact
def poisonBlastRadius (poisoned : Bool) (cacheHitsPerSec : Nat) : Nat :=
  if poisoned then cacheHitsPerSec else 0

theorem cache_not_poisoned_no_blast (n : Nat) :
    poisonBlastRadius false n = 0 := by
  simp [poisonBlastRadius]

theorem cache_poisoned_blast_grows (n : Nat) (h : 0 < n) :
    0 < poisonBlastRadius true n := by
  simp [poisonBlastRadius]; exact h

-- Blast radius monotone in cache hit rate
theorem cache_blast_monotone (n1 n2 : Nat) (h : n1 <= n2) :
    poisonBlastRadius true n1 <= poisonBlastRadius true n2 := by
  simp [poisonBlastRadius]; exact h

-- Net: zero-risk requires keyed headers, validated host, path norm, Vary cookie
def netCachePoisonRisk (keyed : Bool) (hostValidated : Bool)
    (pathNorm : Bool) (varyCookie : Bool) : Nat :=
  unkeyedHeaderRisk keyed true +
  hostHeaderPoisonRisk hostValidated true +
  cacheDeceptionRisk pathNorm varyCookie

theorem cache_net_risk_zero_fully_mitigated :
    netCachePoisonRisk true true true true = 0 := by
  simp [netCachePoisonRisk, unkeyedHeaderRisk, hostHeaderPoisonRisk, cacheDeceptionRisk]

theorem cache_net_risk_pos_unmitigated :
    0 < netCachePoisonRisk false false false false := by
  simp [netCachePoisonRisk, unkeyedHeaderRisk, hostHeaderPoisonRisk, cacheDeceptionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end CachePoisoningRisk
