import Init
-- DNSRebindingRisk.lean
-- Anti-thesis: Same-origin policy completely prevents external sites from
-- reading responses from internal services; DNS is just name resolution and
-- does not affect browser security boundaries.
-- Refutation: An attacker-controlled DNS record with a sub-second TTL can
-- rebind the hostname to an internal IP after the browser's SOP check,
-- turning the victim's browser into a pivot into the private network.
-- Zero IP-range validation and insufficient TTL enforcement are the root defects.

namespace Gnosis.Security.DNSRebindingRisk

-- TTL window: rebinding requires victim to re-resolve within the attack window
def rebindingWindowMs (ttlMs : Nat) (requestDelayMs : Nat) : Nat :=
  if requestDelayMs ≤ ttlMs then 0 else requestDelayMs - ttlMs

theorem low_ttl_opens_rebinding_window (delay ttl : Nat) (h : ttl < delay) :
    0 < rebindingWindowMs ttl delay := by { simp [rebindingWindowMs]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem high_ttl_closes_rebinding_window (delay ttl : Nat) (h : delay ≤ ttl) :
    rebindingWindowMs ttl delay = 0 := by { simp [rebindingWindowMs]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem rebinding_window_grows_as_ttl_shrinks (delay t1 t2 : Nat)
    (ht : t1 ≤ t2) (h : t2 < delay) :
    rebindingWindowMs t2 delay ≤ rebindingWindowMs t1 delay := by { simp [rebindingWindowMs]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- IP validation: private-range IP check blocks the rebind
def resolvedIPIsInternal (ip : Nat) (privateStart : Nat) (privateEnd : Nat) : Bool :=
  privateStart ≤ ip && ip ≤ privateEnd

def rebindingSucceeds (ipValidated : Bool) (inRebindingWindow : Bool) : Bool :=
  !ipValidated && inRebindingWindow

theorem rebinding_blocked_by_ip_validation (window : Bool) :
    rebindingSucceeds true window = false := by { simp [rebindingSucceeds]

theorem rebinding_blocked_outside_window (validated : Bool) :
    rebindingSucceeds validated false = false := by
  simp [rebindingSucceeds]
  cases validated <;> simp

theorem rebinding_succeeds_when_unvalidated_in_window :
    rebindingSucceeds false true = true := by
  simp [rebindingSucceeds]

-- Same-origin bypass: rebinding allows cross-origin reads
def crossOriginReadBlocked (sopEnforced : Bool) (rebindingSucceeded : Bool) : Bool :=
  sopEnforced && !rebindingSucceeded

theorem sop_enforced_no_rebind_blocks_read :
    crossOriginReadBlocked true false = true := by
  simp [crossOriginReadBlocked]

theorem sop_enforced_with_rebind_allows_read :
    crossOriginReadBlocked true true = false := by
  simp [crossOriginReadBlocked]

theorem sop_unenforced_allows_read (r : Bool) :
    crossOriginReadBlocked false r = false := by
  simp [crossOriginReadBlocked]

-- Blast radius: number of internal services reachable after rebinding
def internalServicesReachable (rebindingSucceeded : Bool) (serviceCount : Nat) : Nat :=
  if rebindingSucceeded then serviceCount else 0

theorem rebinding_opens_internal_access (n : Nat) (h : 0 < n) :
    0 < internalServicesReachable true n := by
  simp [internalServicesReachable]; exact h

theorem no_rebinding_no_internal_access (n : Nat) :
    internalServicesReachable false n = 0 := by
  simp [internalServicesReachable]

theorem more_services_more_blast (n1 n2 : Nat) (h : n1 ≤ n2) :
    internalServicesReachable true n1 ≤ internalServicesReachable true n2 := by
  simp [internalServicesReachable]; exact h

-- TTL enforcement: minimum TTL cap limits rebinding opportunity
def enforcedTTLMs (requestedTTL : Nat) (minTTL : Nat) : Nat :=
  max requestedTTL minTTL

theorem enforced_ttl_at_least_minimum (req minTTL : Nat) :
    minTTL ≤ enforcedTTLMs req minTTL := by
  simp [enforcedTTLMs]
  exact Nat.le_max_right req minTTL

theorem enforced_ttl_prevents_rebinding (delay minTTL : Nat) (h : delay ≤ minTTL) :
    rebindingWindowMs (enforcedTTLMs 0 minTTL) delay = 0 := by
  simp [rebindingWindowMs, enforcedTTLMs]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- DNS pinning: browser-level fix caches IP to resist rebind
def dnsPinningResistsRebind (pinned : Bool) (ttlExpiredAfterMs : Nat)
    (pinDurationMs : Nat) : Bool :=
  pinned && pinDurationMs > ttlExpiredAfterMs

theorem dns_pinning_active_during_pin (ttl pin : Nat) (h : ttl < pin) :
    dnsPinningResistsRebind true ttl pin = true := by { simp [dnsPinningResistsRebind]; exact h

theorem dns_pinning_expired_allows_rebind (ttl : Nat) (h : 0 < ttl) :
    dnsPinningResistsRebind true ttl 0 = false := by
  simp [dnsPinningResistsRebind]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem dns_pinning_disabled_no_protection (ttl pin : Nat) :
    dnsPinningResistsRebind false ttl pin = false := by { simp [dnsPinningResistsRebind]

-- Aggregate DNS rebinding risk score
def dnsRebindingTotalRisk (ttlMs : Nat) (delayMs : Nat) (ipValidated : Bool)
    (serviceCount : Nat) (pinDurationMs : Nat) : Nat :=
  let window := rebindingWindowMs ttlMs delayMs
  let rebindOccurs := !ipValidated && 0 < window
  internalServicesReachable rebindOccurs serviceCount

theorem dns_rebinding_risk_eliminated_by_ip_validation (ttl delay n pin : Nat) :
    dnsRebindingTotalRisk ttl delay true n pin = 0 := by
  simp [dnsRebindingTotalRisk, internalServicesReachable]

theorem dns_rebinding_risk_eliminated_by_high_ttl (delay n pin : Nat) :
    dnsRebindingTotalRisk delay delay false n pin = 0 := by
  simp [dnsRebindingTotalRisk, rebindingWindowMs, internalServicesReachable]

theorem dns_rebinding_risk_positive_low_ttl_no_validation (n : Nat) (hn : 0 < n) :
    0 < dnsRebindingTotalRisk 0 1 false n 0 := by
  simp [dnsRebindingTotalRisk, rebindingWindowMs, internalServicesReachable]; exact hn

-- Combined defence: IP validation AND enforced TTL closes all rebinding paths
theorem dns_rebinding_defence_in_depth (ttl delay n pin : Nat) (h : delay ≤ ttl) :
    dnsRebindingTotalRisk ttl delay true n pin = 0 ∧
    dnsRebindingTotalRisk ttl delay false n pin = 0 := by
  constructor
  · simp [dnsRebindingTotalRisk, internalServicesReachable]
  · simp [dnsRebindingTotalRisk, rebindingWindowMs, internalServicesReachable]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Services at risk is monotone in service count
theorem blast_radius_monotone (ttl delay n1 n2 : Nat) (iv : Bool)
    (hn : n1 ≤ n2) :
    dnsRebindingTotalRisk ttl delay iv n1 0 ≤ dnsRebindingTotalRisk ttl delay iv n2 0 := by
  simp only [dnsRebindingTotalRisk, internalServicesReachable]
  split_ifs <;> omega

end DNSRebindingRisk
