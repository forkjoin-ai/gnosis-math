import Init
-- HTTPSDowngradeRisk.lean
-- Anti-thesis: HTTPS downgrade attacks are historical artifacts from the SSL 2.0/3.0
-- era; modern TLS 1.3 deployments enforce forward secrecy and authenticated
-- handshakes, browsers enforce HSTS, and the POODLE/BEAST/CRIME attacks are
-- all patched in current TLS stacks, making downgrade a solved problem.
-- Refutation: HSTS must be preloaded for the first connection to be safe;
-- new clients or cleared caches are vulnerable to SSL-stripping on the first
-- request. Mixed-content downgrade allows an attacker with network access to
-- inject HTTP resources into an HTTPS page. TLS 1.0/1.1 cipher fallback is
-- still enabled in many load balancers for "compatibility". ALPN confusion
-- allows protocol negotiation manipulation. TLS cipher suite configuration
-- often retains weak export_-grade or RC4 ciphers for legacy support.

namespace Gnosis.Security.HTTPSDowngradeRisk

-- HSTS bypass: first connection without preload is vulnerable to SSL stripping
def hstsBypassRisk (hstsEnabled : Bool) (hstsPreloaded : Bool)
    (maxAgeSeconds : Nat) (minSafeMaxAgeSeconds : Nat) : Bool :=
  !hstsEnabled || (!hstsPreloaded && maxAgeSeconds < minSafeMaxAgeSeconds)

theorem hsts_preloaded_safe (maxAge minAge : Nat) :
    hstsBypassRisk true true maxAge minAge = false := by { simp [hstsBypassRisk]

theorem hsts_not_enabled_risky (preloaded : Bool) (maxAge minAge : Nat) :
    hstsBypassRisk false preloaded maxAge minAge = true := by
  simp [hstsBypassRisk]

theorem adequate_max_age_without_preload_safe (maxAge minAge : Nat) (h : minAge ≤ maxAge) :
    hstsBypassRisk true false maxAge minAge = false := by
  simp [hstsBypassRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem short_max_age_no_preload_risky (maxAge minAge : Nat) (h : maxAge < minAge) :
    hstsBypassRisk true false maxAge minAge = true := by { simp [hstsBypassRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- SSL stripping: network attacker intercepts HTTP redirect before HTTPS upgrade
def sslStrippingRisk (httpsRedirectEnabled : Bool) (hstsPresent : Bool)
    (networkPathTrusted : Bool) : Bool :=
  httpsRedirectEnabled && !hstsPresent && !networkPathTrusted

theorem hsts_present_prevents_stripping (redirect network : Bool) :
    sslStrippingRisk redirect true network = false := by { simp [sslStrippingRisk]

theorem trusted_network_prevents_stripping (redirect hsts : Bool) :
    sslStrippingRisk redirect hsts true = false := by
  simp [sslStrippingRisk]

theorem no_redirect_no_stripping_attack (hsts network : Bool) :
    sslStrippingRisk false hsts network = false := by
  simp [sslStrippingRisk]

theorem redirect_no_hsts_untrusted_network_risky :
    sslStrippingRisk true false false = true := by
  simp [sslStrippingRisk]

-- TLS version downgrade: server accepts TLS 1.0/1.1 enabling POODLE/BEAST variants
def tlsVersionDowngradeRisk (minimumTLSVersion : Nat) (safeTLSVersion : Nat) : Bool :=
  minimumTLSVersion < safeTLSVersion

theorem minimum_tls_at_or_above_safe (min safe : Nat) (h : safe ≤ min) :
    tlsVersionDowngradeRisk min safe = false := by
  simp [tlsVersionDowngradeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem minimum_tls_below_safe_risky (min safe : Nat) (h : min < safe) :
    tlsVersionDowngradeRisk min safe = true := by { simp [tlsVersionDowngradeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem tls_version_at_minimum_safe (n : Nat) :
    tlsVersionDowngradeRisk n n = false := by { simp [tlsVersionDowngradeRisk]

-- Weak cipher suite: server offers export_/RC4/CBC ciphers enabling downgrade attacks
def weakCipherSuiteRisk (exportCiphersEnabled : Bool) (rc4Enabled : Bool)
    (cbc3DESEnabled : Bool) : Bool :=
  exportCiphersEnabled || rc4Enabled || cbc3DESEnabled

theorem no_weak_ciphers_safe :
    weakCipherSuiteRisk false false false = false := by
  simp [weakCipherSuiteRisk]

theorem export_ciphers_enabled_risky (rc4 cbc : Bool) :
    weakCipherSuiteRisk true rc4 cbc = true := by
  simp [weakCipherSuiteRisk]

theorem rc4_enabled_risky (export_ cbc : Bool) :
    weakCipherSuiteRisk export_ true cbc = true := by
  simp [weakCipherSuiteRisk]

theorem cbc3des_enabled_risky (export_ rc4 : Bool) :
    weakCipherSuiteRisk export_ rc4 true = true := by
  simp [weakCipherSuiteRisk]

-- Mixed content downgrade: HTTP subresources in HTTPS page
def mixedContentRisk (mixedContentBlocked : Bool) (activeContentHTTP : Bool) : Bool :=
  !mixedContentBlocked && activeContentHTTP

theorem mixed_content_blocked_safe (active : Bool) :
    mixedContentRisk true active = false := by
  simp [mixedContentRisk]

theorem no_active_http_content_safe (blocked : Bool) :
    mixedContentRisk blocked false = false := by
  simp [mixedContentRisk]

theorem unblocked_active_http_content_risky :
    mixedContentRisk false true = true := by
  simp [mixedContentRisk]

-- Aggregate HTTPS downgrade risk
def aggregateHTTPSDowngradeRisk
    (hstsEnabled hstsPreloaded : Bool) (maxAge minAge : Nat)
    (minTLS safeTLS : Nat)
    (exportCiphers rc4 cbc3des : Bool)
    (mixedBlocked activeHTTP : Bool) : Nat :=
  (if hstsBypassRisk hstsEnabled hstsPreloaded maxAge minAge then 1 else 0) +
  (if tlsVersionDowngradeRisk minTLS safeTLS then 1 else 0) +
  (if weakCipherSuiteRisk exportCiphers rc4 cbc3des then 1 else 0) +
  (if mixedContentRisk mixedBlocked activeHTTP then 1 else 0)

theorem fully_hardened_zero_downgrade :
    aggregateHTTPSDowngradeRisk true true 31536000 31536000 13 12 false false false true false = 0 := by
  simp [aggregateHTTPSDowngradeRisk, hstsBypassRisk, tlsVersionDowngradeRisk,
        weakCipherSuiteRisk, mixedContentRisk]

theorem all_downgrade_vectors_max :
    aggregateHTTPSDowngradeRisk false false 0 31536000 10 12 true false false false true = 4 := by
  simp [aggregateHTTPSDowngradeRisk, hstsBypassRisk, tlsVersionDowngradeRisk,
        weakCipherSuiteRisk, mixedContentRisk]

-- Economic: HTTPS downgrade scanner detection value
def httpsDowngradeDetectionValueCents (mitmBreachCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (mitmBreachCostCents : Int) - (scannerCostCents : Int)

theorem https_downgrade_detection_profitable (breach scan : Nat) (h : scan < breach) :
    0 < httpsDowngradeDetectionValueCents breach scan := by
  simp [httpsDowngradeDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem https_downgrade_break_even (cost : Nat) :
    0 ≤ httpsDowngradeDetectionValueCents cost cost := by
  simp [httpsDowngradeDetectionValueCents]

-- Fleet ROI: HTTPS downgrade scan across all HTTPS-serving endpoints
def httpsDowngradeFleetROI (detectionValue : Nat) (httpsEndpoints : Nat) : Nat :=
  detectionValue * httpsEndpoints

theorem https_downgrade_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    httpsDowngradeFleetROI v s1 ≤ httpsDowngradeFleetROI v s2 := by
  simp [httpsDowngradeFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_https_downgrade_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < httpsDowngradeFleetROI v s := by
  simp [httpsDowngradeFleetROI]
  exact Nat.mul_pos hv hs

end HTTPSDowngradeRisk
