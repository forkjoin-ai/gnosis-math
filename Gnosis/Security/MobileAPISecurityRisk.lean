import Init
-- MobileAPISecurityRisk.lean
-- Anti-thesis: Mobile apps are harder to attack than web apps because the binary
-- is compiled, so API secrets and tokens are effectively hidden.
-- Refutation: Reverse engineering extracts hardcoded keys in minutes; missing
-- certificate pinning enables MitM on any network; insecure local storage leaks
-- tokens to any app with file-read permissions, each yielding positive risk.

namespace Gnosis.Security.MobileAPISecurityRisk

-- Hardcoded API key: embedded in binary, extractable by strings/disassembly
def hardcodedKeyRisk (keyEmbedded : Bool) : Nat :=
  if keyEmbedded then 1 else 0

theorem mobile_no_hardcoded_key_safe :
    hardcodedKeyRisk false = 0 := by { simp [hardcodedKeyRisk]

theorem mobile_hardcoded_key_risk :
    0 < hardcodedKeyRisk true := by
  simp [hardcodedKeyRisk]

-- Missing certificate pinning: MitM on untrusted network intercepts all traffic
def certPinningRisk (pinned : Bool) : Nat :=
  if pinned then 0 else 1

theorem mobile_cert_pinned_safe :
    certPinningRisk true = 0 := by
  simp [certPinningRisk]

theorem mobile_no_cert_pinning_risk :
    0 < certPinningRisk false := by
  simp [certPinningRisk]

-- Insecure local storage: tokens in SharedPreferences/NSUserDefaults readable by other apps
def insecureStorageRisk (encryptedAtRest : Bool) : Nat :=
  if encryptedAtRest then 0 else 1

theorem mobile_encrypted_storage_safe :
    insecureStorageRisk true = 0 := by
  simp [insecureStorageRisk]

theorem mobile_plain_storage_risk :
    0 < insecureStorageRisk false := by
  simp [insecureStorageRisk]

-- JWT without expiry: stolen token grants perpetual access
def jwtExpiryRisk (hasExpiry : Bool) (expirySeconds : Nat) (maxAllowedSecs : Nat) : Nat :=
  if !hasExpiry then 2
  else if expirySeconds > maxAllowedSecs then 1
  else 0

theorem mobile_jwt_with_short_expiry_safe (e m : Nat) (h : e ≤ m) :
    jwtExpiryRisk true e m = 0 := by
  simp [jwtExpiryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem mobile_jwt_no_expiry_risk (e m : Nat) :
    0 < jwtExpiryRisk false e m := by { simp [jwtExpiryRisk]

theorem mobile_jwt_long_expiry_risk (e m : Nat) (h : m < e) :
    0 < jwtExpiryRisk true e m := by
  simp [jwtExpiryRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Insufficient token entropy: short random token brute-forceable
def tokenEntropyRisk (entropyBits : Nat) (minBits : Nat) : Nat :=
  if entropyBits ≥ minBits then 0 else minBits - entropyBits

theorem mobile_sufficient_entropy_safe (e m : Nat) (h : e ≥ m) :
    tokenEntropyRisk e m = 0 := by { simp [tokenEntropyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem mobile_low_entropy_risk (e m : Nat) (h : e < m) :
    0 < tokenEntropyRisk e m := by { simp [tokenEntropyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Cleartext HTTP: traffic sniffable on local network
def cleartextHTTPRisk (usesTLS : Bool) : Nat :=
  if usesTLS then 0 else 1

theorem mobile_tls_safe :
    cleartextHTTPRisk true = 0 := by { simp [cleartextHTTPRisk]

theorem mobile_cleartext_risk :
    0 < cleartextHTTPRisk false := by
  simp [cleartextHTTPRisk]

-- Net: zero-risk requires all mobile API controls
def netMobileAPIRisk (keyEmbedded : Bool) (pinned : Bool) (encrypted : Bool)
    (hasExpiry : Bool) (expiry : Nat) (usesTLS : Bool) : Nat :=
  hardcodedKeyRisk keyEmbedded +
  certPinningRisk pinned +
  insecureStorageRisk encrypted +
  jwtExpiryRisk hasExpiry expiry 3600 +
  cleartextHTTPRisk usesTLS

theorem mobile_net_risk_zero_fully_mitigated :
    netMobileAPIRisk false true true true 1800 true = 0 := by
  simp [netMobileAPIRisk, hardcodedKeyRisk, certPinningRisk, insecureStorageRisk,
        jwtExpiryRisk, cleartextHTTPRisk]

theorem mobile_net_risk_pos_unmitigated :
    0 < netMobileAPIRisk true false false false 0 false := by
  simp [netMobileAPIRisk, hardcodedKeyRisk, certPinningRisk, insecureStorageRisk,
        jwtExpiryRisk, cleartextHTTPRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end MobileAPISecurityRisk
