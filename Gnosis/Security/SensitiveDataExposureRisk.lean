import Init
-- SensitiveDataExposureRisk.lean
-- Anti-thesis: Data on internal networks needs no encryption because
-- the network perimeter is trusted and external attackers cannot reach it.
-- Refutation: Lateral movement after any perimeter breach exposes unencrypted
-- internal traffic to full read access; the exposure window is strictly positive
-- whenever TLS is absent or encryption-at-rest is skipped, regardless of
-- network topology.

namespace Gnosis.Security.SensitiveDataExposureRisk

-- TLS absent: plaintext transmission enables passive interception
def tlsAbsentRisk (tlsEnabled : Bool) (dataClassification : Nat) : Nat :=
  if tlsEnabled then 0 else dataClassification + 1

theorem data_tls_enabled_safe (c : Nat) :
    tlsAbsentRisk true c = 0 := by { simp [tlsAbsentRisk]

theorem data_tls_absent_risk (c : Nat) :
    0 < tlsAbsentRisk false c := by
  simp [tlsAbsentRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- TLS downgrade: server accepts SSLv3 or TLS 1.0 via negotiation
def tlsDowngradeRisk (minTlsVersion : Nat) (requiredMinVersion : Nat) : Nat :=
  if minTlsVersion >= requiredMinVersion then 0 else requiredMinVersion - minTlsVersion

theorem data_tls_version_sufficient_safe (v r : Nat) (h : v >= r) :
    tlsDowngradeRisk v r = 0 := by { simp [tlsDowngradeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem data_tls_version_too_low_risk (v r : Nat) (h : v < r) :
    0 < tlsDowngradeRisk v r := by { simp [tlsDowngradeRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Encryption at rest: sensitive data stored unencrypted on disk
def encryptionAtRestRisk (encrypted : Bool) (dataClassification : Nat) : Nat :=
  if encrypted then 0 else dataClassification + 1

theorem data_encrypted_at_rest_safe (c : Nat) :
    encryptionAtRestRisk true c = 0 := by { simp [encryptionAtRestRisk]

theorem data_unencrypted_at_rest_risk (c : Nat) :
    0 < encryptionAtRestRisk false c := by
  simp [encryptionAtRestRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- PII over HTTP: personal data in GET params leaks via server logs and referrer
def piiInUrlRisk (method : Nat) (piiPresent : Bool) : Nat :=
  -- method: 0 = GET (log-visible), 1 = POST, etc.
  if !piiPresent then 0
  else if method = 0 then 2
  else 1

theorem data_no_pii_safe (m : Nat) :
    piiInUrlRisk m false = 0 := by { simp [piiInUrlRisk]

theorem data_pii_in_get_high_risk :
    piiInUrlRisk 0 true = 2 := by
  simp [piiInUrlRisk]

theorem data_pii_in_post_lower_risk (m : Nat) (h : m ≠ 0) :
    piiInUrlRisk m true = 1 := by
  simp [piiInUrlRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Key rotation: stale encryption keys increase blast radius of key compromise
def keyRotationRisk (keyAgeDays : Nat) (maxKeyAgeDays : Nat) : Nat :=
  if keyAgeDays <= maxKeyAgeDays then 0 else keyAgeDays - maxKeyAgeDays

theorem data_key_within_rotation_window_safe (a m : Nat) (h : a <= m) :
    keyRotationRisk a m = 0 := by { simp [keyRotationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem data_key_overdue_rotation_risk (a m : Nat) (h : m < a) :
    0 < keyRotationRisk a m := by { simp [keyRotationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Risk monotone in classification level (higher sensitivity = more exposure damage)
theorem data_tls_absent_risk_monotone (c1 c2 : Nat) (h : c1 <= c2) :
    tlsAbsentRisk false c1 <= tlsAbsentRisk false c2 := by { simp [tlsAbsentRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires TLS enabled, sufficient TLS version, encrypted at rest, fresh keys
def netDataExposureRisk (tlsEnabled : Bool) (tlsVer reqVer : Nat)
    (encrypted : Bool) (keyAge maxAge : Nat) : Nat :=
  tlsAbsentRisk tlsEnabled 0 + tlsDowngradeRisk tlsVer reqVer +
  encryptionAtRestRisk encrypted 0 + keyRotationRisk keyAge maxAge

theorem data_net_risk_zero_fully_mitigated (v r a m : Nat)
    (hv : v >= r) (ha : a <= m) :
    netDataExposureRisk true v r true a m = 0 := by { simp [netDataExposureRisk, tlsAbsentRisk, tlsDowngradeRisk,
        encryptionAtRestRisk, keyRotationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem data_net_risk_pos_unmitigated (v r : Nat) (h : v < r) :
    0 < netDataExposureRisk false v r false (r + 1) 0 := by { simp [netDataExposureRisk, tlsAbsentRisk, tlsDowngradeRisk,
        encryptionAtRestRisk, keyRotationRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end SensitiveDataExposureRisk
