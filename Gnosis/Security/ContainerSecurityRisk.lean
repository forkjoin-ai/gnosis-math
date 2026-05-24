import Init
-- ContainerSecurityRisk.lean
-- Anti-thesis: Containerisation provides strong isolation so container-internal
-- vulnerabilities cannot affect the host or other containers.
-- Refutation: Privileged containers, root UID, excess Linux capabilities, and
-- unscanned images each provide a strictly positive host-escape or lateral-
-- movement surface that automated scanners detect before deployment.

namespace Gnosis.Security.ContainerSecurityRisk

-- Running as root: UID 0 inside container maps to host root if namespace escapes
def containerRootRisk (runsAsRoot : Bool) : Nat :=
  if runsAsRoot then 1 else 0

theorem container_non_root_safe :
    containerRootRisk false = 0 := by { simp [containerRootRisk]

theorem container_root_uid_risk :
    0 < containerRootRisk true := by
  simp [containerRootRisk]

-- Privileged flag: --privileged grants full host device access
def privilegedContainerRisk (isPrivileged : Bool) : Nat :=
  if isPrivileged then 2 else 0

theorem container_unprivileged_safe :
    privilegedContainerRisk false = 0 := by
  simp [privilegedContainerRisk]

theorem container_privileged_risk :
    0 < privilegedContainerRisk true := by
  simp [privilegedContainerRisk]

-- Excess capabilities: CAP_SYS_ADMIN or CAP_NET_ADMIN enable kernel exploits
def excessCapabilityRisk (capCount : Nat) (maxAllowed : Nat) : Nat :=
  if capCount ≤ maxAllowed then 0 else capCount - maxAllowed

theorem container_caps_within_limit_safe (c m : Nat) (h : c ≤ m) :
    excessCapabilityRisk c m = 0 := by
  simp [excessCapabilityRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem container_excess_caps_risk (c m : Nat) (h : m < c) :
    0 < excessCapabilityRisk c m := by { simp [excessCapabilityRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem container_caps_risk_monotone (c1 c2 m : Nat) (h1 : c1 ≤ c2) (h2 : m < c1) :
    excessCapabilityRisk c1 m ≤ excessCapabilityRisk c2 m := by { simp [excessCapabilityRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Unscanned image: known CVEs in base image layers exploitable at runtime
def unscannedImageRisk (scanned : Bool) (knownCVEs : Nat) : Nat :=
  if scanned then 0 else knownCVEs + 1

theorem container_scanned_image_safe (n : Nat) :
    unscannedImageRisk true n = 0 := by { simp [unscannedImageRisk]

theorem container_unscanned_image_risk (n : Nat) :
    0 < unscannedImageRisk false n := by
  simp [unscannedImageRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Permissive network policy: no egress restriction enables data exfiltration
def networkPolicyRisk (egressRestricted : Bool) (ingressRestricted : Bool) : Nat :=
  (if egressRestricted then 0 else 1) + (if ingressRestricted then 0 else 1)

theorem container_full_network_restriction_safe :
    networkPolicyRisk true true = 0 := by { simp [networkPolicyRisk]

theorem container_no_egress_restriction_risk :
    0 < networkPolicyRisk false true := by
  simp [networkPolicyRisk]

theorem container_no_network_restriction_risk :
    0 < networkPolicyRisk false false := by
  simp [networkPolicyRisk]

-- Read-only root filesystem reduces post-exploit persistence
def writableRootfsRisk (readOnly : Bool) : Nat :=
  if readOnly then 0 else 1

theorem container_readonly_rootfs_safe :
    writableRootfsRisk true = 0 := by
  simp [writableRootfsRisk]

theorem container_writable_rootfs_risk :
    0 < writableRootfsRisk false := by
  simp [writableRootfsRisk]

-- Net: zero-risk requires non-root + unprivileged + scanned + restricted network
def netContainerRisk (runsAsRoot : Bool) (isPrivileged : Bool) (capCount : Nat)
    (scanned : Bool) (egressRestricted : Bool) : Nat :=
  containerRootRisk runsAsRoot +
  privilegedContainerRisk isPrivileged +
  excessCapabilityRisk capCount 0 +
  unscannedImageRisk scanned 0 +
  networkPolicyRisk egressRestricted true

theorem container_net_risk_zero_fully_mitigated :
    netContainerRisk false false 0 true true = 0 := by
  simp [netContainerRisk, containerRootRisk, privilegedContainerRisk,
        excessCapabilityRisk, unscannedImageRisk, networkPolicyRisk]

theorem container_net_risk_pos_unmitigated :
    0 < netContainerRisk true true 5 false false := by
  simp [netContainerRisk, containerRootRisk, privilegedContainerRisk,
        excessCapabilityRisk, unscannedImageRisk, networkPolicyRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end ContainerSecurityRisk
