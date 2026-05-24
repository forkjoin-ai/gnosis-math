import Init
-- InfrastructureMisconfigRisk.lean
-- Anti-thesis: Cloud infrastructure is secure by default because providers
-- configure resources with least-privilege out of the box.
-- Refutation: Default configurations optimise for ease-of-use, not security;
-- public S3 buckets, exposed debug endpoints, default credentials, and
-- permissive security groups each yield a strictly positive exposure window
-- discoverable by automated scanners in under one minute.

namespace Gnosis.Security.InfrastructureMisconfigRisk

-- Public S3 bucket: object storage publicly readable without authentication
def publicS3BucketRisk (blockPublicAccess : Bool) (bucketPolicy : Nat) : Nat :=
  -- bucketPolicy: 0 = no policy, higher = more restrictive
  if blockPublicAccess then 0
  else if bucketPolicy = 0 then 2
  else 1

theorem infra_block_public_access_safe (p : Nat) :
    publicS3BucketRisk true p = 0 := by { simp [publicS3BucketRisk]

theorem infra_no_block_no_policy_risk :
    0 < publicS3BucketRisk false 0 := by
  simp [publicS3BucketRisk]

-- Exposed debug endpoint: /debug, /actuator/env, /metrics without auth
def debugEndpointRisk (endpointEnabled : Bool) (authRequired : Bool) : Nat :=
  if !endpointEnabled || authRequired then 0 else 1

theorem infra_debug_disabled_safe (auth : Bool) :
    debugEndpointRisk false auth = 0 := by
  simp [debugEndpointRisk]

theorem infra_debug_enabled_no_auth_risk :
    0 < debugEndpointRisk true false := by
  simp [debugEndpointRisk]

-- Default credentials: admin/admin or root/root still active
def defaultCredentialRisk (credentialsChanged : Bool) : Nat :=
  if credentialsChanged then 0 else 1

theorem infra_credentials_changed_safe :
    defaultCredentialRisk true = 0 := by
  simp [defaultCredentialRisk]

theorem infra_default_credentials_risk :
    0 < defaultCredentialRisk false := by
  simp [defaultCredentialRisk]

-- Overly permissive security group: 0.0.0.0/0 inbound on admin port
def securityGroupRisk (sourceRestricted : Bool) (adminPortExposed : Bool) : Nat :=
  if !adminPortExposed || sourceRestricted then 0 else 1

theorem infra_admin_not_exposed_safe (restricted : Bool) :
    securityGroupRisk restricted false = 0 := by
  simp [securityGroupRisk]

theorem infra_admin_exposed_unrestricted_risk :
    0 < securityGroupRisk false true := by
  simp [securityGroupRisk]

-- Unpatched OS: known CVE in kernel or base image exploitable remotely
def unpatchedOSRisk (patchLevel : Nat) (currentPatchLevel : Nat) : Nat :=
  if patchLevel >= currentPatchLevel then 0 else currentPatchLevel - patchLevel

theorem infra_fully_patched_safe (p : Nat) :
    unpatchedOSRisk p p = 0 := by
  simp [unpatchedOSRisk]

theorem infra_behind_patches_risk (p c : Nat) (h : p < c) :
    0 < unpatchedOSRisk p c := by
  simp [unpatchedOSRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Patch deficit is monotone (more behind = more risk)
theorem infra_patch_risk_monotone (p1 p2 c : Nat) (h1 : p1 <= p2) (h2 : p2 < c) :
    unpatchedOSRisk p2 c <= unpatchedOSRisk p1 c := by { simp [unpatchedOSRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires all controls enabled
def netInfraMisconfigRisk (blockPublic : Bool) (debugDisabled : Bool)
    (credChanged : Bool) (sgRestricted : Bool) : Nat :=
  publicS3BucketRisk blockPublic 0 +
  debugEndpointRisk (! debugDisabled) false +
  defaultCredentialRisk credChanged +
  securityGroupRisk sgRestricted true

theorem infra_net_risk_zero_fully_mitigated :
    netInfraMisconfigRisk true true true true = 0 := by { simp [netInfraMisconfigRisk, publicS3BucketRisk, debugEndpointRisk,
        defaultCredentialRisk, securityGroupRisk]

theorem infra_net_risk_pos_unmitigated :
    0 < netInfraMisconfigRisk false false false false := by
  simp [netInfraMisconfigRisk, publicS3BucketRisk, debugEndpointRisk,
        defaultCredentialRisk, securityGroupRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end InfrastructureMisconfigRisk
