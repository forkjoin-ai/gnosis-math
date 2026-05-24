import Init
-- SupplyChainRisk.lean
-- Anti-thesis: Installing open-source dependencies from a package registry
-- is safe because the registry enforces code review before publishing.
-- Refutation: Typosquatting, dependency confusion, malicious maintainer
-- takeover, and unpinned version ranges each yield a strictly positive
-- injection window because registries do not audit package behaviour,
-- only publication identity.

namespace Gnosis.Security.SupplyChainRisk

-- Typosquatting: package name one character off from legitimate package
def typosquattingRisk (nameEditDistance : Nat) (packageVerified : Bool) : Nat :=
  if packageVerified then 0
  else if nameEditDistance <= 1 then 2
  else if nameEditDistance <= 3 then 1
  else 0

theorem supply_verified_package_safe (d : Nat) :
    typosquattingRisk d true = 0 := by { simp [typosquattingRisk]

theorem supply_off_by_one_unverified_risk :
    0 < typosquattingRisk 1 false := by
  simp [typosquattingRisk]

-- Unpinned version: semver range accepts future malicious minor/patch release
def unpinnedVersionRisk (versionPinned : Bool) (ecosystemSize : Nat) : Nat :=
  if versionPinned then 0 else ecosystemSize + 1

theorem supply_pinned_version_safe (e : Nat) :
    unpinnedVersionRisk true e = 0 := by
  simp [unpinnedVersionRisk]

theorem supply_unpinned_version_risk (e : Nat) :
    0 < unpinnedVersionRisk false e := by
  simp [unpinnedVersionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Dependency confusion: internal package name resolvable from public registry
def dependencyConfusionRisk (internalScopeEnforced : Bool)
    (registryPriority : Nat) : Nat :=
  -- registryPriority: 0 = internal first, higher = external preferred
  if internalScopeEnforced then 0
  else registryPriority + 1

theorem supply_internal_scope_safe (p : Nat) :
    dependencyConfusionRisk true p = 0 := by { simp [dependencyConfusionRisk]

theorem supply_no_scope_confusion_risk (p : Nat) :
    0 < dependencyConfusionRisk false p := by
  simp [dependencyConfusionRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Maintainer takeover: abandoned package acquired by malicious actor
def maintainerTakeoverRisk (packageActive : Bool) (downloadCount : Nat) : Nat :=
  if packageActive then 0 else downloadCount

theorem supply_active_package_safe (d : Nat) :
    maintainerTakeoverRisk true d = 0 := by { simp [maintainerTakeoverRisk]

theorem supply_abandoned_high_download_risk (d : Nat) (h : 0 < d) :
    0 < maintainerTakeoverRisk false d := by
  simp [maintainerTakeoverRisk]; exact h

-- Integrity check: absent hash verification allows MitM substitution
def integrityCheckRisk (hashVerified : Bool) : Nat :=
  if hashVerified then 0 else 1

theorem supply_hash_verified_safe :
    integrityCheckRisk true = 0 := by
  simp [integrityCheckRisk]

theorem supply_no_hash_check_risk :
    0 < integrityCheckRisk false := by
  simp [integrityCheckRisk]

-- Typosquatting risk non-increasing as edit distance grows (unverified)
theorem supply_typosquatting_decreases_with_distance (d1 d2 : Nat)
    (h : d1 <= d2) :
    typosquattingRisk d2 false <= typosquattingRisk d1 false := by
  simp [typosquattingRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: zero-risk requires verified packages, pinned versions, scoped_ registry, integrity
def netSupplyChainRisk (verified : Bool) (pinned : Bool)
    (scoped_ : Bool) (hashChecked : Bool) : Nat :=
  typosquattingRisk 0 verified +
  unpinnedVersionRisk pinned 0 +
  dependencyConfusionRisk scoped_ 0 +
  integrityCheckRisk hashChecked

theorem supply_net_risk_zero_fully_mitigated :
    netSupplyChainRisk true true true true = 0 := by { simp [netSupplyChainRisk, typosquattingRisk, unpinnedVersionRisk,
        dependencyConfusionRisk, integrityCheckRisk]

theorem supply_net_risk_pos_unmitigated :
    0 < netSupplyChainRisk false false false false := by
  simp [netSupplyChainRisk, typosquattingRisk, unpinnedVersionRisk,
        dependencyConfusionRisk, integrityCheckRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end SupplyChainRisk
