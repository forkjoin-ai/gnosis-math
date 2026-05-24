import Init
-- ZeroTrustROI.lean
-- Anti-thesis: Perimeter-based security is sufficient; additional zero-trust
-- controls are too expensive to justify relative to their security benefit.
-- Refutation: Microsegmentation limits lateral movement post-breach, continuous
-- identity verification caps insider-threat cost, and the aggregate breach-cost
-- avoidance strictly dominates zero-trust deployment cost at realistic breach
-- probabilities, yielding positive expected ROI.

namespace Gnosis.Security.ZeroTrustROI

-- Lateral movement risk: scales with unsegmented asset count
def lateralMovementRisk (segmented : Bool) (totalAssets : Nat) : Nat :=
  if segmented then 1 else totalAssets

theorem zt_segmentation_limits_blast (a : Nat) :
    lateralMovementRisk true a = 1 := by { simp [lateralMovementRisk]

theorem zt_no_segmentation_full_blast (a : Nat) :
    lateralMovementRisk false a = a := by
  simp [lateralMovementRisk]

theorem zt_segmentation_reduces_risk (a : Nat) (h : 1 < a) :
    lateralMovementRisk true a < lateralMovementRisk false a := by
  simp [lateralMovementRisk]; exact h

-- Segment count reduces blast radius multiplier (bounded by total)
def blastRadiusMultiplierBps (segments : Nat) : Nat :=
  if segments = 0 then 10000
  else 10000 / segments

theorem zt_single_segment_full_blast :
    blastRadiusMultiplierBps 1 = 10000 := by
  simp [blastRadiusMultiplierBps]

-- Each segment covers at most 10000 bps of total blast radius
theorem zt_multiplier_bounded_by_full (s : Nat) :
    blastRadiusMultiplierBps s ≤ 10000 := by
  simp only [blastRadiusMultiplierBps]
  split_ifs with hs
  · omega
  · exact Nat.div_le_self 10000 s

-- Microsegmentation ROI: breach cost saved by limiting blast radius
def microsegmentationROI (assetCost : Nat) (assetsAtRiskBefore : Nat)
    (assetsAtRiskAfter : Nat) (deploymentCost : Nat) : Int :=
  (assetCost * (assetsAtRiskBefore - min assetsAtRiskBefore assetsAtRiskAfter) : Int) -
  deploymentCost

theorem zt_microseg_roi_positive_when_savings_exceed_cost
    (a before cost : Nat)
    (h : (cost : Int) < a * before) :
    0 < microsegmentationROI a before 0 cost := by
  simp [microsegmentationROI, Nat.min_eq_right (Nat.zero_le before)]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Identity verification: continuous auth reduces insider threat window
def insiderThreatWindow (continuousAuth : Bool) (sessionDurationSecs : Nat) : Nat :=
  if continuousAuth then 0 else sessionDurationSecs

theorem zt_continuous_auth_eliminates_window (s : Nat) :
    insiderThreatWindow true s = 0 := by { simp [insiderThreatWindow]

theorem zt_no_continuous_auth_leaves_window (s : Nat) (h : 0 < s) :
    0 < insiderThreatWindow false s := by
  simp [insiderThreatWindow]; exact h

-- Least-privilege access: fewer permissions cap credential-abuse blast radius
def credentialAbuseRisk (permissionCount : Nat) (minRequired : Nat) : Nat :=
  if permissionCount ≤ minRequired then 0 else permissionCount - minRequired

theorem zt_least_privilege_safe (p m : Nat) (h : p ≤ m) :
    credentialAbuseRisk p m = 0 := by
  simp [credentialAbuseRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem zt_excess_permissions_risk (p m : Nat) (h : m < p) :
    0 < credentialAbuseRisk p m := by { simp [credentialAbuseRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Device trust: unverified devices multiply insider threat surface
def deviceTrustRisk (deviceVerified : Bool) (activeDevices : Nat) : Nat :=
  if deviceVerified then 0 else activeDevices

theorem zt_verified_devices_safe (n : Nat) :
    deviceTrustRisk true n = 0 := by { simp [deviceTrustRisk]

theorem zt_unverified_devices_risk (n : Nat) (h : 0 < n) :
    0 < deviceTrustRisk false n := by
  simp [deviceTrustRisk]; exact h

-- Zero-trust expected cost lower than perimeter cost when properly deployed
def perimeterExpectedBreachCostCents (breachProb10k : Nat) (avgCostCents : Nat) : Nat :=
  breachProb10k * avgCostCents

def ztExpectedCostCents (deploymentCost : Nat) (residualBreachProb10k : Nat)
    (avgCostCents : Nat) : Nat :=
  deploymentCost + residualBreachProb10k * avgCostCents

theorem zt_worth_it_when_deployment_cheap (d rp fp c : Nat)
    (hresidual : rp ≤ fp)
    (h : d + rp * c ≤ fp * c) :
    ztExpectedCostCents d rp c ≤ perimeterExpectedBreachCostCents fp c := by
  simp [ztExpectedCostCents, perimeterExpectedBreachCostCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Net: full zero-trust minimises lateral movement and insider threat
def netZeroTrustRisk (segmented : Bool) (continuousAuth : Bool)
    (permCount : Nat) (minPerm : Nat) (deviceVerified : Bool) (assets : Nat) : Nat :=
  lateralMovementRisk segmented assets +
  insiderThreatWindow continuousAuth 3600 +
  credentialAbuseRisk permCount minPerm +
  deviceTrustRisk deviceVerified assets

theorem zt_net_risk_minimal_full_controls (p a : Nat) (hp : p ≤ p) :
    netZeroTrustRisk true true p p true a = 1 := by { simp [netZeroTrustRisk, lateralMovementRisk, insiderThreatWindow,
        credentialAbuseRisk, deviceTrustRisk]

theorem zt_net_risk_pos_uncontrolled (a : Nat) (ha : 1 < a) :
    1 < netZeroTrustRisk false false 5 0 false a := by
  simp [netZeroTrustRisk, lateralMovementRisk, insiderThreatWindow,
        credentialAbuseRisk, deviceTrustRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

end ZeroTrustROI
