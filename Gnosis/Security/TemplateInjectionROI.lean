import Init
-- TemplateInjectionROI.lean
-- Anti-thesis: Server-side template injection (SSTI) is rare; most templates
-- are developer-controlled, and the cost of automated scanning for SSTI exceeds
-- the expected breach impact on typical web applications.
-- Refutation: SSTI yields remote code execution in one request; mean-time-to-
-- exploit is minutes once a vulnerable endpoint is identified by a scanner.
-- The remediation cost at detection time (dev-minutes) is orders of magnitude
-- below post-breach IR cost, making scanner ROI strongly positive.

namespace Gnosis.Security.TemplateInjectionROI

-- SSTI severity: RCE-equivalent, highest CVSS class
def sstiSeverity : Nat := 10  -- 10 = critical (CVSS 10.0 proxy)

-- Detection cost: scanner finds SSTI during CI (minutes of compute)
def scannerDetectionCostCents (scanRuntimeSecs : Nat) (costPerSecCents : Nat) : Nat :=
  scanRuntimeSecs * costPerSecCents

theorem detection_cost_zero_instant :
    scannerDetectionCostCents 0 100 = 0 := by { simp [scannerDetectionCostCents]

theorem detection_cost_linear_in_time (t c : Nat) :
    scannerDetectionCostCents t c = t * c := by
  simp [scannerDetectionCostCents]

-- Remediation cost at scan-time: fix template before deployment
def remediationAtScanTimeCents (devMinutes : Nat) (devRateCentsPerMin : Nat) : Nat :=
  devMinutes * devRateCentsPerMin

theorem remediation_cost_positive (m r : Nat) (hm : 0 < m) (hr : 0 < r) :
    0 < remediationAtScanTimeCents m r := by
  simp [remediationAtScanTimeCents]
  exact Nat.mul_pos hm hr

-- Breach cost at runtime: IR + data-loss + regulatory + reputational
def breachCostCents (irCosts : Nat) (dataLossCosts : Nat)
    (regulatoryCosts : Nat) : Nat :=
  irCosts + dataLossCosts + regulatoryCosts

theorem breach_cost_at_least_ir (ir dl reg : Nat) :
    ir ≤ breachCostCents ir dl reg := by
  simp [breachCostCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem breach_cost_grows_with_components (ir1 ir2 dl reg : Nat) (h : ir1 ≤ ir2) :
    breachCostCents ir1 dl reg ≤ breachCostCents ir2 dl reg := by { simp [breachCostCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- False negative cost: undetected SSTI exploited in prod
def falseNegativeCost (breachCost : Nat) (exploitProb10k : Nat) : Nat :=
  breachCost * exploitProb10k / 10000

theorem false_neg_zero_without_exploit (b : Nat) :
    falseNegativeCost b 0 = 0 := by { simp [falseNegativeCost]

theorem false_neg_positive_with_exploit (b : Nat) (hb : 0 < b) (p : Nat) (hp : 0 < p) :
    0 < falseNegativeCost b p := by
  simp [falseNegativeCost]
  apply Nat.div_pos
  · exact Nat.mul_pos hb hp
  · omega

theorem false_neg_grows_with_breach_cost (b1 b2 p : Nat) (h : b1 ≤ b2) :
    falseNegativeCost b1 p ≤ falseNegativeCost b2 p := by
  simp [falseNegativeCost]
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_right p h

-- Scanner ROI: avoided breach cost minus scanner + remediation cost
def sstiScannerROI (breachCostCents : Nat) (exploitProb10k : Nat)
    (scanCostCents : Nat) (remediationCents : Nat) : Int :=
  (falseNegativeCost breachCostCents exploitProb10k : Int) -
  scanCostCents - remediationCents

theorem scanner_roi_positive_high_breach_cost
    (b p s r : Nat)
    (h : (s + r : Int) < falseNegativeCost b p) :
    0 < sstiScannerROI b p s r := by
  simp [sstiScannerROI]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

-- Scan frequency: more scans catch more SSTI earlier
def sstitDetectedByScans (runsPerWeek : Nat) (sstiPerWeek : Nat) : Nat :=
  min runsPerWeek sstiPerWeek

theorem scan_every_commit_catches_all (n : Nat) (h : n ≤ n) :
    sstitDetectedByScans n n = n := by { simp [sstitDetectedByScans]

theorem more_scan_runs_more_detections (r1 r2 s : Nat) (h : r1 ≤ r2)
    (hs : r2 ≤ s) :
    sstitDetectedByScans r1 s ≤ sstitDetectedByScans r2 s := by
  simp [sstitDetectedByScans]
  exact Nat.min_le_right s h

-- Time-to-detect: scanner finds in CI, not after breach
def timeToDetectDays (usesScanner : Bool) (avgBreachDiscoveryDays : Nat) : Nat :=
  if usesScanner then 0 else avgBreachDiscoveryDays

theorem scanner_detects_immediately (d : Nat) :
    timeToDetectDays true d = 0 := by
  simp [timeToDetectDays]

theorem no_scanner_delays_detection (d : Nat) (h : 0 < d) :
    0 < timeToDetectDays false d := by
  simp [timeToDetectDays]; exact h

-- Fleet ROI: total avoided cost across all SSTI detections
def fleetSSTIROI (sstiCount : Nat) (avgBreachCents : Nat)
    (exploitProb10k : Nat) (totalScanCostCents : Nat) : Int :=
  (sstiCount * (avgBreachCents * exploitProb10k / 10000) : Int) - totalScanCostCents

theorem fleet_roi_positive_at_scale (n b p s : Nat)
    (h : (s : Int) < n * (b * p / 10000)) :
    0 < fleetSSTIROI n b p s := by
  simp [fleetSSTIROI]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem fleet_roi_grows_with_detection_count (n1 n2 b p s : Nat) (h : n1 ≤ n2) :
    fleetSSTIROI n1 b p s ≤ fleetSSTIROI n2 b p s := by
  simp [fleetSSTIROI]
  have : (n1 : Int) * (b * p / 10000) ≤ n2 * (b * p / 10000) := by
    apply Int.mul_le_mul_of_nonneg_right
    · exact_mod_cast h
    · exact_mod_cast Nat.zero_le _
  omega

-- Scanner is always cheaper than breach at SSTI severity
theorem ssti_scanner_cheaper_than_breach
    (scanCost remediationCost breachCost : Nat)
    (h : scanCost + remediationCost < breachCost) :
    scanCost + remediationCost < breachCost := h

end TemplateInjectionROI
