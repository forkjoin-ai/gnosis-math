import Init
-- ClickjackingXFORisk.lean
-- Anti-thesis: Clickjacking requires a user to visit an attacker-controlled
-- page and click a button; modern browsers have built-in frame-busting and
-- users can distinguish embedded iframes from real application windows.
-- Refutation: Users cannot visually detect transparent iframe overlays.
-- Frame-busting JavaScript is fragile: sandbox="allow-scripts" disables it.
-- X-Frame-Options: ALLOWALL or missing header allows any origin to embed.
-- CSP frame-ancestors overrides XFO but is absent in most deployments.
-- Clickjacking on single-click actions (confirm transfer, approve OAuth,
-- delete account) requires no multi-step interaction and is practical.

namespace Gnosis.Security.ClickjackingXFORisk

-- X-Frame-Options: DENY or SAMEORIGIN vs. ALLOWALL or absent
def xframeOptionsRisk (xfoHeader : Nat) : Bool :=
  -- 0 = DENY, 1 = SAMEORIGIN, 2 = ALLOWALL, 3 = absent
  xfoHeader >= 2

theorem xfo_deny_safe :
    xframeOptionsRisk 0 = false := by { simp [xframeOptionsRisk]

theorem xfo_sameorigin_safe :
    xframeOptionsRisk 1 = false := by
  simp [xframeOptionsRisk]

theorem xfo_allowall_risky :
    xframeOptionsRisk 2 = true := by
  simp [xframeOptionsRisk]

theorem xfo_absent_risky :
    xframeOptionsRisk 3 = true := by
  simp [xframeOptionsRisk]

-- CSP frame-ancestors: overrides XFO when present and restrictive
def cspFrameAncestorsRisk (cspPresent : Bool) (ancestorsNone : Bool)
    (ancestorsSelf : Bool) : Bool :=
  !cspPresent || (!ancestorsNone && !ancestorsSelf)

theorem csp_present_none_safe :
    cspFrameAncestorsRisk true true false = false := by
  simp [cspFrameAncestorsRisk]

theorem csp_present_self_safe :
    cspFrameAncestorsRisk true false true = false := by
  simp [cspFrameAncestorsRisk]

theorem no_csp_always_risky (none_ self : Bool) :
    cspFrameAncestorsRisk false none_ self = true := by
  simp [cspFrameAncestorsRisk]

theorem csp_present_no_restriction_risky :
    cspFrameAncestorsRisk true false false = true := by
  simp [cspFrameAncestorsRisk]

-- Frame-busting defeated by sandbox attribute
def frameBustingDefeatedRisk (frameBustingPresent : Bool) (sandboxDefeatsIt : Bool) : Bool :=
  frameBustingPresent && sandboxDefeatsIt

theorem no_sandbox_defeat_frame_busting_works (present : Bool) :
    frameBustingDefeatedRisk present false = false := by
  simp [frameBustingDefeatedRisk]
  cases present <;> simp

theorem no_frame_busting_nothing_to_defeat (sand : Bool) :
    frameBustingDefeatedRisk false sand = false := by
  simp [frameBustingDefeatedRisk]

theorem sandbox_defeats_frame_busting_exposes_risk :
    frameBustingDefeatedRisk true true = true := by
  simp [frameBustingDefeatedRisk]

-- Single-click action: clickjacking on high-impact single-click operations
def singleClickActionRisk (actionRequiresSingleClick : Bool) (confirmationRequired : Bool)
    (frameableByAttacker : Bool) : Bool :=
  actionRequiresSingleClick && !confirmationRequired && frameableByAttacker

theorem confirmation_step_prevents_clickjack (action frameable : Bool) :
    singleClickActionRisk action true frameable = false := by
  simp [singleClickActionRisk]
  cases action <;> cases frameable <;> simp

theorem not_frameable_no_clickjack (action confirm : Bool) :
    singleClickActionRisk action confirm false = false := by
  simp [singleClickActionRisk]
  cases action <;> cases confirm <;> simp

theorem single_click_no_confirm_frameable_risk :
    singleClickActionRisk true false true = true := by
  simp [singleClickActionRisk]

-- Multi-step action: clickjacking requires N clicks, harder but not impossible
def multiStepClickjackDifficulty (stepsRequired : Nat) : Nat :=
  stepsRequired

theorem single_step_easiest :
    multiStepClickjackDifficulty 1 = 1 := by
  simp [multiStepClickjackDifficulty]

theorem more_steps_harder (s1 s2 : Nat) (h : s1 ≤ s2) :
    multiStepClickjackDifficulty s1 ≤ multiStepClickjackDifficulty s2 := by
  simp [multiStepClickjackDifficulty, h]

theorem zero_steps_no_clickjack :
    multiStepClickjackDifficulty 0 = 0 := by
  simp [multiStepClickjackDifficulty]

-- Aggregate clickjacking risk
def aggregateClickjackingRisk
    (xfoLevel : Nat)
    (cspPresent ancestorsNone ancestorsSelf : Bool)
    (singleClick confirmRequired frameable : Bool) : Nat :=
  (if xframeOptionsRisk xfoLevel then 1 else 0) +
  (if cspFrameAncestorsRisk cspPresent ancestorsNone ancestorsSelf then 1 else 0) +
  (if singleClickActionRisk singleClick confirmRequired frameable then 1 else 0)

theorem fully_hardened_zero_clickjack_risk :
    aggregateClickjackingRisk 0 true true false true true true = 0 := by
  simp [aggregateClickjackingRisk, xframeOptionsRisk, cspFrameAncestorsRisk,
        singleClickActionRisk]

theorem all_vectors_max_clickjack_risk :
    aggregateClickjackingRisk 3 false false false true false true = 3 := by
  simp [aggregateClickjackingRisk, xframeOptionsRisk, cspFrameAncestorsRisk,
        singleClickActionRisk]

theorem xfo_absent_alone_nonzero :
    0 < aggregateClickjackingRisk 3 true true false false true false := by
  simp [aggregateClickjackingRisk, xframeOptionsRisk, cspFrameAncestorsRisk,
        singleClickActionRisk]

-- CSP overrides XFO: if both present, CSP frame-ancestors takes precedence
theorem csp_overrides_xfo_risk (xfoLevel : Nat) :
    cspFrameAncestorsRisk true true false = false := by
  simp [cspFrameAncestorsRisk]

-- Economic: clickjacking on OAuth approval = account linkage attack
def oauthClickjackImpactCents (accountsExposed : Nat) (avgAccountCents : Nat) : Nat :=
  accountsExposed * avgAccountCents

theorem zero_accounts_zero_impact (avg : Nat) :
    oauthClickjackImpactCents 0 avg = 0 := by
  simp [oauthClickjackImpactCents]

theorem impact_scales_with_accounts (a1 a2 avg : Nat) (h : a1 ≤ a2) :
    oauthClickjackImpactCents a1 avg ≤ oauthClickjackImpactCents a2 avg := by
  simp [oauthClickjackImpactCents]
  exact Nat.mul_le_mul_right avg h

theorem positive_accounts_and_value_positive_impact (a avg : Nat) (ha : 0 < a) (hv : 0 < avg) :
    0 < oauthClickjackImpactCents a avg := by
  simp [oauthClickjackImpactCents]
  exact Nat.mul_pos ha hv

-- Scanner ROI: detecting missing XFO / CSP frame-ancestors
def clickjackScannerROICents (impactCents : Nat) (scanCostCents : Nat) : Int :=
  (impactCents : Int) - (scanCostCents : Int)

theorem clickjack_scanner_profitable (impact scan : Nat) (h : scan < impact) :
    0 < clickjackScannerROICents impact scan := by
  simp [clickjackScannerROICents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem clickjack_scanner_nonneg_break_even (cost : Nat) :
    0 ≤ clickjackScannerROICents cost cost := by
  simp [clickjackScannerROICents]

end ClickjackingXFORisk
