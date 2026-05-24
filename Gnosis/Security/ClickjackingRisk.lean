import Init
-- ClickjackingRisk.lean
-- Anti-thesis: Serving pages without X-Frame-Options or CSP frame-ancestors
-- carries no clickjacking risk because modern browsers detect framing attacks.
-- Refutation: Without frame embedding controls, an attacker overlays an
-- invisible iframe over a trusted UI, harvesting clicks on privileged actions,
-- yielding a strictly positive vulnerability window.

namespace Gnosis.Security.ClickjackingRisk

-- Clickjacking: page can be embedded in attacker's iframe
def clickjackingRisk (hasSensitiveActions : Bool) (frameControlSet : Bool) : Nat :=
  if !hasSensitiveActions || frameControlSet then 0 else 1

-- Frame control header eliminates clickjacking
theorem clickjacking_frame_control_set_safe :
    clickjackingRisk true true = 0 := by
  simp [clickjackingRisk]

-- Missing frame control on page with sensitive actions is strictly vulnerable
theorem clickjacking_no_frame_control_risk :
    0 < clickjackingRisk true false := by
  simp [clickjackingRisk]

-- X-Frame-Options DENY vs SAMEORIGIN
def xFrameOptionsDenyRisk (crossOriginFraming : Bool) (denySet : Bool) : Nat :=
  if !crossOriginFraming || denySet then 0 else 1

theorem xfo_deny_set_safe :
    xFrameOptionsDenyRisk true true = 0 := by
  simp [xFrameOptionsDenyRisk]

theorem xfo_deny_missing_risk :
    0 < xFrameOptionsDenyRisk true false := by
  simp [xFrameOptionsDenyRisk]

-- CSP frame-ancestors: more granular than X-Frame-Options
def cspFrameAncestorsRisk (embeddable : Bool) (frameAncestorsSet : Bool) : Nat :=
  if !embeddable || frameAncestorsSet then 0 else 1

theorem csp_frame_ancestors_set_safe :
    cspFrameAncestorsRisk true true = 0 := by
  simp [cspFrameAncestorsRisk]

theorem csp_frame_ancestors_missing_risk :
    0 < cspFrameAncestorsRisk true false := by
  simp [cspFrameAncestorsRisk]

-- Frame-busting JS is insufficient: can be defeated by sandbox attribute
def frameBustingOnlyRisk (sandboxed : Bool) : Nat :=
  if sandboxed then 1 else 0

theorem frame_busting_bypassed_by_sandbox :
    0 < frameBustingOnlyRisk true := by
  simp [frameBustingOnlyRisk]

-- Double framing: intermediate trusted frame defeats single-frame detection
def doubleFramingRisk (singleLayerCheck : Bool) (deepInspection : Bool) : Nat :=
  if !singleLayerCheck || deepInspection then 0 else 1

theorem clickjacking_deep_inspection_safe :
    doubleFramingRisk true true = 0 := by
  simp [doubleFramingRisk]

theorem clickjacking_single_layer_only_risk :
    0 < doubleFramingRisk true false := by
  simp [doubleFramingRisk]

-- Net: zero-risk requires both X-Frame-Options AND CSP frame-ancestors
def netClickjackingRisk (sensitive : Bool) (xfoSet : Bool) (cspSet : Bool) : Nat :=
  clickjackingRisk sensitive xfoSet + cspFrameAncestorsRisk sensitive cspSet

theorem clickjacking_net_risk_zero_fully_mitigated :
    netClickjackingRisk true true true = 0 := by
  simp [netClickjackingRisk, clickjackingRisk, cspFrameAncestorsRisk]

theorem clickjacking_net_risk_pos_unmitigated :
    0 < netClickjackingRisk true false false := by
  simp [netClickjackingRisk, clickjackingRisk, cspFrameAncestorsRisk]

end ClickjackingRisk
