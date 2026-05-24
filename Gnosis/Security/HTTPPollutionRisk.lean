import Init
-- HTTPPollutionRisk.lean
-- Anti-thesis: HTTP parameter and prototype pollution are developer education
-- problems; frameworks sanitize inputs automatically, and server-side JavaScript
-- is not susceptible to prototype-chain manipulation from untrusted HTTP input.
-- Refutation: Prototype pollution in Node.js (via lodash merge, qs parse,
-- JSON.parse with __proto__ keys) has RCE primitives via gadget chains.
-- HTTP Parameter Pollution (HPP) causes WAFs and application logic to read
-- different parameter values, bypassing security controls. Header pollution
-- (duplicate headers, comma-folding) confuses proxy chains and enables
-- cache-poisoning, authorization bypass, and log injection.

namespace Gnosis.Security.HTTPPollutionRisk

-- Prototype pollution: __proto__ or constructor.prototype key in parsed input
def prototypePollutionRisk (inputSanitized : Bool) (protoKeyBlocked : Bool)
    (deepMergePresent : Bool) : Bool :=
  !inputSanitized && !protoKeyBlocked && deepMergePresent

theorem sanitized_input_no_proto_pollution (blocked deep : Bool) :
    prototypePollutionRisk true blocked deep = false := by { simp [prototypePollutionRisk]

theorem blocked_proto_key_no_pollution (sanitized deep : Bool) :
    prototypePollutionRisk sanitized true deep = false := by
  simp [prototypePollutionRisk]
  cases sanitized <;> simp

theorem no_deep_merge_no_pollution (sanitized blocked : Bool) :
    prototypePollutionRisk sanitized blocked false = false := by
  simp [prototypePollutionRisk]
  cases sanitized <;> cases blocked <;> simp

theorem all_conditions_proto_pollution_risk :
    prototypePollutionRisk false false true = true := by
  simp [prototypePollutionRisk]

-- Gadget chain depth: prototype pollution impact scales with gadget availability
def gadgetChainSeverity (protoProps : Nat) (gadgetsAvailable : Nat) : Nat :=
  protoProps * gadgetsAvailable

theorem no_polluted_props_no_gadget_chain (gadgets : Nat) :
    gadgetChainSeverity 0 gadgets = 0 := by
  simp [gadgetChainSeverity]

theorem gadget_severity_scales_with_props (p1 p2 g : Nat) (h : p1 ≤ p2) :
    gadgetChainSeverity p1 g ≤ gadgetChainSeverity p2 g := by
  simp [gadgetChainSeverity]
  exact Nat.mul_le_mul_right g h

theorem positive_props_and_gadgets_yields_severity (p g : Nat) (hp : 0 < p) (hg : 0 < g) :
    0 < gadgetChainSeverity p g := by
  simp [gadgetChainSeverity]
  exact Nat.mul_pos hp hg

-- HTTP Parameter Pollution: duplicate parameters allow WAF bypass
def hppWafBypassRisk (duplicateParamsAllowed : Bool) (wafReadsFirst : Bool)
    (appReadsLast : Bool) : Bool :=
  duplicateParamsAllowed && (wafReadsFirst != appReadsLast)

theorem no_duplicate_params_no_hpp (wf al : Bool) :
    hppWafBypassRisk false wf al = false := by
  simp [hppWafBypassRisk]

theorem consistent_reading_no_hpp_bypass (dup : Bool) (same : Bool) :
    hppWafBypassRisk dup same same = false := by
  simp [hppWafBypassRisk]

theorem hpp_waf_reads_first_app_reads_last_bypass :
    hppWafBypassRisk true true false = true := by
  simp [hppWafBypassRisk]

theorem hpp_waf_reads_last_app_reads_first_bypass :
    hppWafBypassRisk true false true = true := by
  simp [hppWafBypassRisk]

-- Header pollution: duplicate headers with different values confuse proxy chains
def headerPollutionRisk (duplicateHeadersAllowed : Bool) (proxyNormalizesHeaders : Bool) : Bool :=
  duplicateHeadersAllowed && !proxyNormalizesHeaders

theorem proxy_normalization_prevents_header_pollution (dup : Bool) :
    headerPollutionRisk dup true = false := by
  simp [headerPollutionRisk]
  cases dup <;> simp

theorem no_duplicate_headers_no_pollution (norm : Bool) :
    headerPollutionRisk false norm = false := by
  simp [headerPollutionRisk]

theorem duplicate_headers_without_normalization_polluted :
    headerPollutionRisk true false = true := by
  simp [headerPollutionRisk]

-- Cache key pollution: unkeyed headers included in cached response
def cachePollutionRisk (headerIncludedInResponse : Bool) (headerKeyed : Bool)
    (pollutionInjectable : Bool) : Bool :=
  headerIncludedInResponse && !headerKeyed && pollutionInjectable

theorem keyed_header_no_cache_pollution (inResp injectable : Bool) :
    cachePollutionRisk inResp true injectable = false := by
  simp [cachePollutionRisk]
  cases inResp <;> cases injectable <;> simp

theorem non_injectable_no_cache_pollution (inResp keyed : Bool) :
    cachePollutionRisk inResp keyed false = false := by
  simp [cachePollutionRisk]
  cases inResp <;> cases keyed <;> simp

theorem full_cache_pollution_conditions :
    cachePollutionRisk true false true = true := by
  simp [cachePollutionRisk]

-- Parameter override: attacker-controlled param shadows application param
def paramOverrideRisk (paramAllowlist : Bool) (lastValueWins : Bool)
    (attackerPrecedesApp : Bool) : Bool :=
  !paramAllowlist && lastValueWins && attackerPrecedesApp

theorem allowlist_prevents_param_override (lv ap : Bool) :
    paramOverrideRisk true lv ap = false := by
  simp [paramOverrideRisk]

theorem first_value_wins_no_override (allowlist ap : Bool) :
    paramOverrideRisk allowlist false ap = false := by
  simp [paramOverrideRisk]
  cases allowlist <;> simp

theorem attacker_before_app_with_last_wins_override :
    paramOverrideRisk false true true = true := by
  simp [paramOverrideRisk]

-- Aggregate pollution risk
def aggregatePollutionRisk
    (inputSan protoBlocked deepMerge : Bool)
    (dupParams wafFirst appLast : Bool)
    (dupHeaders proxyNorm : Bool) : Nat :=
  (if prototypePollutionRisk inputSan protoBlocked deepMerge then 1 else 0) +
  (if hppWafBypassRisk dupParams wafFirst appLast then 1 else 0) +
  (if headerPollutionRisk dupHeaders proxyNorm then 1 else 0)

theorem fully_hardened_zero_pollution_risk :
    aggregatePollutionRisk true true false false true true false true = 0 := by
  simp [aggregatePollutionRisk, prototypePollutionRisk, hppWafBypassRisk, headerPollutionRisk]

theorem all_vectors_max_pollution_risk :
    aggregatePollutionRisk false false true true true false true false = 3 := by
  simp [aggregatePollutionRisk, prototypePollutionRisk, hppWafBypassRisk, headerPollutionRisk]

theorem proto_pollution_alone_nonzero :
    0 < aggregatePollutionRisk false false true false true true false true := by
  simp [aggregatePollutionRisk, prototypePollutionRisk, hppWafBypassRisk, headerPollutionRisk]

-- Economic: scanner detection value for pollution bugs
def pollutionDetectionValueCents (breachCostCents : Nat) (scanCostCents : Nat) : Int :=
  (breachCostCents : Int) - (scanCostCents : Int)

theorem detection_profitable_when_breach_exceeds_scan (breach scan : Nat) (h : scan < breach) :
    0 < pollutionDetectionValueCents breach scan := by
  simp [pollutionDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem detection_nonneg_at_break_even (cost : Nat) :
    0 ≤ pollutionDetectionValueCents cost cost := by
  simp [pollutionDetectionValueCents]

-- Fleet ROI: detection value scales with instances scanned
def fleetPollutionROICents (valuePerInstance : Nat) (instances : Nat) : Nat :=
  valuePerInstance * instances

theorem fleet_roi_scales_with_instances (v i1 i2 : Nat) (h : i1 ≤ i2) :
    fleetPollutionROICents v i1 ≤ fleetPollutionROICents v i2 := by
  simp [fleetPollutionROICents]
  exact Nat.mul_le_mul_left v h

theorem positive_fleet_roi (v i : Nat) (hv : 0 < v) (hi : 0 < i) :
    0 < fleetPollutionROICents v i := by
  simp [fleetPollutionROICents]
  exact Nat.mul_pos hv hi

end HTTPPollutionRisk
