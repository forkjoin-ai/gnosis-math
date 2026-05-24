import Init
-- XMLEntityExpansionRisk.lean
-- Anti-thesis: XML entity expansion (billion laughs) is a well-known denial-of-service
-- vector that every mature XML parser mitigates by default; entity expansion limits
-- are built into libxml2, Expat, and the JDK's DocumentBuilderFactory, making
-- this a theoretical risk in modern deployments.
-- Refutation: Many parsers require explicit opt-in to enable entity limits
-- (FEATURE_SECURE_PROCESSING in Java is not the default in all contexts).
-- Quadratic blowup attacks use only two expansion levels and evade simple
-- depth-based counting. External DTD references bypass local entity limits
-- and enable SSRF via the parser's network fetching. Custom parsers and
-- streaming parsers often omit protection entirely. Billion laughs remains
-- a live DoS vector in microservices that accept XML payloads without gateway
-- pre-filtering.

namespace Gnosis.Security.XMLEntityExpansionRisk

-- Billion laughs: exponential entity expansion (e.g., 10^9 expansions from 10 levels)
def billionLaughsRisk (entityExpansionLimited : Bool) (maxExpansionDepth : Nat)
    (safeDepthThreshold : Nat) : Bool :=
  !entityExpansionLimited || (safeDepthThreshold < maxExpansionDepth)

theorem expansion_limited_within_threshold_safe (depth threshold : Nat)
    (h : depth ≤ threshold) :
    billionLaughsRisk true depth threshold = false := by { simp [billionLaughsRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem expansion_not_limited_always_risky (depth threshold : Nat) :
    billionLaughsRisk false depth threshold = true := by { simp [billionLaughsRisk]

theorem depth_exceeds_threshold_risky (depth threshold : Nat) (h : threshold < depth) :
    billionLaughsRisk true depth threshold = true := by
  simp [billionLaughsRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem depth_at_threshold_safe (n : Nat) :
    billionLaughsRisk true n n = false := by { simp [billionLaughsRisk]

-- Quadratic blowup: two-level expansion with large intermediate entity
-- expandedSize ≈ entityCount * entitySize (two levels → quadratic in input length)
def quadraticBlowupRisk (entityCountLimit : Nat) (entitySizeLimit : Nat)
    (safeExpansionBudget : Nat) : Bool :=
  safeExpansionBudget < entityCountLimit * entitySizeLimit

theorem within_expansion_budget_safe (count size budget : Nat)
    (h : count * size ≤ budget) :
    quadraticBlowupRisk count size budget = false := by
  simp [quadraticBlowupRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem exceeds_expansion_budget_risky (count size budget : Nat)
    (h : budget < count * size) :
    quadraticBlowupRisk count size budget = true := by { simp [quadraticBlowupRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem zero_entity_count_no_blowup (size budget : Nat) :
    quadraticBlowupRisk 0 size budget = false := by { simp [quadraticBlowupRisk]

theorem zero_entity_size_no_blowup (count budget : Nat) :
    quadraticBlowupRisk count 0 budget = false := by
  simp [quadraticBlowupRisk]

-- External entity (XXE variant via DTD): parser fetches external DTD from network
def externalEntityDTDRisk (externalDTDAllowed : Bool) (networkFetchEnabled : Bool)
    (egressFiltered : Bool) : Bool :=
  externalDTDAllowed && networkFetchEnabled && !egressFiltered

theorem external_dtd_disallowed_safe (network egress : Bool) :
    externalEntityDTDRisk false network egress = false := by
  simp [externalEntityDTDRisk]

theorem network_fetch_disabled_safe (dtd egress : Bool) :
    externalEntityDTDRisk dtd false egress = false := by
  simp [externalEntityDTDRisk]

theorem egress_filtered_dtd_risk_mitigated (dtd network : Bool) :
    externalEntityDTDRisk dtd network true = false := by
  simp [externalEntityDTDRisk]

theorem dtd_allowed_network_fetch_no_egress_risky :
    externalEntityDTDRisk true true false = true := by
  simp [externalEntityDTDRisk]

-- DTD processing: inline DOCTYPE with entity declarations
def dtdProcessingRisk (dtdProcessingEnabled : Bool) (inlineDocTypeAllowed : Bool) : Bool :=
  dtdProcessingEnabled && inlineDocTypeAllowed

theorem dtd_processing_disabled_safe (inline : Bool) :
    dtdProcessingRisk false inline = false := by
  simp [dtdProcessingRisk]

theorem inline_doctype_disallowed_safe (dtd : Bool) :
    dtdProcessingRisk dtd false = false := by
  simp [dtdProcessingRisk]

theorem both_enabled_risky :
    dtdProcessingRisk true true = true := by
  simp [dtdProcessingRisk]

-- Parser secure processing: FEATURE_SECURE_PROCESSING or equivalent enabled
def parserSecureProcessingRisk (secureProcessingEnabled : Bool)
    (customParserUsed : Bool) (customParserHardened : Bool) : Bool :=
  !secureProcessingEnabled && (customParserUsed && !customParserHardened || !customParserUsed)

theorem secure_processing_enabled_safe (custom hardened : Bool) :
    parserSecureProcessingRisk true custom hardened = false := by
  simp [parserSecureProcessingRisk]

theorem custom_hardened_parser_safe :
    parserSecureProcessingRisk false true true = false := by
  simp [parserSecureProcessingRisk]

theorem no_secure_no_custom_risky :
    parserSecureProcessingRisk false false false = true := by
  simp [parserSecureProcessingRisk]

theorem no_secure_custom_unhardened_risky :
    parserSecureProcessingRisk false true false = true := by
  simp [parserSecureProcessingRisk]

-- Expansion budget: total bytes after entity expansion must be bounded
def expansionBudgetRisk (rawPayloadBytes : Nat) (expansionFactor : Nat)
    (maxAllowedBytes : Nat) : Bool :=
  maxAllowedBytes < rawPayloadBytes * expansionFactor

theorem within_budget_safe (raw factor max : Nat) (h : raw * factor ≤ max) :
    expansionBudgetRisk raw factor max = false := by
  simp [expansionBudgetRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem exceeds_budget_risky (raw factor max : Nat) (h : max < raw * factor) :
    expansionBudgetRisk raw factor max = true := by { simp [expansionBudgetRisk]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem zero_expansion_factor_no_risk (raw max : Nat) :
    expansionBudgetRisk raw 0 max = false := by { simp [expansionBudgetRisk]

-- Aggregate XML entity expansion risk
def aggregateXMLEntityExpansionRisk
    (expansionLimited : Bool) (maxDepth safeDepth : Nat)
    (entityCount entitySize expansionBudget : Nat)
    (extDTD networkFetch egress : Bool)
    (dtpEnabled inline : Bool) : Nat :=
  (if billionLaughsRisk expansionLimited maxDepth safeDepth then 1 else 0) +
  (if quadraticBlowupRisk entityCount entitySize expansionBudget then 1 else 0) +
  (if externalEntityDTDRisk extDTD networkFetch egress then 1 else 0) +
  (if dtdProcessingRisk dtpEnabled inline then 1 else 0)

theorem fully_hardened_zero_xml_expansion :
    aggregateXMLEntityExpansionRisk true 5 10 100 100 1000000
      false false true false false = 0 := by
  simp [aggregateXMLEntityExpansionRisk, billionLaughsRisk, quadraticBlowupRisk,
        externalEntityDTDRisk, dtdProcessingRisk]

theorem all_xml_vectors_max_risk :
    aggregateXMLEntityExpansionRisk false 20 5 1000 1000 100
      true true false true true = 4 := by
  simp [aggregateXMLEntityExpansionRisk, billionLaughsRisk, quadraticBlowupRisk,
        externalEntityDTDRisk, dtdProcessingRisk]

-- Economic: XML entity expansion scanner value (DoS prevention)
def xmlExpansionDetectionValueCents (downtimeCostCents : Nat) (scannerCostCents : Nat) : Int :=
  (downtimeCostCents : Int) - (scannerCostCents : Int)

theorem xml_expansion_detection_profitable (downtime scan : Nat) (h : scan < downtime) :
    0 < xmlExpansionDetectionValueCents downtime scan := by
  simp [xmlExpansionDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem xml_expansion_break_even (cost : Nat) :
    0 ≤ xmlExpansionDetectionValueCents cost cost := by
  simp [xmlExpansionDetectionValueCents]

-- Fleet ROI: XML expansion detections across XML-consuming services
def xmlExpansionFleetROI (detectionValue : Nat) (xmlServices : Nat) : Nat :=
  detectionValue * xmlServices

theorem xml_expansion_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    xmlExpansionFleetROI v s1 ≤ xmlExpansionFleetROI v s2 := by
  simp [xmlExpansionFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_xml_expansion_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < xmlExpansionFleetROI v s := by
  simp [xmlExpansionFleetROI]
  exact Nat.mul_pos hv hs

end XMLEntityExpansionRisk
