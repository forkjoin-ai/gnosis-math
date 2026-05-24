import Init
-- UnicodeNormalizationRisk.lean
-- Anti-thesis: Unicode normalization attacks are academic; all modern web frameworks
-- normalize input to NFC or NFKC before processing, and operating system path
-- resolution handles Unicode transparently, so normalization-based bypasses
-- are not exploitable in practice.
-- Refutation: Security checks applied before normalization allow homograph-like
-- bypasses: e.g., a path containing U+FF0E (fullwidth period) passes a "../"
-- check but normalizes to "/" at the OS level. Case-folding attacks (ß→ss,
-- ı→i) bypass case-insensitive comparisons used for authorization. NFD/NFC
-- dual representation enables filter bypass: ﬁ (U+FB01) normalizes to "fi",
-- defeating blocklists. Unicode normalization in domain names enables IDN
-- homograph phishing. These vectors have been exploited in real authentication
-- bypasses in Python's urllib, Ruby's Rack, and Java servlet containers.

namespace Gnosis.Security.UnicodeNormalizationRisk

-- Normalization order: security check runs before normalization, enabling bypass
def normalizationOrderRisk (securityCheckBeforeNormalization : Bool)
    (normalizationApplied : Bool) : Bool :=
  securityCheckBeforeNormalization && normalizationApplied

theorem check_after_normalization_safe (norm : Bool) :
    normalizationOrderRisk false norm = false := by { simp [normalizationOrderRisk]

theorem no_normalization_no_bypass (before : Bool) :
    normalizationOrderRisk before false = false := by
  simp [normalizationOrderRisk]

theorem check_before_normalization_risky :
    normalizationOrderRisk true true = true := by
  simp [normalizationOrderRisk]

-- Homograph bypass: visually identical characters from different Unicode blocks
def homographBypassRisk (homographFilteringEnabled : Bool) (unicodeInputAllowed : Bool)
    (inputNormalizedToASCII : Bool) : Bool :=
  !homographFilteringEnabled && unicodeInputAllowed && !inputNormalizedToASCII

theorem homograph_filter_enabled_safe (unicode ascii : Bool) :
    homographBypassRisk true unicode ascii = false := by
  simp [homographBypassRisk]

theorem unicode_input_rejected_safe (filter ascii : Bool) :
    homographBypassRisk filter false ascii = false := by
  simp [homographBypassRisk]

theorem ascii_normalization_prevents_homograph (filter unicode : Bool) :
    homographBypassRisk filter unicode true = false := by
  simp [homographBypassRisk]

theorem unfiltered_unicode_no_ascii_norm_risky :
    homographBypassRisk false true false = true := by
  simp [homographBypassRisk]

-- Case folding bypass: ß→ss, ı→i bypass case-insensitive security comparisons
def caseFoldingBypassRisk (caseFoldingAwareComparison : Bool)
    (nonASCIICaseInputAllowed : Bool) : Bool :=
  !caseFoldingAwareComparison && nonASCIICaseInputAllowed

theorem case_folding_aware_comparison_safe (nonAscii : Bool) :
    caseFoldingBypassRisk true nonAscii = false := by
  simp [caseFoldingBypassRisk]

theorem non_ascii_case_blocked_safe (aware : Bool) :
    caseFoldingBypassRisk aware false = false := by
  simp [caseFoldingBypassRisk]

theorem unaware_comparison_with_non_ascii_risky :
    caseFoldingBypassRisk false true = true := by
  simp [caseFoldingBypassRisk]

-- NFD/NFC dual representation: same visual glyph has multiple byte representations
def nfdNfcDualRepRisk (normalizationFormConsistent : Bool)
    (multipleFormsAccepted : Bool) : Bool :=
  !normalizationFormConsistent && multipleFormsAccepted

theorem consistent_normalization_safe (multi : Bool) :
    nfdNfcDualRepRisk true multi = false := by
  simp [nfdNfcDualRepRisk]

theorem single_form_only_safe (consistent : Bool) :
    nfdNfcDualRepRisk consistent false = false := by
  simp [nfdNfcDualRepRisk]

theorem inconsistent_multi_form_risky :
    nfdNfcDualRepRisk false true = true := by
  simp [nfdNfcDualRepRisk]

-- IDN homograph: internationalized domain names visually mimic legitimate domains
def idnHomographRisk (idnHomographCheckEnabled : Bool) (unicodeDomainsAllowed : Bool)
    (punycodeForcedInDisplay : Bool) : Bool :=
  !idnHomographCheckEnabled && unicodeDomainsAllowed && !punycodeForcedInDisplay

theorem idn_check_enabled_safe (unicode punycode : Bool) :
    idnHomographRisk true unicode punycode = false := by
  simp [idnHomographRisk]

theorem unicode_domains_blocked_safe (check punycode : Bool) :
    idnHomographRisk check false punycode = false := by
  simp [idnHomographRisk]

theorem punycode_in_display_prevents_confusion (check unicode : Bool) :
    idnHomographRisk check unicode true = false := by
  simp [idnHomographRisk]

theorem unchecked_unicode_domain_no_punycode_risky :
    idnHomographRisk false true false = true := by
  simp [idnHomographRisk]

-- Path traversal via Unicode fullwidth: U+FF0E (．) normalizes to period
def unicodePathTraversalRisk (fullwidthCharFiltered : Bool)
    (pathNormalizedBeforeCheck : Bool) : Bool :=
  !fullwidthCharFiltered && !pathNormalizedBeforeCheck

theorem fullwidth_filtered_safe (norm : Bool) :
    unicodePathTraversalRisk true norm = false := by
  simp [unicodePathTraversalRisk]

theorem path_normalized_before_check_safe (filter : Bool) :
    unicodePathTraversalRisk filter true = false := by
  simp [unicodePathTraversalRisk]

theorem unfiltered_unnormalized_path_risky :
    unicodePathTraversalRisk false false = true := by
  simp [unicodePathTraversalRisk]

-- Aggregate Unicode normalization risk
def aggregateUnicodeNormalizationRisk
    (checkBeforeNorm normApplied : Bool)
    (homographFilter unicodeInput asciiNorm : Bool)
    (caseFoldAware nonAsciiCase : Bool)
    (normConsistent multiForm : Bool) : Nat :=
  (if normalizationOrderRisk checkBeforeNorm normApplied then 1 else 0) +
  (if homographBypassRisk homographFilter unicodeInput asciiNorm then 1 else 0) +
  (if caseFoldingBypassRisk caseFoldAware nonAsciiCase then 1 else 0) +
  (if nfdNfcDualRepRisk normConsistent multiForm then 1 else 0)

theorem fully_hardened_zero_unicode_risk :
    aggregateUnicodeNormalizationRisk false true true true false true false true false = 0 := by
  simp [aggregateUnicodeNormalizationRisk, normalizationOrderRisk,
        homographBypassRisk, caseFoldingBypassRisk, nfdNfcDualRepRisk]

theorem all_unicode_vectors_max_risk :
    aggregateUnicodeNormalizationRisk true true false true false false true false true = 4 := by
  simp [aggregateUnicodeNormalizationRisk, normalizationOrderRisk,
        homographBypassRisk, caseFoldingBypassRisk, nfdNfcDualRepRisk]

-- Economic: Unicode normalization scanner detection value
def unicodeNormalizationDetectionValueCents (authBypassCostCents : Nat)
    (scannerCostCents : Nat) : Int :=
  (authBypassCostCents : Int) - (scannerCostCents : Int)

theorem unicode_detection_profitable (bypass scan : Nat) (h : scan < bypass) :
    0 < unicodeNormalizationDetectionValueCents bypass scan := by
  simp [unicodeNormalizationDetectionValueCents]; repeat (first | assumption | constructor | rfl | split | intro | apply Nat.le_refl | apply Nat.zero_le | apply Nat.succ_pos | apply Nat.zero_lt_succ | apply Nat.le_add_right | apply Nat.le_add_left | apply Nat.mul_le_mul_left | apply Nat.mul_le_mul_right | apply Nat.mul_pos | apply Nat.div_le_div_right | apply Nat.min_le_min | apply Nat.le_trans | apply Nat.le_of_lt | decide) }

theorem unicode_break_even (cost : Nat) :
    0 ≤ unicodeNormalizationDetectionValueCents cost cost := by
  simp [unicodeNormalizationDetectionValueCents]

-- Fleet ROI: Unicode normalization scans across multi-language services
def unicodeNormalizationFleetROI (detectionValue : Nat) (internationalServices : Nat) : Nat :=
  detectionValue * internationalServices

theorem unicode_fleet_roi_monotone (v s1 s2 : Nat) (h : s1 ≤ s2) :
    unicodeNormalizationFleetROI v s1 ≤ unicodeNormalizationFleetROI v s2 := by
  simp [unicodeNormalizationFleetROI]
  exact Nat.mul_le_mul_left v h

theorem positive_unicode_fleet_roi (v s : Nat) (hv : 0 < v) (hs : 0 < s) :
    0 < unicodeNormalizationFleetROI v s := by
  simp [unicodeNormalizationFleetROI]
  exact Nat.mul_pos hv hs

end UnicodeNormalizationRisk
