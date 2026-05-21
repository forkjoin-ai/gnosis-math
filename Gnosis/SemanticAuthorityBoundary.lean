namespace Gnosis
namespace SemanticAuthorityBoundary

/-!
# Semantic Authority Boundary

Shared UI already carries the practical base vocabulary:
- emotion validation is neuro-symbolic taxonomy membership;
- intent detection is confidence-scored behavior, not mind reading;
- speaker identity is thresholded enrollment/identification;
- diagnosis-like labels live in layer-5 mental-health state and remain
  hypotheses unless clinically attested;
- culture lives in layer-7 environment and is best handled as self-report or
  provisional context;
- authority delta measures communicative drift, not entitlement to truth.

This file gives those surfaces a finite authority boundary. A claim may be
observed, proposed, self-reported, externally validated, or clinically
attested. It becomes scanner-authoritative only under explicit authority
conditions and zero contradictions.
-/

inductive SharedUiEvidenceSurface where
  | emotionTaxonomyValidation
  | intentSignal
  | speakerIdentification
  | mentalHealthLayer
  | culturalEnvironmentLayer
  | authorityDelta
  deriving DecidableEq, Repr

inductive SemanticClaimKind where
  | affectLabel
  | speakerIdentity
  | speakerIntent
  | diagnosisHypothesis
  | culturalFrame
  | authorityDelta
  | semanticAuthority
  deriving DecidableEq, Repr

inductive SemanticAuthorityVerdict where
  | observationOnly
  | candidate
  | selfReported
  | externallyValidated
  | clinicallyAttested
  | authorityBlocked
  | semanticAuthorityGranted
  deriving DecidableEq, Repr

structure SemanticAuthorityClaim where
  kind : SemanticClaimKind
  confidenceMilli : Nat
  evidenceMass : Nat
  selfReported : Bool
  userConfirmed : Bool
  externallyValidated : Bool
  domainCredentialed : Bool
  contradictionCount : Nat
  deriving DecidableEq, Repr

def confidenceBounded (claim : SemanticAuthorityClaim) : Prop :=
  claim.confidenceMilli ≤ 1000

def hasContradiction (claim : SemanticAuthorityClaim) : Bool :=
  0 < claim.contradictionCount

def selfReportAccepted (claim : SemanticAuthorityClaim) : Bool :=
  claim.selfReported && claim.userConfirmed

def externallyAnchored (claim : SemanticAuthorityClaim) : Bool :=
  claim.externallyValidated && claim.contradictionCount == 0

def clinicallyAnchored (claim : SemanticAuthorityClaim) : Bool :=
  claim.domainCredentialed && claim.externallyValidated &&
    claim.contradictionCount == 0

def semanticAuthorityConditions (claim : SemanticAuthorityClaim) : Bool :=
  claim.selfReported &&
  claim.userConfirmed &&
  claim.externallyValidated &&
  claim.domainCredentialed &&
  claim.contradictionCount == 0

def semanticAuthorityVerdict
    (claim : SemanticAuthorityClaim) : SemanticAuthorityVerdict :=
  if hasContradiction claim then
    .authorityBlocked
  else
    match claim.kind with
    | .diagnosisHypothesis =>
        if clinicallyAnchored claim then .clinicallyAttested else .candidate
    | .culturalFrame =>
        if selfReportAccepted claim then .selfReported else .candidate
    | .speakerIntent =>
        if selfReportAccepted claim then .selfReported else .candidate
    | .speakerIdentity =>
        if externallyAnchored claim then .externallyValidated else .candidate
    | .semanticAuthority =>
        if semanticAuthorityConditions claim then
          .semanticAuthorityGranted
        else
          .authorityBlocked
    | .affectLabel =>
        if externallyAnchored claim then .externallyValidated else .observationOnly
    | .authorityDelta =>
        if selfReportAccepted claim then .selfReported else .candidate

def authorityGranted (claim : SemanticAuthorityClaim) : Bool :=
  semanticAuthorityVerdict claim = .semanticAuthorityGranted

structure SpeakerIntentBoundary where
  claim : SemanticAuthorityClaim
  utteranceEvidenceMass : Nat
  behavioralSignalMass : Nat
  deriving DecidableEq, Repr

structure DiagnosisBoundary where
  claim : SemanticAuthorityClaim
  symptomEvidenceMass : Nat
  clinicalAttestationMass : Nat
  deriving DecidableEq, Repr

structure CultureBoundary where
  claim : SemanticAuthorityClaim
  selfDeclaredMass : Nat
  observedContextMass : Nat
  deriving DecidableEq, Repr

structure SemanticAuthorityBoundaryReport where
  claims : List SemanticAuthorityClaim
  theoremLabel : String
  observationalOnly : Bool
  deriving DecidableEq, Repr

def claimNeedsObligation (claim : SemanticAuthorityClaim) : Bool :=
  match semanticAuthorityVerdict claim with
  | .candidate => true
  | .authorityBlocked => true
  | .observationOnly => true
  | _ => false

def boundaryObligationCount : List SemanticAuthorityClaim → Nat
  | [] => 0
  | claim :: rest =>
      (if claimNeedsObligation claim then 1 else 0) + boundaryObligationCount rest

def boundaryGrantedCount : List SemanticAuthorityClaim → Nat
  | [] => 0
  | claim :: rest =>
      (if authorityGranted claim then 1 else 0) + boundaryGrantedCount rest

def boundaryBlockedCount : List SemanticAuthorityClaim → Nat
  | [] => 0
  | claim :: rest =>
      (if semanticAuthorityVerdict claim = .authorityBlocked then 1 else 0) +
        boundaryBlockedCount rest

def buildBoundaryReport
    (claims : List SemanticAuthorityClaim) : SemanticAuthorityBoundaryReport :=
  { claims
    theoremLabel :=
      "Gnosis.SemanticAuthorityBoundary.no_unwitnessed_semantic_authority"
    observationalOnly := true }

def BoundaryReportNonAuthority
    (report : SemanticAuthorityBoundaryReport) : Prop :=
  report.observationalOnly = true

theorem boundary_report_non_authority
    (claims : List SemanticAuthorityClaim) :
    BoundaryReportNonAuthority (buildBoundaryReport claims) := by
  rfl

theorem speaker_intent_not_authority_without_confirmation
    (claim : SemanticAuthorityClaim)
    (hKind : claim.kind = .speakerIntent)
    (hNoConfirm : claim.userConfirmed = false) :
    semanticAuthorityVerdict claim ≠ .semanticAuthorityGranted := by
  cases claim with
  | mk kind confidenceMilli evidenceMass selfReported userConfirmed
      externallyValidated domainCredentialed contradictionCount =>
  cases hKind
  simp at hNoConfirm
  by_cases hContradiction : 0 < contradictionCount
  · simp [semanticAuthorityVerdict, hasContradiction, hContradiction]
  · simp [semanticAuthorityVerdict, hasContradiction, selfReportAccepted,
      hContradiction, hNoConfirm]

theorem diagnosis_not_clinically_attested_without_domain_credential
    (claim : SemanticAuthorityClaim)
    (hKind : claim.kind = .diagnosisHypothesis)
    (hNoCredential : claim.domainCredentialed = false) :
    semanticAuthorityVerdict claim ≠ .clinicallyAttested := by
  cases claim with
  | mk kind confidenceMilli evidenceMass selfReported userConfirmed
      externallyValidated domainCredentialed contradictionCount =>
  cases hKind
  simp at hNoCredential
  by_cases hContradiction : 0 < contradictionCount
  · simp [semanticAuthorityVerdict, hasContradiction, hContradiction]
  · simp [semanticAuthorityVerdict, hasContradiction, clinicallyAnchored,
      hContradiction, hNoCredential]

theorem cultural_observation_without_self_report_is_candidate_not_self_report
    (claim : SemanticAuthorityClaim)
    (hKind : claim.kind = .culturalFrame)
    (hNoSelfReport : claim.selfReported = false) :
    semanticAuthorityVerdict claim ≠ .selfReported := by
  cases claim with
  | mk kind confidenceMilli evidenceMass selfReported userConfirmed
      externallyValidated domainCredentialed contradictionCount =>
  cases hKind
  simp at hNoSelfReport
  by_cases hContradiction : 0 < contradictionCount
  · simp [semanticAuthorityVerdict, hasContradiction, hContradiction]
  · simp [semanticAuthorityVerdict, hasContradiction, selfReportAccepted,
      hContradiction, hNoSelfReport]

theorem semantic_authority_requires_all_conditions
    (claim : SemanticAuthorityClaim)
    (h : authorityGranted claim = true) :
    semanticAuthorityVerdict claim = .semanticAuthorityGranted := by
  unfold authorityGranted at h
  exact of_decide_eq_true h

theorem semantic_authority_blocked_by_contradiction
    (claim : SemanticAuthorityClaim)
    (hContradiction : hasContradiction claim = true) :
    semanticAuthorityVerdict claim = .authorityBlocked := by
  unfold semanticAuthorityVerdict
  simp [hContradiction]

def witnessIntentClaim : SemanticAuthorityClaim :=
  { kind := .speakerIntent
    confidenceMilli := 730
    evidenceMass := 2
    selfReported := false
    userConfirmed := false
    externallyValidated := false
    domainCredentialed := false
    contradictionCount := 0 }

def witnessDiagnosisClaim : SemanticAuthorityClaim :=
  { kind := .diagnosisHypothesis
    confidenceMilli := 640
    evidenceMass := 3
    selfReported := false
    userConfirmed := false
    externallyValidated := false
    domainCredentialed := false
    contradictionCount := 0 }

def witnessCultureClaim : SemanticAuthorityClaim :=
  { kind := .culturalFrame
    confidenceMilli := 500
    evidenceMass := 1
    selfReported := false
    userConfirmed := false
    externallyValidated := false
    domainCredentialed := false
    contradictionCount := 0 }

def witnessSemanticAuthorityClaim : SemanticAuthorityClaim :=
  { kind := .semanticAuthority
    confidenceMilli := 900
    evidenceMass := 4
    selfReported := true
    userConfirmed := true
    externallyValidated := true
    domainCredentialed := true
    contradictionCount := 0 }

def witnessBoundaryReport : SemanticAuthorityBoundaryReport :=
  buildBoundaryReport
    [ witnessIntentClaim
    , witnessDiagnosisClaim
    , witnessCultureClaim
    , witnessSemanticAuthorityClaim ]

theorem witness_intent_is_candidate :
    semanticAuthorityVerdict witnessIntentClaim = .candidate := by
  rfl

theorem witness_diagnosis_is_candidate :
    semanticAuthorityVerdict witnessDiagnosisClaim = .candidate := by
  rfl

theorem witness_culture_is_candidate :
    semanticAuthorityVerdict witnessCultureClaim = .candidate := by
  rfl

theorem witness_semantic_authority_granted :
    semanticAuthorityVerdict witnessSemanticAuthorityClaim =
      .semanticAuthorityGranted := by
  rfl

theorem witness_boundary_obligation_count :
    boundaryObligationCount witnessBoundaryReport.claims = 3 := by
  rfl

theorem witness_boundary_granted_count :
    boundaryGrantedCount witnessBoundaryReport.claims = 1 := by
  rfl

theorem witness_boundary_non_authority :
    BoundaryReportNonAuthority witnessBoundaryReport := by
  rfl

end SemanticAuthorityBoundary
end Gnosis
