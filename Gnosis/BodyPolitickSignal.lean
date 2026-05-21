import Init
import Gnosis.SignalEnvelope
import Gnosis.DifferentialAggregateBoundary

namespace Gnosis
namespace BodyPolitickSignal

open Gnosis.SignalEnvelope
open Gnosis.DifferentialAggregateBoundary

inductive BodyPolitickSource where
  | publicAggregate
  | privateAggregate
  | mixedAggregate
  deriving Repr, DecidableEq

structure BodyPolitickSignal where
  envelope : SignalEnvelope
  participantCount : Nat
  releasedFields : Nat
  privacyBudget : Nat
  source : BodyPolitickSource
  claimsAuthority : Bool
  deriving Repr, DecidableEq

def aggregateRelease (s : BodyPolitickSignal) : AggregateRelease :=
  {
    participantCount := s.participantCount,
    releasedFields := s.releasedFields,
    privacyBudget := s.privacyBudget
  }

def valid (s : BodyPolitickSignal) : Prop :=
  SignalEnvelope.valid s.envelope ∧
    differentiallyAggregate (aggregateRelease s) ∧
    s.claimsAuthority = false

def isObservation (_s : BodyPolitickSignal) : Prop := True

def reconstructsPrivateMemberOrder (s : BodyPolitickSignal) : Prop :=
  reconstructsMemberOrder (aggregateRelease s)

structure ThothAdmission where
  signal : BodyPolitickSignal
  lineageChecked : Bool
  conjectureMarked : Bool
  failureAuditExposed : Bool
  deriving Repr, DecidableEq

def admissionValid (a : ThothAdmission) : Prop :=
  valid a.signal ∧ a.lineageChecked = true ∧ a.failureAuditExposed = true

theorem public_aggregate_estimate_bounded
    (s : BodyPolitickSignal)
    (h : valid s)
    (_hSource : s.source = BodyPolitickSource.publicAggregate) :
    s.envelope.estimate ≤ 100 :=
  SignalEnvelope.valid_estimate_bounded s.envelope h.left

theorem private_aggregate_estimate_bounded
    (s : BodyPolitickSignal)
    (h : valid s)
    (_hSource : s.source = BodyPolitickSource.privateAggregate) :
    s.envelope.estimate ≤ 100 :=
  SignalEnvelope.valid_estimate_bounded s.envelope h.left

theorem aggregate_privacy_budget_bounded
    (s : BodyPolitickSignal)
    (h : valid s) :
    s.privacyBudget ≤ 100 :=
  differential_aggregate_privacy_budget_bounded (aggregateRelease s) h.right.left

theorem private_aggregate_blocks_member_reconstruction
    (s : BodyPolitickSignal)
    (h : valid s)
    (_hSource : s.source = BodyPolitickSource.privateAggregate) :
    ¬ reconstructsPrivateMemberOrder s :=
  differential_aggregate_blocks_member_reconstruction (aggregateRelease s) h.right.left

theorem observation_not_authority
    (s : BodyPolitickSignal)
    (h : valid s) :
    s.claimsAuthority = false :=
  h.right.right

theorem body_politick_signal_is_observation
    (s : BodyPolitickSignal) :
    isObservation s := by
  trivial

theorem thoth_admission_preserves_non_authority
    (a : ThothAdmission)
    (h : admissionValid a) :
    a.signal.claimsAuthority = false :=
  observation_not_authority a.signal h.left

end BodyPolitickSignal
end Gnosis
