import Gnosis.PhilosophicalAllegories

namespace Gnosis
namespace GreekLogicCanon

/-!
# Greek Logic Canon

Finite Init-compatible canon/citation core.  The pre-ledger module attempted
to resolve many classical paradoxes through unavailable analytic APIs; this
restoration keeps the reusable substrate: canon entries, citation witnesses,
acyclic dependency ranks, and bridge morphisms into the allegory layer.
-/

inductive GreekThinker where
  | zeno
  | socrates
  | plato
  | aristotle
  | epicurus
deriving DecidableEq, Repr

inductive CanonTopic where
  | motion
  | inquiry
  | projection
  | predication
  | contingency
deriving DecidableEq, Repr

structure CanonEntry where
  thinker : GreekThinker
  topic : CanonTopic
  rank : Nat

namespace CanonEntry

def precedes (earlier later : CanonEntry) : Prop :=
  earlier.rank < later.rank

def compatibleTopic (left right : CanonEntry) : Prop :=
  left.topic = right.topic

theorem precedes_irrefl (entry : CanonEntry) :
    ¬ entry.precedes entry := by
  intro h
  exact Nat.lt_irrefl entry.rank h

theorem precedes_trans
    {a b c : CanonEntry}
    (hab : a.precedes b)
    (hbc : b.precedes c) :
    a.precedes c := by
  exact Nat.lt_trans hab hbc

theorem precedes_asymmetric
    {a b : CanonEntry}
    (hab : a.precedes b) :
    ¬ b.precedes a := by
  intro hba
  exact Nat.lt_asymm hab hba

end CanonEntry

structure CanonCitation where
  source : CanonEntry
  target : CanonEntry
  topicPreserved : source.compatibleTopic target
  rankIncreases : source.precedes target

namespace CanonCitation

theorem no_self_citation (citation : CanonCitation) :
    citation.source ≠ citation.target := by
  intro h
  have hRank : citation.source.rank = citation.target.rank :=
    congrArg CanonEntry.rank h
  have hContradiction :
      citation.target.rank < citation.target.rank := by
    simpa [CanonEntry.precedes, hRank] using citation.rankIncreases
  exact Nat.lt_irrefl citation.target.rank hContradiction

def totalRankSpan (citation : CanonCitation) : Nat :=
  citation.target.rank - citation.source.rank

theorem positive_rank_span (citation : CanonCitation) :
    0 < citation.totalRankSpan := by
  unfold totalRankSpan
  exact Nat.sub_pos_of_lt citation.rankIncreases

end CanonCitation

def zenoMotion : CanonEntry where
  thinker := .zeno
  topic := .motion
  rank := 1

def aristotleMotion : CanonEntry where
  thinker := .aristotle
  topic := .motion
  rank := 4

def socraticInquiry : CanonEntry where
  thinker := .socrates
  topic := .inquiry
  rank := 2

def platonicInquiry : CanonEntry where
  thinker := .plato
  topic := .inquiry
  rank := 3

def platonicProjection : CanonEntry where
  thinker := .plato
  topic := .projection
  rank := 3

def aristotlePredication : CanonEntry where
  thinker := .aristotle
  topic := .predication
  rank := 4

def epicureanContingency : CanonEntry where
  thinker := .epicurus
  topic := .contingency
  rank := 5

def zenoToAristotleMotion : CanonCitation where
  source := zenoMotion
  target := aristotleMotion
  topicPreserved := rfl
  rankIncreases := by
    unfold CanonEntry.precedes zenoMotion aristotleMotion
    decide

def socratesToPlatoInquiry : CanonCitation where
  source := socraticInquiry
  target := platonicInquiry
  topicPreserved := rfl
  rankIncreases := by
    unfold CanonEntry.precedes socraticInquiry platonicInquiry
    decide

theorem zeno_motion_span_positive :
    0 < zenoToAristotleMotion.totalRankSpan := by
  exact zenoToAristotleMotion.positive_rank_span

theorem socratic_inquiry_no_self_citation :
    socratesToPlatoInquiry.source ≠ socratesToPlatoInquiry.target := by
  exact socratesToPlatoInquiry.no_self_citation

def topicToAllegoryCarrier : CanonTopic -> PhilosophicalAllegories.AllegoryCarrier
  | .motion => .dividedLine
  | .inquiry => .socraticElenchus
  | .projection => .caveShadow
  | .predication => .shipIdentity
  | .contingency => .twoTruths

def citationToAllegoryMorphism
    (citation : CanonCitation) :
    PhilosophicalAllegories.AllegoryMorphism where
  source := topicToAllegoryCarrier citation.source.topic
  target := topicToAllegoryCarrier citation.target.topic
  bearing := citation.totalRankSpan + 1
  distortion := citation.totalRankSpan

theorem citation_morphism_positive_bearing
    (citation : CanonCitation) :
    0 < (citationToAllegoryMorphism citation).bearing := by
  unfold citationToAllegoryMorphism
  exact Nat.succ_pos citation.totalRankSpan

theorem citation_morphism_bounded_distortion
    (citation : CanonCitation) :
    (citationToAllegoryMorphism citation).distortion <
      (citationToAllegoryMorphism citation).bearing := by
  unfold citationToAllegoryMorphism
  exact Nat.lt_succ_self citation.totalRankSpan

theorem citation_morphism_positive_gain
    (citation : CanonCitation) :
    0 < (citationToAllegoryMorphism citation).informationGain := by
  exact
    (citationToAllegoryMorphism citation).positive_gain_when_distortion_bounded
      (citation_morphism_positive_bearing citation)
      (citation_morphism_bounded_distortion citation)

structure CanonCertificate where
  motionCitation : CanonCitation
  inquiryCitation : CanonCitation
  motionSpanPositive : 0 < motionCitation.totalRankSpan
  inquiryNoSelfCitation : inquiryCitation.source ≠ inquiryCitation.target

def finiteGreekCanonCertificate : CanonCertificate where
  motionCitation := zenoToAristotleMotion
  inquiryCitation := socratesToPlatoInquiry
  motionSpanPositive := zeno_motion_span_positive
  inquiryNoSelfCitation := socratic_inquiry_no_self_citation

theorem greek_logic_canon_restored_master :
    0 < finiteGreekCanonCertificate.motionCitation.totalRankSpan ∧
      finiteGreekCanonCertificate.inquiryCitation.source ≠
        finiteGreekCanonCertificate.inquiryCitation.target ∧
      0 < (citationToAllegoryMorphism zenoToAristotleMotion).informationGain ∧
      0 < (citationToAllegoryMorphism socratesToPlatoInquiry).informationGain := by
  exact
    ⟨finiteGreekCanonCertificate.motionSpanPositive,
      finiteGreekCanonCertificate.inquiryNoSelfCitation,
      citation_morphism_positive_gain zenoToAristotleMotion,
      citation_morphism_positive_gain socratesToPlatoInquiry⟩

end GreekLogicCanon
end Gnosis
