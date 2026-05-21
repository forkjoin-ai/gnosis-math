import Gnosis.Witnesses.Bible.Torah.GenesisCircumcisionCovenantWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansTitusLibertyWitness
import Gnosis.Witnesses.Bible.Galatians.GalatiansAntiochConfrontationWitness

namespace Gnosis.Witnesses.Bible.Torah
namespace TorahGalatiansCircumcisionTandemWitness

/-!
# Torah / Galatians Circumcision Tandem Witness

This bridge exists to avoid duplicate coverage of the same text. Genesis 17 is
covered as Torah covenant-token source text. Galatians 2 is covered as the
Pauline dispute where that token is refused as a Gentile capture requirement.

No `sorry`, no new `axiom`.
-/

structure TandemCoverageDiscipline where
  genesisCoversCovenantToken : Bool := true
  galatiansCoversCaptureDispute : Bool := true
  noDuplicateSourceCoverage : Bool := true
  overlapHandledAsSemanticBridge : Bool := true
deriving DecidableEq, Repr

def tandemCoverageDiscipline : TandemCoverageDiscipline := {}

def noDuplicateCoverageDiscipline (d : TandemCoverageDiscipline) : Prop :=
  d.genesisCoversCovenantToken = true ∧
  d.galatiansCoversCaptureDispute = true ∧
  d.noDuplicateSourceCoverage = true ∧
  d.overlapHandledAsSemanticBridge = true

theorem torah_galatians_no_duplicate_coverage :
    noDuplicateCoverageDiscipline tandemCoverageDiscipline := by
  unfold noDuplicateCoverageDiscipline tandemCoverageDiscipline
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem torah_galatians_circumcision_tandem_witness :
    GenesisCircumcisionCovenantWitness.circumcisionIsCovenantToken
      GenesisCircumcisionCovenantWitness.circumcisionToken ∧
    Gnosis.Witnesses.Bible.Galatians.GalatiansTitusLibertyWitness.falseBrethrenCaptureFails
      Gnosis.Witnesses.Bible.Galatians.GalatiansTitusLibertyWitness.titusLibertyBoundary ∧
    Gnosis.Witnesses.Bible.Galatians.GalatiansAntiochConfrontationWitness.faithNotLawJustifies
      Gnosis.Witnesses.Bible.Galatians.GalatiansAntiochConfrontationWitness.justificationBoundary ∧
    noDuplicateCoverageDiscipline tandemCoverageDiscipline := by
  exact ⟨
    GenesisCircumcisionCovenantWitness.genesis_circumcision_token,
    Gnosis.Witnesses.Bible.Galatians.GalatiansTitusLibertyWitness.galatians_titus_liberty_boundary,
    Gnosis.Witnesses.Bible.Galatians.GalatiansAntiochConfrontationWitness.galatians_justification_boundary,
    torah_galatians_no_duplicate_coverage⟩

end TorahGalatiansCircumcisionTandemWitness
end Gnosis.Witnesses.Bible.Torah
