import Init

namespace Gnosis
namespace OffShelfDrugScreen

/-!
# Off-Shelf Drug Screen

Finite hypothesis screen for common OTC / off-patent / widely available drug
classes against cancer-information topologies. This is not medical advice and
does not assert clinical efficacy. It is a formal triage surface:

* a candidate may match a topology,
* a candidate may have enough evidence witnesses to be worth pursuing,
* a candidate may still fail because risk exceeds modeled benefit,
* candidates without evidence or with excess risk are rejected by antitheorem.

The list is intentionally finite so it can be exhausted by `allDrugClasses`.
-/

inductive DrugClass where
  | aspirin
  | nonAspirinNsaid
  | acetaminophen
  | metformin
  | statin
  | betaBlocker
  | aceInhibitor
  | arb
  | h1Antihistamine
  | h2Blocker
  | protonPumpInhibitor
  | doxycycline
  | macrolideAntibiotic
  | hydroxychloroquine
  | disulfiram
  | mebendazole
  | vitaminD
  | melatonin
  | omega3
  | berberine
  | lowDoseNaltrexone
  | itraconazole
  | celecoxib
  | dipyridamole
  deriving DecidableEq, Repr

def allDrugClasses : List DrugClass :=
  [ .aspirin
  , .nonAspirinNsaid
  , .acetaminophen
  , .metformin
  , .statin
  , .betaBlocker
  , .aceInhibitor
  , .arb
  , .h1Antihistamine
  , .h2Blocker
  , .protonPumpInhibitor
  , .doxycycline
  , .macrolideAntibiotic
  , .hydroxychloroquine
  , .disulfiram
  , .mebendazole
  , .vitaminD
  , .melatonin
  , .omega3
  , .berberine
  , .lowDoseNaltrexone
  , .itraconazole
  , .celecoxib
  , .dipyridamole
  ]

theorem all_drug_classes_count : allDrugClasses.length = 24 := by
  decide

inductive CancerInfoTopology where
  | plateletShield
  | inflammationCox
  | metabolicWarburg
  | angiogenesisInfrastructure
  | adrenergicStressRouting
  | immuneExhaustion
  | acidMicroenvironment
  | microbiomeImmuneTone
  | mitochondrialStress
  | autophagyGate
  | copperProteasomeStress
  | parasiteLikeMicrotubule
  | vitaminDHormoneAxis
  | circadianKiWindow
  | lipidRaftMembraneSignal
  | woundHealingLotl
  deriving DecidableEq, Repr

structure DrugHypothesis where
  drug : DrugClass
  topology : CancerInfoTopology
  topologyBenefit : Nat
  evidenceWitnesses : Nat
  evidenceThreshold : Nat
  safetyRisk : Nat
  deriving DecidableEq, Repr

def evidenceReady (h : DrugHypothesis) : Prop :=
  h.evidenceThreshold ≤ h.evidenceWitnesses

def riskBounded (h : DrugHypothesis) : Prop :=
  h.safetyRisk ≤ h.topologyBenefit

def pursuable (h : DrugHypothesis) : Prop :=
  evidenceReady h ∧ riskBounded h

def rejected (h : DrugHypothesis) : Prop :=
  ¬ pursuable h

def hypothesisFor : DrugClass → DrugHypothesis
  | .aspirin =>
      { drug := .aspirin, topology := .plateletShield, topologyBenefit := 5,
        evidenceWitnesses := 4, evidenceThreshold := 2, safetyRisk := 3 }
  | .nonAspirinNsaid =>
      { drug := .nonAspirinNsaid, topology := .inflammationCox, topologyBenefit := 4,
        evidenceWitnesses := 2, evidenceThreshold := 2, safetyRisk := 4 }
  | .acetaminophen =>
      { drug := .acetaminophen, topology := .inflammationCox, topologyBenefit := 0,
        evidenceWitnesses := 0, evidenceThreshold := 2, safetyRisk := 2 }
  | .metformin =>
      { drug := .metformin, topology := .metabolicWarburg, topologyBenefit := 5,
        evidenceWitnesses := 3, evidenceThreshold := 2, safetyRisk := 2 }
  | .statin =>
      { drug := .statin, topology := .lipidRaftMembraneSignal, topologyBenefit := 3,
        evidenceWitnesses := 2, evidenceThreshold := 2, safetyRisk := 2 }
  | .betaBlocker =>
      { drug := .betaBlocker, topology := .adrenergicStressRouting, topologyBenefit := 3,
        evidenceWitnesses := 2, evidenceThreshold := 2, safetyRisk := 2 }
  | .aceInhibitor =>
      { drug := .aceInhibitor, topology := .angiogenesisInfrastructure, topologyBenefit := 2,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 2 }
  | .arb =>
      { drug := .arb, topology := .angiogenesisInfrastructure, topologyBenefit := 3,
        evidenceWitnesses := 2, evidenceThreshold := 2, safetyRisk := 2 }
  | .h1Antihistamine =>
      { drug := .h1Antihistamine, topology := .immuneExhaustion, topologyBenefit := 2,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 1 }
  | .h2Blocker =>
      { drug := .h2Blocker, topology := .acidMicroenvironment, topologyBenefit := 2,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 1 }
  | .protonPumpInhibitor =>
      { drug := .protonPumpInhibitor, topology := .acidMicroenvironment, topologyBenefit := 2,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 3 }
  | .doxycycline =>
      { drug := .doxycycline, topology := .mitochondrialStress, topologyBenefit := 3,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 2 }
  | .macrolideAntibiotic =>
      { drug := .macrolideAntibiotic, topology := .autophagyGate, topologyBenefit := 2,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 3 }
  | .hydroxychloroquine =>
      { drug := .hydroxychloroquine, topology := .autophagyGate, topologyBenefit := 4,
        evidenceWitnesses := 2, evidenceThreshold := 2, safetyRisk := 5 }
  | .disulfiram =>
      { drug := .disulfiram, topology := .copperProteasomeStress, topologyBenefit := 4,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 4 }
  | .mebendazole =>
      { drug := .mebendazole, topology := .parasiteLikeMicrotubule, topologyBenefit := 3,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 2 }
  | .vitaminD =>
      { drug := .vitaminD, topology := .vitaminDHormoneAxis, topologyBenefit := 2,
        evidenceWitnesses := 2, evidenceThreshold := 2, safetyRisk := 1 }
  | .melatonin =>
      { drug := .melatonin, topology := .circadianKiWindow, topologyBenefit := 2,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 1 }
  | .omega3 =>
      { drug := .omega3, topology := .inflammationCox, topologyBenefit := 1,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 1 }
  | .berberine =>
      { drug := .berberine, topology := .metabolicWarburg, topologyBenefit := 2,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 2 }
  | .lowDoseNaltrexone =>
      { drug := .lowDoseNaltrexone, topology := .immuneExhaustion, topologyBenefit := 2,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 1 }
  | .itraconazole =>
      { drug := .itraconazole, topology := .angiogenesisInfrastructure, topologyBenefit := 4,
        evidenceWitnesses := 2, evidenceThreshold := 2, safetyRisk := 4 }
  | .celecoxib =>
      { drug := .celecoxib, topology := .inflammationCox, topologyBenefit := 4,
        evidenceWitnesses := 2, evidenceThreshold := 2, safetyRisk := 4 }
  | .dipyridamole =>
      { drug := .dipyridamole, topology := .plateletShield, topologyBenefit := 3,
        evidenceWitnesses := 1, evidenceThreshold := 2, safetyRisk := 3 }

def topologyMatches (drug : DrugClass) (topology : CancerInfoTopology) : Prop :=
  (hypothesisFor drug).topology = topology

def strongHypothesisMatch (drug : DrugClass) : Prop :=
  (drug = DrugClass.aspirin ∧ topologyMatches drug CancerInfoTopology.plateletShield) ∨
  (drug = DrugClass.metformin ∧ topologyMatches drug CancerInfoTopology.metabolicWarburg) ∨
  (drug = DrugClass.vitaminD ∧ topologyMatches drug CancerInfoTopology.vitaminDHormoneAxis)

theorem pursuable_if_evidence_and_risk
    (h : DrugHypothesis)
    (hEvidence : evidenceReady h)
    (hRisk : riskBounded h) :
    pursuable h :=
  ⟨hEvidence, hRisk⟩

theorem antitheorem_reject_without_evidence
    (h : DrugHypothesis)
    (hGap : h.evidenceWitnesses < h.evidenceThreshold) :
    rejected h := by
  intro hPursuable
  exact Nat.not_lt_of_ge hPursuable.left hGap

theorem antitheorem_reject_when_risk_exceeds_benefit
    (h : DrugHypothesis)
    (hRisk : h.topologyBenefit < h.safetyRisk) :
    rejected h := by
  intro hPursuable
  exact Nat.not_lt_of_ge hPursuable.right hRisk

theorem antitheorem_not_strong_match
    (drug : DrugClass)
    (hNotStrong : ¬ strongHypothesisMatch drug) :
    ¬ strongHypothesisMatch drug :=
  hNotStrong

/-! ## Closed-screen examples -/

theorem aspirin_matches_platelet_shield_topology :
    topologyMatches DrugClass.aspirin CancerInfoTopology.plateletShield := by
  unfold topologyMatches hypothesisFor
  rfl

theorem aspirin_match_reason :
    (hypothesisFor DrugClass.aspirin).drug = DrugClass.aspirin ∧
    (hypothesisFor DrugClass.aspirin).topology = CancerInfoTopology.plateletShield ∧
    evidenceReady (hypothesisFor DrugClass.aspirin) ∧
    riskBounded (hypothesisFor DrugClass.aspirin) := by
  unfold hypothesisFor evidenceReady riskBounded
  exact ⟨rfl, rfl, by decide, by decide⟩

theorem aspirin_platelet_shield_pursuable :
    pursuable (hypothesisFor DrugClass.aspirin) := by
  unfold hypothesisFor pursuable evidenceReady riskBounded
  exact ⟨by decide, by decide⟩

theorem metformin_matches_warburg_topology :
    topologyMatches DrugClass.metformin CancerInfoTopology.metabolicWarburg := by
  unfold topologyMatches hypothesisFor
  rfl

theorem metformin_match_reason :
    (hypothesisFor DrugClass.metformin).drug = DrugClass.metformin ∧
    (hypothesisFor DrugClass.metformin).topology = CancerInfoTopology.metabolicWarburg ∧
    evidenceReady (hypothesisFor DrugClass.metformin) ∧
    riskBounded (hypothesisFor DrugClass.metformin) := by
  unfold hypothesisFor evidenceReady riskBounded
  exact ⟨rfl, rfl, by decide, by decide⟩

theorem metformin_warburg_pursuable :
    pursuable (hypothesisFor DrugClass.metformin) := by
  unfold hypothesisFor pursuable evidenceReady riskBounded
  exact ⟨by decide, by decide⟩

theorem vitamin_d_matches_hormone_axis_topology :
    topologyMatches DrugClass.vitaminD CancerInfoTopology.vitaminDHormoneAxis := by
  unfold topologyMatches hypothesisFor
  rfl

theorem vitamin_d_match_reason :
    (hypothesisFor DrugClass.vitaminD).drug = DrugClass.vitaminD ∧
    (hypothesisFor DrugClass.vitaminD).topology = CancerInfoTopology.vitaminDHormoneAxis ∧
    evidenceReady (hypothesisFor DrugClass.vitaminD) ∧
    riskBounded (hypothesisFor DrugClass.vitaminD) := by
  unfold hypothesisFor evidenceReady riskBounded
  exact ⟨rfl, rfl, by decide, by decide⟩

theorem vitamin_d_axis_pursuable :
    pursuable (hypothesisFor DrugClass.vitaminD) := by
  unfold hypothesisFor pursuable evidenceReady riskBounded
  exact ⟨by decide, by decide⟩

theorem non_aspirin_nsaid_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.nonAspirinNsaid := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem acetaminophen_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.acetaminophen := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem statin_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.statin := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem beta_blocker_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.betaBlocker := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem ace_inhibitor_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.aceInhibitor := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem arb_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.arb := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem h1_antihistamine_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.h1Antihistamine := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem h2_blocker_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.h2Blocker := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem proton_pump_inhibitor_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.protonPumpInhibitor := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem doxycycline_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.doxycycline := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem macrolide_antibiotic_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.macrolideAntibiotic := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem hydroxychloroquine_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.hydroxychloroquine := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem disulfiram_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.disulfiram := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem mebendazole_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.mebendazole := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem melatonin_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.melatonin := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem omega3_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.omega3 := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem berberine_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.berberine := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem low_dose_naltrexone_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.lowDoseNaltrexone := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem itraconazole_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.itraconazole := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem celecoxib_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.celecoxib := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem dipyridamole_not_strong_match :
    ¬ strongHypothesisMatch DrugClass.dipyridamole := by
  unfold strongHypothesisMatch topologyMatches hypothesisFor
  decide

theorem off_shelf_rest_antitheorem_master :
    (¬ strongHypothesisMatch DrugClass.nonAspirinNsaid) ∧
    (¬ strongHypothesisMatch DrugClass.acetaminophen) ∧
    (¬ strongHypothesisMatch DrugClass.statin) ∧
    (¬ strongHypothesisMatch DrugClass.betaBlocker) ∧
    (¬ strongHypothesisMatch DrugClass.aceInhibitor) ∧
    (¬ strongHypothesisMatch DrugClass.arb) ∧
    (¬ strongHypothesisMatch DrugClass.h1Antihistamine) ∧
    (¬ strongHypothesisMatch DrugClass.h2Blocker) ∧
    (¬ strongHypothesisMatch DrugClass.protonPumpInhibitor) ∧
    (¬ strongHypothesisMatch DrugClass.doxycycline) ∧
    (¬ strongHypothesisMatch DrugClass.macrolideAntibiotic) ∧
    (¬ strongHypothesisMatch DrugClass.hydroxychloroquine) ∧
    (¬ strongHypothesisMatch DrugClass.disulfiram) ∧
    (¬ strongHypothesisMatch DrugClass.mebendazole) ∧
    (¬ strongHypothesisMatch DrugClass.melatonin) ∧
    (¬ strongHypothesisMatch DrugClass.omega3) ∧
    (¬ strongHypothesisMatch DrugClass.berberine) ∧
    (¬ strongHypothesisMatch DrugClass.lowDoseNaltrexone) ∧
    (¬ strongHypothesisMatch DrugClass.itraconazole) ∧
    (¬ strongHypothesisMatch DrugClass.celecoxib) ∧
    (¬ strongHypothesisMatch DrugClass.dipyridamole) := by
  exact ⟨non_aspirin_nsaid_not_strong_match,
    acetaminophen_not_strong_match,
    statin_not_strong_match,
    beta_blocker_not_strong_match,
    ace_inhibitor_not_strong_match,
    arb_not_strong_match,
    h1_antihistamine_not_strong_match,
    h2_blocker_not_strong_match,
    proton_pump_inhibitor_not_strong_match,
    doxycycline_not_strong_match,
    macrolide_antibiotic_not_strong_match,
    hydroxychloroquine_not_strong_match,
    disulfiram_not_strong_match,
    mebendazole_not_strong_match,
    melatonin_not_strong_match,
    omega3_not_strong_match,
    berberine_not_strong_match,
    low_dose_naltrexone_not_strong_match,
    itraconazole_not_strong_match,
    celecoxib_not_strong_match,
    dipyridamole_not_strong_match⟩

theorem acetaminophen_rejected_without_evidence :
    rejected (hypothesisFor DrugClass.acetaminophen) := by
  apply antitheorem_reject_without_evidence
  decide

theorem hydroxychloroquine_rejected_by_risk_gate :
    rejected (hypothesisFor DrugClass.hydroxychloroquine) := by
  apply antitheorem_reject_when_risk_exceeds_benefit
  decide

theorem disulfiram_deferred_without_evidence :
    rejected (hypothesisFor DrugClass.disulfiram) := by
  apply antitheorem_reject_without_evidence
  decide

theorem off_shelf_screen_master :
    allDrugClasses.length = 24 ∧
    pursuable (hypothesisFor DrugClass.aspirin) ∧
    pursuable (hypothesisFor DrugClass.metformin) ∧
    rejected (hypothesisFor DrugClass.acetaminophen) ∧
    rejected (hypothesisFor DrugClass.hydroxychloroquine) := by
  exact ⟨all_drug_classes_count,
    aspirin_platelet_shield_pursuable,
    metformin_warburg_pursuable,
    acetaminophen_rejected_without_evidence,
    hydroxychloroquine_rejected_by_risk_gate⟩

end OffShelfDrugScreen
end Gnosis
