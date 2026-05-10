/-
  TaoBowlTwinVoidBridge.lean
  ===========================

  Morphisms between `StepwiseAnalysisFramework.TwinVoidDial` (three-field
  step dial) and `TaoBowlTwinVoid.TaoBowlWithConsensus` (twin-void bowl with
  rigidity / damping), plus optional reconstruction on `AnalysisCard`.

  Imports `Gnosis.StepwiseAnalysisFramework` and `Gnosis.TaoBowlTwinVoid`.
  Optional standing-wave chamber hook: `optionalChamberOfCard` composes
  `optionalConsensusBowl` with `toClassicBowl` and `chamberOfBowl`.

  Zero `sorry`, zero new `axiom`.
-/

import Gnosis.StepwiseAnalysisFramework
import Gnosis.TaoBowlTwinVoid

namespace TaoBowlTwinVoidBridge

open StepwiseAnalysisFramework
open TaoBowlTwinVoid
open EchoChamberAsTaoBowl
open EchoChamberAsStandingWave
open OpinionAsInterference

/-! ## Dial ↔ consensus bowl -/

/-- Drop rigidity/damping: the three consensus-axis fields agree with
    `TwinVoidDial`. -/
def twinDialOfConsensus (b : TaoBowlWithConsensus) : TwinVoidDial where
  rim := b.rim
  voidStructural := b.voidStructural
  consensusFill := b.consensusFill

/-- Attach default rigidity and damping from explicit parameters. -/
def consensusBowlOfDial (d : TwinVoidDial) (rigidity damping : Nat) : TaoBowlWithConsensus where
  rim := d.rim
  voidStructural := d.voidStructural
  consensusFill := d.consensusFill
  rigidity := rigidity
  damping := damping

theorem twinDial_rim (b : TaoBowlWithConsensus) :
    (twinDialOfConsensus b).rim = b.rim :=
  rfl

theorem twinDial_voidStructural (b : TaoBowlWithConsensus) :
    (twinDialOfConsensus b).voidStructural = b.voidStructural :=
  rfl

theorem twinDial_consensusFill (b : TaoBowlWithConsensus) :
    (twinDialOfConsensus b).consensusFill = b.consensusFill :=
  rfl

theorem effective_void_agrees (b : TaoBowlWithConsensus) :
    StepwiseAnalysisFramework.effectiveVoid (twinDialOfConsensus b) =
      TaoBowlTwinVoid.effectiveVoid b := by
  unfold StepwiseAnalysisFramework.effectiveVoid TaoBowlTwinVoid.effectiveVoid twinDialOfConsensus
  rfl

theorem functional_void_score_agrees (b : TaoBowlWithConsensus) :
    StepwiseAnalysisFramework.functionalVoidScore (twinDialOfConsensus b) =
      TaoBowlTwinVoid.functionalUsefulness b := by
  unfold StepwiseAnalysisFramework.functionalVoidScore TaoBowlTwinVoid.functionalUsefulness
  rw [effective_void_agrees, twinDial_rim]

theorem structural_void_score_agrees (b : TaoBowlWithConsensus) :
    StepwiseAnalysisFramework.structuralVoidScore (twinDialOfConsensus b) =
      TaoBowlTwinVoid.structuralUsefulness b := by
  unfold StepwiseAnalysisFramework.structuralVoidScore TaoBowlTwinVoid.structuralUsefulness
  unfold twinDialOfConsensus
  rfl

theorem twinDial_consensus_roundtrip (d : TwinVoidDial) (rigidity damping : Nat) :
    twinDialOfConsensus (consensusBowlOfDial d rigidity damping) = d := by
  cases d
  rfl

theorem consensus_bowl_roundtrip_fields (b : TaoBowlWithConsensus) :
    consensusBowlOfDial (twinDialOfConsensus b) b.rigidity b.damping = b := by
  cases b
  rfl

/-! ## AnalysisCard: optional bowl from optional dial -/

/-- When a card carries `some` dial, build the consensus bowl once
    rigidity and damping are supplied. -/
def optionalConsensusBowl (c : AnalysisCard) (rigidity damping : Nat) :
    Option TaoBowlWithConsensus :=
  c.twinDial.map (fun d => consensusBowlOfDial d rigidity damping)

theorem optional_consensus_bowl_eq_some (c : AnalysisCard) (d : TwinVoidDial)
    (r dmp : Nat) (h : c.twinDial = some d) :
    optionalConsensusBowl c r dmp = some (consensusBowlOfDial d r dmp) := by
  unfold optionalConsensusBowl
  simp [h]

theorem optional_consensus_bowl_eq_none (c : AnalysisCard) (r dmp : Nat)
    (h : c.twinDial = none) : optionalConsensusBowl c r dmp = none := by
  unfold optionalConsensusBowl
  simp [h]

/-! ## Standing-wave chamber from a card (`chamberOfBowl` after projection) -/

/-- `center_frequency` on `chamberOfBowl` ignores `members`; it is always
    `fundamentalMode` on the underlying `TaoBowl` (same as
    `TaoBowlSignalCoupling.chamberOfBowl_center_frequency` for `[]`). -/
theorem chamberOfBowl_center_frequency_any_members (b : TaoBowl) (members : List OpinionWave) :
    (chamberOfBowl b members).center_frequency = fundamentalMode b := by
  unfold chamberOfBowl
  rfl

/-- Map optional consensus → classic Tao bowl → standing-wave chamber. -/
def optionalChamberOfCard (c : AnalysisCard) (rigidity damping : Nat)
    (members : List OpinionWave) : Option EchoChamber :=
  (optionalConsensusBowl c rigidity damping).map fun b =>
    chamberOfBowl (TaoBowlTwinVoid.toClassicBowl b) members

theorem optional_chamber_of_card_eq_some (c : AnalysisCard) (d : TwinVoidDial)
    (r dmp : Nat) (members : List OpinionWave) (h : c.twinDial = some d) :
    optionalChamberOfCard c r dmp members =
      some (chamberOfBowl (TaoBowlTwinVoid.toClassicBowl (consensusBowlOfDial d r dmp)) members) := by
  unfold optionalChamberOfCard optionalConsensusBowl
  simp [h]

theorem optional_chamber_center_frequency_map_eq_some_dial
    (c : AnalysisCard) (d : TwinVoidDial) (r dmp : Nat) (members : List OpinionWave)
    (h : c.twinDial = some d) :
    (optionalChamberOfCard c r dmp members).map EchoChamber.center_frequency =
      some (fundamentalMode (TaoBowlTwinVoid.toClassicBowl (consensusBowlOfDial d r dmp))) := by
  rw [optional_chamber_of_card_eq_some c d r dmp members h]
  simp only [Option.map_some]
  exact congrArg Option.some
    (chamberOfBowl_center_frequency_any_members (TaoBowlTwinVoid.toClassicBowl (consensusBowlOfDial d r dmp)) members)

theorem optional_chamber_center_frequency_eq_of_cards_same_dial
    (c1 c2 : AnalysisCard) (d : TwinVoidDial) (r dmp : Nat) (members : List OpinionWave)
    (h1 : c1.twinDial = some d) (h2 : c2.twinDial = some d) :
    (optionalChamberOfCard c1 r dmp members).map EchoChamber.center_frequency =
      (optionalChamberOfCard c2 r dmp members).map EchoChamber.center_frequency := by
  rw [optional_chamber_center_frequency_map_eq_some_dial c1 d r dmp members h1]
  rw [optional_chamber_center_frequency_map_eq_some_dial c2 d r dmp members h2]

/-! ### Same dial + rigidity/damping → same `fundamentalMode` on projected classic bowl -/

theorem bowl_eq_of_optionalConsensus_some (c : AnalysisCard) (d : TwinVoidDial) (r dmp : Nat)
    (h : c.twinDial = some d) (b : TaoBowlWithConsensus)
    (hb : optionalConsensusBowl c r dmp = some b) : b = consensusBowlOfDial d r dmp := by
  have hs : some b = some (consensusBowlOfDial d r dmp) := by
    rw [← hb, optional_consensus_bowl_eq_some c d r dmp h]
  injection hs

theorem fundamental_mode_toClassic_eq_of_optionalConsensus_paths
    (c1 c2 : AnalysisCard) (d : TwinVoidDial) (r dmp : Nat)
    (h1 : c1.twinDial = some d) (h2 : c2.twinDial = some d)
    (b1 b2 : TaoBowlWithConsensus)
    (hb1 : optionalConsensusBowl c1 r dmp = some b1)
    (hb2 : optionalConsensusBowl c2 r dmp = some b2) :
    fundamentalMode (TaoBowlTwinVoid.toClassicBowl b1) =
      fundamentalMode (TaoBowlTwinVoid.toClassicBowl b2) := by
  rw [bowl_eq_of_optionalConsensus_some c1 d r dmp h1 b1 hb1,
      bowl_eq_of_optionalConsensus_some c2 d r dmp h2 b2 hb2]

/-- **Run lemma:** every card in `run` carries the *same* `some d` dial and
    the same `rigidity` / `damping` parameters → each optional chamber’s
    `center_frequency` map agrees (whenever the dial is present on both). -/
theorem run_forall_same_dial_same_optional_chamber_center
    (run : AnalysisRun) (d : TwinVoidDial) (r dmp : Nat) (members : List OpinionWave)
    (hall : ∀ c ∈ run, c.twinDial = some d) :
    ∀ c1 c2, c1 ∈ run → c2 ∈ run →
      (optionalChamberOfCard c1 r dmp members).map EchoChamber.center_frequency =
        (optionalChamberOfCard c2 r dmp members).map EchoChamber.center_frequency := by
  intro c1 c2 h1 h2
  exact optional_chamber_center_frequency_eq_of_cards_same_dial c1 c2 d r dmp members
    (hall c1 h1) (hall c2 h2)

/-! ## `toClassicBowl` factors through the stepwise dial -/

theorem toClassic_bowl_eq_of_twin_dial (b : TaoBowlWithConsensus) :
    TaoBowlTwinVoid.toClassicBowl b =
      { rim := b.rim
        void := StepwiseAnalysisFramework.effectiveVoid (twinDialOfConsensus b)
        rigidity := b.rigidity
        damping := b.damping } := by
  unfold TaoBowlTwinVoid.toClassicBowl
  rw [← effective_void_agrees]

end TaoBowlTwinVoidBridge
