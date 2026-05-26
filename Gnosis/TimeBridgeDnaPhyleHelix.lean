import Gnosis.TimeBridgeParticleShapeIsomorphism

/-
  TimeBridgeDnaPhyleHelix.lean
  ============================

  Formal support for jump scene 6: a human-scale DNA-like double helix whose
  macro helix is made from chained finite Phyle humps. The carrier remains
  isomorphic to the same two-port time bridge.
-/

namespace GnosisMath
namespace TimeBridgeDnaPhyleHelix

open GnosisMath.Phyle
open GnosisMath.CalatravaBridge
open GnosisMath.TimeBridgePresentCarrier
open GnosisMath.TimeBridgeBigBangEmanation
open GnosisMath.TimeBridgeParticleShapeIsomorphism

/-- One macro hump in the DNA-scale Phyle helix. -/
structure PhyleHump where
  index : Nat
  carrierBars : Nat
  stable : StabilityScore

/-- The default jump-6 chain: twelve visible macro humps. -/
def dnaHumpCount : Nat :=
  12

/-- Every macro hump is made from the nine-bar Phyle carrier. -/
def phyleHump (index : Nat) : PhyleHump where
  index := index
  carrierBars := phyleBars
  stable := defaultStabilityCutoff

/-- The finite chain of Phyle humps used by the DNA visual. -/
def dnaPhyleHumpChain : List PhyleHump :=
  List.ofFn (fun i : Fin dnaHumpCount => phyleHump i.val)

/-- The DNA macro helix uses the `dna` particle-shape carrier presentation. -/
def dnaPhyleCarrier : PathologicTwoPort × PathologicTwoPort :=
  shapeCarrier ParticleShape.dna

theorem dna_hump_count_closed :
    dnaHumpCount = 12 :=
  rfl

theorem dna_phyle_hump_chain_length :
    dnaPhyleHumpChain.length = dnaHumpCount := by
  unfold dnaPhyleHumpChain
  exact List.length_ofFn

theorem phyle_hump_uses_nine_bars (index : Nat) :
    (phyleHump index).carrierBars = 9 := by
  unfold phyleHump
  exact phyle_is_tripod_of_tripods

theorem phyle_hump_is_stable (index : Nat) :
    defaultStabilityCutoff ≤ (phyleHump index).stable := by
  unfold phyleHump
  exact Nat.le_refl defaultStabilityCutoff

theorem dna_shape_carrier_isomorphic_to_bridge :
    CarrierIsomorphic dnaPhyleCarrier
      (timeBridgePresent.entry, timeBridgePresent.exit) := by
  unfold dnaPhyleCarrier
  exact dna_maps_to_bridge_carrier

/-- Every Phyle hump in the finite chain is stable. -/
theorem every_dna_hump_is_stable
    (hump : PhyleHump) (hMember : hump ∈ dnaPhyleHumpChain) :
    defaultStabilityCutoff ≤ hump.stable := by
  unfold dnaPhyleHumpChain at hMember
  rcases List.mem_ofFn.mp hMember with ⟨i, hi⟩
  rw [← hi]
  exact phyle_hump_is_stable i.val

/-- Every Phyle hump in the chain uses the nine-bar Phyle carrier. -/
theorem every_dna_hump_uses_phyle
    (hump : PhyleHump) (hMember : hump ∈ dnaPhyleHumpChain) :
    hump.carrierBars = 9 := by
  unfold dnaPhyleHumpChain at hMember
  rcases List.mem_ofFn.mp hMember with ⟨i, hi⟩
  rw [← hi]
  exact phyle_hump_uses_nine_bars i.val

/--
  DNA Phyle helix bundle: jump 6 is a finite chain of twelve stable Phyle
  humps, each hump uses the nine-bar carrier, and the macro carrier remains
  isomorphic to the two-port time bridge.
-/
theorem time_bridge_dna_phyle_helix_bundle :
    dnaPhyleHumpChain.length = 12 ∧
    (∀ hump : PhyleHump, hump ∈ dnaPhyleHumpChain →
      hump.carrierBars = 9) ∧
    (∀ hump : PhyleHump, hump ∈ dnaPhyleHumpChain →
      defaultStabilityCutoff ≤ hump.stable) ∧
    CarrierIsomorphic dnaPhyleCarrier
      (timeBridgePresent.entry, timeBridgePresent.exit) :=
  ⟨by rw [dna_phyle_hump_chain_length, dna_hump_count_closed],
   every_dna_hump_uses_phyle, every_dna_hump_is_stable,
   dna_shape_carrier_isomorphic_to_bridge⟩

end TimeBridgeDnaPhyleHelix
end GnosisMath
