import Init
import Gnosis.SkyrmsBuleyEquilibria

namespace Gnosis
namespace NSBTemporalLadderAscent

open Gnosis (godWeight godWeight_ceiling)
open Gnosis.SkyrmsBuleyEquilibria

/-!
# NSB temporal ladder — expansion operators and cross-rung certificates

This module packages **ascent** from a present-only anchor (Nash-flavoured reduced coordination)
through Skyrms-aligned play into Buley temporal data, together with **cross-rung consistency** and
**God-weight** bookkeeping at **zero vent**.

**Scope discipline.** Narrative text about “training trajectories’’ or personal biography is not
imported here—the claims are structural equalities and implications between the formal contracts in
`SkyrmsBuleyEquilibria`. In particular, **`Buley` equilibria are not unique** (`buley_equilibrium_nonunique_witness`)
and there is **no** theorem that only Buley states are “self-verifying’': every rung has its own fixed-point
predicate; Buley distinguishes itself by **deterministic one-step closure** via `buleyUpdate`.
-/

/-- Present-only coordination carrier (reduced **Nash-flavoured** anchor: one instantaneous action). -/
structure NashCoordAnchor where
  present : Nat

/-- Memory / social leg: pair of play values before convention collapse;
for a **canonically lifted** anchor we duplicate the present value (zero off-diagonal memory). -/
structure SkyrmsMemoryPair where
  recall : Nat
  action : Nat

/-- Expand an anchor to symmetric **Skyrms** state and memory pair (recall := action := present). -/
def expandAnchorToSkyrms (a : NashCoordAnchor) : SkyrmsState × SkyrmsMemoryPair :=
  ({ a1 := a.present, a2 := a.present },
    { recall := a.present, action := a.present })

/-- From an aligned Skyrms state (`a1 = a2`) attach explicit **past/future** endpoints. -/
def expandSkyrmsToBuley (past future : Nat) (σ : SkyrmsState) (_ : σ.a1 = σ.a2) : BuleyState :=
  { past := past, present := σ.a1, future := future }

/-- **Coherent triangular lift**: triangular `Buley` state whose midpoint matches the anchor. -/
def expandAnchorToBuley (past future : Nat) (a : NashCoordAnchor)
    (_h : a.present = (past + future) / 2) : BuleyState :=
  expandSkyrmsToBuley past future { a1 := a.present, a2 := a.present } rfl

theorem expandAnchorToSkyrms_is_equilibrium (a : NashCoordAnchor) :
    IsSkyrmsEquilibrium a.present (expandAnchorToSkyrms a).1 := by
  constructor <;> rfl

theorem expandAnchorToBuley_is_equilibrium (past future : Nat) (a : NashCoordAnchor)
    (h : a.present = (past + future) / 2) :
    IsBuleyEquilibrium (expandAnchorToBuley past future a h) := by
  constructor
  · exact h
  · exact buleyUpdate_eq_self_of_midpoint _ h

theorem buley_equilibrium_godWeight_eq_assembly (R : Nat) (s : BuleyState)
    (h : IsBuleyEquilibrium s) :
    godWeight R (buleyVent s) =
      godWeight R (skyrmsVent { a1 := s.present, a2 := s.present }) := by
  have hs0 : skyrmsVent { a1 := s.present, a2 := s.present } = 0 := by
    dsimp [skyrmsVent]
    exact natGap_self s.present
  rw [buley_equilibrium_has_zero_vent s h, hs0]

theorem buley_and_skyrms_ceiling_same_R (R : Nat) (s : BuleyState)
    (hB : IsBuleyEquilibrium s) :
    buleyWeight R s = skyrmsWeight R { a1 := s.present, a2 := s.present } ∧ buleyWeight R s = R + 1 := by
  have hs : IsSkyrmsEquilibrium s.present { a1 := s.present, a2 := s.present } :=
    buley_equilibrium_induces_aligned_skyrms s hB
  refine ⟨?_, ?_⟩
  · unfold buleyWeight skyrmsWeight
    exact buley_equilibrium_godWeight_eq_assembly R s hB
  · exact buley_equilibrium_reaches_ceiling R s hB

/-- Ceiling value **`R + 1` is the same function of `R`** on every rung at zero vent; what changes is the *vent coordinate* until closure. -/
theorem godWeight_ceiling_same_on_zero_vent (R v₁ v₂ : Nat) (hv₁ : v₁ = 0) (hv₂ : v₂ = 0) :
    godWeight R v₁ = godWeight R v₂ := by
  rw [hv₁, hv₂]

end NSBTemporalLadderAscent
end Gnosis
