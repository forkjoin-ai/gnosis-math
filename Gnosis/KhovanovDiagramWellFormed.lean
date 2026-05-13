import Init
import Gnosis.KhovanovCategorifiesJones
import Gnosis.PeriodicElementLinkAtlas

/-!
# Kauffman-resolution cube bookkeeping for `KhovanovCategorifiesJones.Diagram`

For an `n`–crossing diagram one expects `2^n` binary resolutions `α ∈ {0,1}^n`. The
chain-level representation in `KhovanovCategorifiesJones` stores exactly one
`( |α|, k(α) )` row per `α`, so **`resolutions.length` should be `2^(n₊ + n₋)`**.

*   The **canonical catalog** (`unknot`, Hopf, trefoil, `unknotTwist`) satisfies
    this cube-arithmetic shape (`native_decide`).
*   The **`diagramCodecRow`** IUPAC injector tags an extra synthetic row onto the
    unknot’s one-entry table **without** increasing `n₊+n₋`, so it is **not**
    cube-shaped — by design: injectivity lives in `DecidableEq`, not in classical
    diagram completeness.

Counting-only bound for how large `n₊+n₋` must be for *118* distinct resolution
slots in a **full** cube: `Gnosis.IupacResolutionCubeBound`. One concrete
cube-shaped bookkeeping `Diagram` with `n₊ + n₋ = 7` is `Gnosis.SevenCrossingIupacShell`.
General **prefix | ith | suffix** identity for resolution tables: `KhovanovCategorifiesJones.bracketResolutions_split`;
shell **`jonesPoly`** at the canonical `rowSlotFin128` with the middle summand **expanded**:
`SevenCrossingIupacShell.jonesPoly_sevenCrossingTaggedDiagram_rowSlotFin128_closedSummand`.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace KhovanovDiagramWellFormed

open KhovanovCategorifiesJones

/-- Expected resolution count for `n₊ + n₋` signed crossings. -/
def resolutionCubeCardinality (D : Diagram) : Nat :=
  2 ^ (D.nPlus + D.nMinus)

/--
`true` when the stored resolution table has the size of the Kauffman
`Bool^n` cube (`n = n₊+n₋`). This is a **presentation-shape** check, not ambient
isotopy.
-/
def isResolutionCubeShaped (D : Diagram) : Bool :=
  decide (D.resolutions.length = resolutionCubeCardinality D)

theorem unknotResolutionCubeShaped :
    (unknot.resolutions.length = resolutionCubeCardinality unknot) := by native_decide

theorem hopfPlusResolutionCubeShaped :
    (hopfPlus.resolutions.length = resolutionCubeCardinality hopfPlus) := by native_decide

theorem hopfMinusResolutionCubeShaped :
    (hopfMinus.resolutions.length = resolutionCubeCardinality hopfMinus) := by native_decide

theorem trefoilPlusResolutionCubeShaped :
    (trefoilPlus.resolutions.length = resolutionCubeCardinality trefoilPlus) := by native_decide

theorem unknotTwistResolutionCubeShaped :
    (unknotTwist.resolutions.length = resolutionCubeCardinality unknotTwist) := by native_decide

/-- The IUPAC codec is **not** cube-shaped: two table rows while `n₊+n₋ = 0`. -/
theorem diagramCodecRow_not_resolution_cube_shaped (row : Fin 118) :
    ¬(PeriodicElementLinkAtlas.diagramCodecRow row).resolutions.length =
        resolutionCubeCardinality (PeriodicElementLinkAtlas.diagramCodecRow row) := by
  intro h
  simp [resolutionCubeCardinality, PeriodicElementLinkAtlas.diagramCodecRow, List.length,
    Nat.pow_zero] at h

end KhovanovDiagramWellFormed
end Gnosis
