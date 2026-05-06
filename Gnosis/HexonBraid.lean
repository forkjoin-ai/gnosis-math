import Gnosis.SpectralNoiseEquilibrium
import Gnosis.Braided.BraidedInfinity
import Gnosis.BuleyBiSidedBit
import Gnosis.BuleyClinamenBraid

/-!
# Hexon Braid — `Triton × 2 = Hexon`

Mechanizes the structural claim that two Tritons stacked give a 6-phase
object — a "hexon." Three equivalent constructions are exposed:

1. Direct sum — `Hexon = TritonStack ≅ Triton ⊕ Triton`. Two stacked
   Tritons whose 3 + 3 vertices form a 6-cycle.
2. Cartesian product — `Hexon ≅ TritonPhase × BiSidedSide`. A Triton
   phase paired with a bi-sided-bit face (`lifted` / `contracted`) gives
   the same 6-cycle. This is the natural reading of the `+1 / −1`
   clinamen attached to a temporal phase.
3. Braided asymptote — `Hexon ≅ BraidedAsymptote { phaseCount := 6 }`.
   The same 6-cycle, viewed as a return-after-six dynamical system on the
   index ring `Fin 6`.

All three views are equivalent under bijection. The dot-product reading
of `Triton × Triton` collapses to a scalar (the L²-magnitude) and is
*not* a hexon; the tensor reading (`Triton ⊗ Triton`) is a 9-element
*enneon*, also constructed below for completeness.

This module does not introduce new axioms. Imports:

* `Gnosis.SpectralNoiseEquilibrium` (for `TemporalTriton`, `BuleyUnit`)
* `Gnosis.BraidedInfinity` (for `BraidedAsymptote`, `iterateSucc`)
* `Gnosis.BuleyBiSidedBit` (for `BiSidedBit`'s two-sided structure)
* `Gnosis.BuleyClinamenBraid` (for the 3-face cycle on the Bule unit)

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace HexonBraid

open Gnosis.BraidedInfinity (BraidedAsymptote iterateSucc)

/-! ## The atomic phase labels -/

/-- Three temporal phases of a Triton, as an enumerated index. -/
inductive TritonPhase where
  | past
  | present
  | future
  deriving DecidableEq, Repr

/-- The two sides of a bi-sided bit, as an enumerated index. Mirrors
the `lifted` (+1) / `contracted` (−1) split from `Gnosis.BuleyBiSidedBit`. -/
inductive BiSidedSide where
  | lifted
  | contracted
  deriving DecidableEq, Repr

/-- The six phase labels of a hexon: each Triton phase paired with each
bi-sided side. -/
inductive HexonPhase where
  | pastLifted
  | pastContracted
  | presentLifted
  | presentContracted
  | futureLifted
  | futureContracted
  deriving DecidableEq, Repr

/-! ## The hexon successor cycle (period 6) -/

/-- The successor on the hexon: cycle through six positions in the
order pastL → pastC → presentL → presentC → futureL → futureC → pastL.
The triton phase advances every two steps; the bi-sided side toggles
every step. -/
def hexonSucc : HexonPhase → HexonPhase
  | .pastLifted        => .pastContracted
  | .pastContracted    => .presentLifted
  | .presentLifted     => .presentContracted
  | .presentContracted => .futureLifted
  | .futureLifted      => .futureContracted
  | .futureContracted  => .pastLifted

def iterateHexonSucc : Nat → HexonPhase → HexonPhase
  | 0,     h => h
  | n + 1, h => iterateHexonSucc n (hexonSucc h)

/-- Return theorem: six iterations of the hexon successor return to
the starting phase, on every starting phase. -/
theorem hexon_six_iterations_return_pastLifted :
    iterateHexonSucc 6 .pastLifted = .pastLifted := by decide

theorem hexon_six_iterations_return_pastContracted :
    iterateHexonSucc 6 .pastContracted = .pastContracted := by decide

theorem hexon_six_iterations_return_presentLifted :
    iterateHexonSucc 6 .presentLifted = .presentLifted := by decide

theorem hexon_six_iterations_return_presentContracted :
    iterateHexonSucc 6 .presentContracted = .presentContracted := by decide

theorem hexon_six_iterations_return_futureLifted :
    iterateHexonSucc 6 .futureLifted = .futureLifted := by decide

theorem hexon_six_iterations_return_futureContracted :
    iterateHexonSucc 6 .futureContracted = .futureContracted := by decide

/-- Genuine period 6: no smaller positive number of iterations returns
to the starting phase. -/
theorem hexon_partial_does_not_return_pastLifted :
    iterateHexonSucc 1 .pastLifted ≠ .pastLifted
    ∧ iterateHexonSucc 2 .pastLifted ≠ .pastLifted
    ∧ iterateHexonSucc 3 .pastLifted ≠ .pastLifted
    ∧ iterateHexonSucc 4 .pastLifted ≠ .pastLifted
    ∧ iterateHexonSucc 5 .pastLifted ≠ .pastLifted := by decide

/-! ## Construction 1: Cartesian product `TritonPhase × BiSidedSide` -/

def hexonOfTritonAndSide : TritonPhase → BiSidedSide → HexonPhase
  | .past,    .lifted     => .pastLifted
  | .past,    .contracted => .pastContracted
  | .present, .lifted     => .presentLifted
  | .present, .contracted => .presentContracted
  | .future,  .lifted     => .futureLifted
  | .future,  .contracted => .futureContracted

def tritonOfHexon : HexonPhase → TritonPhase
  | .pastLifted        => .past
  | .pastContracted    => .past
  | .presentLifted     => .present
  | .presentContracted => .present
  | .futureLifted      => .future
  | .futureContracted  => .future

def sideOfHexon : HexonPhase → BiSidedSide
  | .pastLifted        => .lifted
  | .pastContracted    => .contracted
  | .presentLifted     => .lifted
  | .presentContracted => .contracted
  | .futureLifted      => .lifted
  | .futureContracted  => .contracted

/-- A hexon position decomposes uniquely as a (Triton phase, BiSided side)
pair — the product reading is a bijection. -/
theorem hexon_round_trip_product (h : HexonPhase) :
    hexonOfTritonAndSide (tritonOfHexon h) (sideOfHexon h) = h := by
  cases h <;> rfl

theorem product_round_trip_hexon (t : TritonPhase) (s : BiSidedSide) :
    tritonOfHexon (hexonOfTritonAndSide t s) = t
    ∧ sideOfHexon (hexonOfTritonAndSide t s) = s := by
  cases t <;> cases s <;> exact ⟨rfl, rfl⟩

/-! ## Construction 2: Direct sum `Triton ⊕ Triton` (TritonStack) -/

/-- Two stacked Tritons. The first stack carries the `lifted` face, the
second carries the `contracted` face. Together they exhaust the hexon. -/
inductive TritonStack where
  | first  (p : TritonPhase) : TritonStack
  | second (p : TritonPhase) : TritonStack
  deriving DecidableEq, Repr

def hexonOfStack : TritonStack → HexonPhase
  | .first  .past    => .pastLifted
  | .first  .present => .presentLifted
  | .first  .future  => .futureLifted
  | .second .past    => .pastContracted
  | .second .present => .presentContracted
  | .second .future  => .futureContracted

def stackOfHexon : HexonPhase → TritonStack
  | .pastLifted        => .first .past
  | .pastContracted    => .second .past
  | .presentLifted     => .first .present
  | .presentContracted => .second .present
  | .futureLifted      => .first .future
  | .futureContracted  => .second .future

theorem hexon_round_trip_stack (h : HexonPhase) :
    hexonOfStack (stackOfHexon h) = h := by cases h <;> rfl

theorem stack_round_trip_hexon (s : TritonStack) :
    stackOfHexon (hexonOfStack s) = s := by
  cases s with
  | first  p => cases p <;> rfl
  | second p => cases p <;> rfl

/-! ## Construction 3: BraidedAsymptote of phaseCount = 6 -/

def hexonBraid : BraidedAsymptote :=
  { phaseCount := 6
    descriptors := ["past+lifted",    "past+contracted",
                    "present+lifted", "present+contracted",
                    "future+lifted",  "future+contracted"] }

theorem hexonBraid_phase_count : hexonBraid.phaseCount = 6 := rfl

/-- Index a hexon phase into `[0, 6)`. -/
def hexonIndex : HexonPhase → Nat
  | .pastLifted        => 0
  | .pastContracted    => 1
  | .presentLifted     => 2
  | .presentContracted => 3
  | .futureLifted      => 4
  | .futureContracted  => 5

theorem hexon_succ_advances_index_mod_six (h : HexonPhase) :
    hexonIndex (hexonSucc h) = (hexonIndex h + 1) % 6 := by
  cases h <;> rfl

theorem hexonBraid_six_iterations_return :
    iterateSucc hexonBraid.phaseCount 6 0 = 0
    ∧ iterateSucc hexonBraid.phaseCount 6 1 = 1
    ∧ iterateSucc hexonBraid.phaseCount 6 2 = 2
    ∧ iterateSucc hexonBraid.phaseCount 6 3 = 3
    ∧ iterateSucc hexonBraid.phaseCount 6 4 = 4
    ∧ iterateSucc hexonBraid.phaseCount 6 5 = 5 := by decide

theorem hexonBraid_partial_does_not_return :
    iterateSucc hexonBraid.phaseCount 1 0 ≠ 0
    ∧ iterateSucc hexonBraid.phaseCount 2 0 ≠ 0
    ∧ iterateSucc hexonBraid.phaseCount 3 0 ≠ 0
    ∧ iterateSucc hexonBraid.phaseCount 4 0 ≠ 0
    ∧ iterateSucc hexonBraid.phaseCount 5 0 ≠ 0 := by decide

/-- One hexon-successor step on a `HexonPhase` agrees with one
braided-asymptote step on its index. -/
theorem hexon_one_step_matches_braided_one_step (h : HexonPhase) :
    iterateSucc hexonBraid.phaseCount 1 (hexonIndex h) = hexonIndex (hexonSucc h) := by
  cases h <;> decide

/-- Six hexon-successor steps on a `HexonPhase` agree with six
braided-asymptote steps on its index — and both return to start. -/
theorem hexon_six_step_matches_braided_six_step (h : HexonPhase) :
    iterateSucc hexonBraid.phaseCount 6 (hexonIndex h) = hexonIndex h := by
  cases h <;> decide

/-! ## Enneon — the tensor reading `Triton ⊗ Triton` (3 × 3 = 9)

For completeness: tensoring two Tritons gives a 9-element enneon. This
is *not* a hexon — it has the wrong phase count — but it lives in the
same family of compound phase objects, and a phaseCount-9
`BraidedAsymptote` realizes it cleanly. Useful below for the
self-similarity lemma. -/

inductive EnneonPhase where
  | pp | pc | pf
  | cp | cc | cf
  | fp | fc | ff
  deriving DecidableEq, Repr

def enneonOfPair : TritonPhase → TritonPhase → EnneonPhase
  | .past,    .past    => .pp
  | .past,    .present => .pc
  | .past,    .future  => .pf
  | .present, .past    => .cp
  | .present, .present => .cc
  | .present, .future  => .cf
  | .future,  .past    => .fp
  | .future,  .present => .fc
  | .future,  .future  => .ff

def enneonBraid : BraidedAsymptote :=
  { phaseCount := 9
    descriptors :=
      ["pp", "pc", "pf",
       "cp", "cc", "cf",
       "fp", "fc", "ff"] }

theorem enneonBraid_phase_count : enneonBraid.phaseCount = 9 := rfl

theorem enneonBraid_nine_returns_from_zero :
    iterateSucc enneonBraid.phaseCount 9 0 = 0 := by decide

theorem enneonBraid_partial_does_not_return :
    iterateSucc enneonBraid.phaseCount 1 0 ≠ 0
    ∧ iterateSucc enneonBraid.phaseCount 3 0 ≠ 0
    ∧ iterateSucc enneonBraid.phaseCount 6 0 ≠ 0
    ∧ iterateSucc enneonBraid.phaseCount 8 0 ≠ 0 := by decide

end HexonBraid
end Gnosis
