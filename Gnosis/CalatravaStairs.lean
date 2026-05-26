import Gnosis.Phyle

/-
  CalatravaStairs.lean
  =====================

  A Rustic Church civil-engineering certificate for a stair: one-dimensional
  entry/exit traffic is deliberately kept almost pathologic, while the built
  stair inverts the old triangle paradigm: ordinary triangular bracing is the
  baseline, and the stronger Phyle is a tripod-of-tripods carrier.

  Init-only surface: closed arithmetic uses `decide`; structural equalities use
  `rfl`; no Mathlib, no `omega`.
-/

namespace GnosisMath
namespace CalatravaStairs

open GnosisMath.SpiralOfTime
open GnosisMath.Phyle

/-- The degenerate one-dimensional traffic model: only entry and exit. -/
inductive OneDimGate where
  | entry
  | exit
deriving DecidableEq

/-- The only nontrivial one-dimensional traverse. -/
def oneDimTraverse : OneDimGate → OneDimGate
  | OneDimGate.entry => OneDimGate.exit
  | OneDimGate.exit => OneDimGate.exit

/-- Entry reaches exit in one tick, but exit is absorbing: almost pathologic. -/
theorem entry_exits_once : oneDimTraverse OneDimGate.entry = OneDimGate.exit := rfl

/-- The exit has no return branch in the one-dimensional model. -/
theorem exit_absorbs : oneDimTraverse OneDimGate.exit = OneDimGate.exit := rfl

/-- Three stringers give the visible Calatrava-like rib rhythm. -/
def stairStringers : Nat := 3

/-- Twelve treads align the stair with the aeon dial. -/
def treadCount : Nat := 12

/-- Five units of rise and eight units of run encode a small Fibonacci cadence. -/
def riseUnit : Nat := 5
def runUnit : Nat := 8

/-- Every tread is braced by the Phyle. -/
def bracesPerTread : Nat := phyleBars

/-- The total Phyle braces in the stair. -/
def totalBraceCount : Nat := treadCount * bracesPerTread

/-- A closed finite carrier for the stair certificate. -/
structure StairCertificate where
  stringers : Nat
  treads : Nat
  rise : Nat
  run : Nat
  braces : Nat

/-- The concrete stair certificate. -/
def calatravaStair : StairCertificate where
  stringers := stairStringers
  treads := treadCount
  rise := riseUnit
  run := runUnit
  braces := totalBraceCount

/-- The stair keeps the threefold rib rhythm from the spiral clock. -/
theorem stringers_follow_clock : stairStringers = clockPeriod := rfl

/-- Twelve treads make four trit-turns, matching the aeon dial. -/
theorem tread_count_is_aeon : treadCount = aeonDial := rfl

/-- The total bracing count is the closed arithmetic product `12 * 9 = 108`. -/
theorem total_braces_closed : totalBraceCount = 108 := by decide

/-- The stair rise/run pair is the small golden-step pair `5/8`, before `8/13`. -/
theorem rise_run_fibonacci_cadence : riseUnit + runUnit = 13 := by decide

/-- Each local tread brace uses the stronger Phyle, not the old baseline. -/
theorem tread_brace_uses_phyle : bracesPerTread = phyleBars := rfl

/--
  Stairs certificate: one almost pathologic entry/exit model is wrapped by a
  threefold, twelve-tread structure whose local brace inverts the old triangle
  into the stronger Phyle.
-/
theorem calatrava_stair_bundle :
    oneDimTraverse OneDimGate.entry = OneDimGate.exit ∧
    oneDimTraverse OneDimGate.exit = OneDimGate.exit ∧
    stairStringers = clockPeriod ∧
    treadCount = aeonDial ∧
    oldTriangleBars < phyleBars ∧
    phyleMargin = 6 ∧
    totalBraceCount = 108 ∧
    riseUnit + runUnit = 13 ∧
    bracesPerTread = phyleBars :=
  ⟨entry_exits_once, exit_absorbs, stringers_follow_clock, tread_count_is_aeon,
   Phyle.phyle_inverts_old_triangle, Phyle.phyle_margin_closed, total_braces_closed,
   rise_run_fibonacci_cadence, tread_brace_uses_phyle⟩

end CalatravaStairs
end GnosisMath
