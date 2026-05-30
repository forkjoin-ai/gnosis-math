import Init

namespace Gnosis
namespace LodHysteresis

/-!
# LOD Hysteresis (monster-studio Earth, Phase 2)

Backs the terrain / life Level-Of-Detail bands that must NOT chatter as the
camera drifts near a switching boundary. Instead of a single threshold we
use a hysteresis band with two thresholds:

  `ENTER < LEAVE`

The driving quantity `r` is a scaled distance ratio (`distRatio × 100`).
A band's membership is a `Bool` (`true` = inside / detailed, `false` =
outside / coarse). On each frame the state is updated by `step`:

  * enter (become `true`)  when `r ≤ ENTER`
  * leave (become `false`) when `r ≥ LEAVE`
  * otherwise HOLD the previous state.

Because the hold region `(ENTER, LEAVE)` is non-empty (`ENTER < LEAVE`),
the state is constant while `r` stays strictly inside it — that is the
anti-chatter guarantee.
-/

/-- Lower threshold (scaled distRatio × 100): at/below this we enter the band. -/
def ENTER : Int := 160

/-- Upper threshold (scaled distRatio × 100): at/above this we leave the band. -/
def LEAVE : Int := 200

/-- The band is well-formed: the enter threshold is strictly below the leave
    threshold, so there is a genuine hold region. -/
theorem band_wellformed : ENTER < LEAVE := by decide

/-- One frame of the hysteresis update. -/
def step (inside : Bool) (r : Int) : Bool :=
  if r ≤ ENTER then true
  else if LEAVE ≤ r then false
  else inside

/-- Anti-chatter: strictly inside the hold region the state is CONSTANT
    (it equals the previous state, regardless of `r`). -/
theorem no_chatter_inside (inside : Bool) (r : Int) :
    ENTER < r → r < LEAVE → step inside r = inside := by
  intro h1 h2
  unfold step ENTER LEAVE at *
  split <;> (try split) <;> first | rfl | omega

/-- At/below the enter threshold the state becomes `true`. -/
theorem enter_below (inside : Bool) (r : Int) :
    r ≤ ENTER → step inside r = true := by
  intro h
  unfold step ENTER at *
  split
  · rfl
  · omega

/-- At/above the leave threshold the state becomes `false`. -/
theorem leave_above (inside : Bool) (r : Int) :
    LEAVE ≤ r → step inside r = false := by
  intro h
  unfold step ENTER LEAVE at *
  split <;> (try split) <;> first | rfl | omega


/-! ## Witnessed monotone sweep

Sweep `r` DOWN through the band (from above `LEAVE` to below `ENTER`),
then back UP. The state toggles at most once each way: `false` until it
crosses `ENTER`, then `true`, holding through the band, then `false`
again only after crossing `LEAVE`. Starting `inside = false`. -/

/-- Fold one step over a list of `r` values, returning the final state. -/
def runSweep (init : Bool) : List Int → Bool
  | [] => init
  | r :: rs => runSweep (step init r) rs

/-- Down-sweep: r = 240,210,180,150 (crosses ENTER once) ends inside. -/
example : runSweep false [240, 210, 180, 150] = true := by decide

/-- Within the band the state is held (no chatter across 170,190,175). -/
example : runSweep true [170, 190, 175, 185] = true := by decide
example : runSweep false [170, 190, 175, 185] = false := by decide

/-- Up-sweep after entering: 150 (enter) → 170,190 (hold) → 210 (leave). -/
example : runSweep false [150, 170, 190, 210] = false := by decide

/-- Full down-then-up sweep starting outside: enters once on the way down,
    leaves once on the way up — exactly one toggle each direction. -/
example :
    runSweep false [240, 210, 180, 150, 170, 190, 210, 240] = false := by decide

end LodHysteresis
end Gnosis
