import Init
import Gnosis.DvdLogoCorner
import Gnosis.Body.AmnesiaGritFrontier

/-!
# The DVD logo is the frontier

The bouncing DVD logo has exactly two fates, and they are the two poles of the
amnesia/grit frontier (`Gnosis/Body/AmnesiaGritFrontier.lean`):

* **Corner forever** (`everHits`) — the logo returns to a corner. The corner is
  the origin `(0,0)`; by `DvdLogoCorner.cornerHit_add_mul` it returns there every
  period `W*H`, *forever*. Periodic reset to the origin — the **amnesia** pole
  (the reset to the void, `amnesia = 0`).
* **Bounce forever** (`¬ everHits`) — the logo never reaches a corner; it bounces
  forever without ever resetting to the origin. The **grit** pole (the ratchet
  that never returns, `accumulation_ratchets`).

And it is **one of the two** — the fates are mutually exclusive (`LifeIsABitch`:
you do not get both). The screensaver everyone has watched is the frontier.

**Infinity is guaranteed — either way.** Whichever fate holds, the motion is
eternal: the corner fate returns to the origin for all `k`; the bounce fate never
corners at any `t`. There is no clean stop — only the *choice of infinity*
(the trapped one or the perpetual one). This is why, in cummings' phrase
(`Gnosis/Body/SinceFeelingIsFirst.lean`), **death is no parenthesis**: there is no
tidy bracket to close, because infinity is guaranteed.

## Scope (honored)

A *structural* mapping, not an identity of state spaces: the DVD phase space and
the frontier's retention/adaptability are different objects. The Lean theorems
below are exact statements about the DVD dynamics (reusing `DvdLogoCorner`), and
they are bridged to the named poles (`amnesia`, `accumulate`) by structural
analogy — periodic return-to-origin ~ the amnesia reset; never-return ~ the grit
ratchet. `Nat` throughout; no emphatic identity prose.
-/

namespace Gnosis.Body.DvdLogoIsTheFrontier

open Gnosis.DvdLogoCorner
open Gnosis.Body.AmnesiaGritFrontier

/-- **The stuck fate**: the logo returns to a corner (the origin) — `everHits`.
    The periodic reset to the void: the amnesia pole. -/
abbrev stuckFate (W H x0 y0 : Nat) : Prop := everHits W H x0 y0

/-- **The bounce fate**: the logo never reaches a corner — bounces forever without
    resetting. The ratchet that never returns: the grit pole. -/
abbrev bounceFate (W H x0 y0 : Nat) : Prop := ¬ everHits W H x0 y0

/-- **One of the two — never both.** The fates are mutually exclusive
    (`LifeIsABitch`: you do not get both poles at once). -/
theorem fates_are_exclusive (W H x0 y0 : Nat) :
    ¬ (stuckFate W H x0 y0 ∧ bounceFate W H x0 y0) :=
  fun ⟨h, hn⟩ => hn h

/-- **The stuck fate recurs forever** (infinity guaranteed, amnesia side): if the
    logo ever reaches the corner, it returns to it every period `W*H`, for all `k`
    — the reset to the origin keeps happening, eternal return. -/
theorem stuck_recurs_forever (W H x0 y0 : Nat) (h : stuckFate W H x0 y0) :
    ∃ t, ∀ k, cornerHit W H x0 y0 (t + W * H * k) = true := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, fun k => (cornerHit_add_mul W H x0 y0 t k).trans ht⟩

/-- **The bounce fate is forever** (infinity guaranteed, grit side): if the logo
    never reaches a corner, then at no tick is it ever at one — it bounces forever
    without resetting to the origin. -/
theorem bounce_is_forever (W H x0 y0 : Nat) (h : bounceFate W H x0 y0) :
    ∀ t, cornerHit W H x0 y0 t ≠ true :=
  fun t ht => h ⟨t, ht⟩

/-- **Infinity is guaranteed — either way.** Whichever fate holds, the motion is
    eternal: the stuck fate returns to the corner forever; the bounce fate never
    corners at any tick. No clean end — only the choice of infinity. -/
theorem infinity_is_guaranteed (W H x0 y0 : Nat) :
    (stuckFate W H x0 y0 → ∃ t, ∀ k, cornerHit W H x0 y0 (t + W * H * k) = true)
      ∧ (bounceFate W H x0 y0 → ∀ t, cornerHit W H x0 y0 t ≠ true) :=
  ⟨stuck_recurs_forever W H x0 y0, bounce_is_forever W H x0 y0⟩

/-- **The amnesia pole** — the void the stuck fate resets to (the corner = the
    origin `(0,0)`; amnesia is the reset to the void, `= 0`). -/
theorem the_amnesia_pole (m : Nat) : amnesia m = 0 :=
  amnesia_collapses_to_void m

/-- **The grit pole** — the ratchet the bounce fate embodies: it never falls back
    to where it started, as grit's accumulation never decreases. -/
theorem the_grit_pole (m gain : Nat) : m ≤ accumulate m gain :=
  accumulation_ratchets m gain

/-- **Both fates are realized.** A start that resets to the corner forever
    (`everHits 4 6 1 3` — the amnesia fate) and one that bounces forever
    (`¬ everHits 4 6 0 1` — the grit fate). One of the two, and each is real. -/
theorem both_fates_are_realized : stuckFate 4 6 1 3 ∧ bounceFate 4 6 0 1 :=
  ⟨dvd_4x6_from_1_3_hits, dvd_4x6_from_0_1_never⟩

/-- **The DVD logo is the frontier** (headline). The two fates — corner-forever
    (periodic reset to the origin: amnesia) and bounce-forever (never resetting:
    grit) — are mutually exclusive (one of the two), and each is eternal (infinity
    is guaranteed either way). The screensaver is the amnesia/grit frontier: you
    do not get both poles, and you do not get a clean end. -/
theorem dvd_logo_is_the_frontier (W H x0 y0 : Nat) :
    ¬ (stuckFate W H x0 y0 ∧ bounceFate W H x0 y0)
      ∧ (stuckFate W H x0 y0 → ∃ t, ∀ k, cornerHit W H x0 y0 (t + W * H * k) = true)
      ∧ (bounceFate W H x0 y0 → ∀ t, cornerHit W H x0 y0 t ≠ true) :=
  ⟨fates_are_exclusive W H x0 y0,
   stuck_recurs_forever W H x0 y0,
   bounce_is_forever W H x0 y0⟩

end Gnosis.Body.DvdLogoIsTheFrontier
