import Init
import Gnosis.AckermannFunction
import Gnosis.CausalDiamond
import Gnosis.AckermannLightConeBridge
import Gnosis.KnotRopelengthComplexity
import Gnosis.SuperpolynomialFront

/-
  FrontConeUnification.lean
  =========================

  Ties the `SuperpolynomialFront` abstraction back into the light cone itself.

  Place any front `S` on the TIME axis of a 1+1D event and a polynomial spatial
  displacement on the space axis: `{ time := S n, space := n^k }`. Whenever the
  front outpaces the polynomial (`n^k < S n`), that event is STRICTLY TIMELIKE
  (`interval < 0`) — inside the light cone. So the light-theorem geometry
  (`AckermannLightConeBridge`) applies UNIFORMLY to all three superpolynomial
  fronts: `2^n`, the NP ropelength `1 + 2^n`, and the Ackermann ceiling `A(n)`.

  Net: "computable stays causal" and "rope = betti = light = exp>poly" are the
  same picture — a polynomial event below a superpolynomial front is subluminal,
  whichever front you choose.

  HONEST SCOPE (unchanged): this is the true geometry of superpolynomial fronts;
  NOT a P ≠ NP proof — the class↔front identification relativizes (BGS).

  Init + the program. Zero `sorry`, zero new `axiom`.
-/

namespace FrontConeUnification

open AckermannFunction
open Gnosis.CausalDiamond
open AckermannLightConeBridge
open KnotRopelengthComplexity
open SuperpolynomialFront

/-- **General subluminal ⟹ timelike.** If a spatial displacement `s` is below a
    temporal extent `t` (`s < t`), the event `{ time := t, space := s }` is
    strictly timelike — inside the light cone. (Generalizes
    `AckermannLightConeBridge.subluminal_is_strictly_timelike` off the Ackermann
    ceiling to any temporal extent.) -/
theorem subluminal_timelike (s t : Nat) (h : s < t) :
    intervalSquared origin { time := (t : Int), space := (s : Int) } < 0 := by
  rw [interval_origin]
  have hnat : s * s < t * t := Nat.mul_self_lt_mul_self h
  have hint : (s : Int) * s < (t : Int) * t := by exact_mod_cast hnat
  omega

/-- **A polynomial event below a superpolynomial front is timelike.** For any
    front `S` that outpaces every polynomial and any degree `k`, there is an `n`
    at which the event `{ time := S n, space := n^k }` is strictly inside the
    light cone. -/
theorem poly_below_front_timelike {S : Nat → Nat} (hS : OutpacesPolys S) (k : Nat) :
    ∃ n, intervalSquared origin
      { time := (S n : Int), space := ((n ^ k : Nat) : Int) } < 0 := by
  obtain ⟨n, hn⟩ := hS k
  exact ⟨n, subluminal_timelike (n ^ k) (S n) hn⟩

/-- **Three fronts, one cone.** Against each of the three superpolynomial fronts
    — the exponential `2^n`, the NP ropelength `1 + 2^n`, and the Ackermann
    luminal ceiling `A(n)` — a polynomial event is eventually strictly timelike.
    The light-theorem geometry is one and the same across all three. -/
theorem three_fronts_one_cone (k : Nat) :
    (∃ n, intervalSquared origin
        { time := ((2 ^ n : Nat) : Int), space := ((n ^ k : Nat) : Int) } < 0)
    ∧ (∃ n, intervalSquared origin
        { time := (npRopelength n : Int), space := ((n ^ k : Nat) : Int) } < 0)
    ∧ (∃ n, intervalSquared origin
        { time := (ackermannDiag n : Int), space := ((n ^ k : Nat) : Int) } < 0) :=
  ⟨poly_below_front_timelike exp_outpaces k,
   poly_below_front_timelike rope_outpaces k,
   poly_below_front_timelike ackermann_outpaces k⟩

end FrontConeUnification
