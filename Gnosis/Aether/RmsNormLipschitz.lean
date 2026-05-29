import Init

/-!
# RMSNorm Lipschitz constant `K_rms` (Rustic Church, Init-only)

This module **certifies the conservative RMSNorm Lipschitz constant** that the
amplituhedron τ-estimator currently uses as an *assumed* engineering bound. It
promotes that bound — `K_rms := ‖w‖∞ / √eps` — from "assumed/bounded (the
weakest link)" to "Lean-proven uniform gain bound for the final RMSNorm's
diagonal map."

Runtime source: `open-source/gnosis/distributed-inference/src/amplituhedron_tau.rs`,
`k_rms_conservative_bound` (`K_rms = ‖w‖∞ / √eps`, the worst case reached only as
`rms(x) → √eps`, i.e. `x → 0`). Doc: `docs/AMPLITUHEDRON_TAU_ESTIMATION.md`.

## The math (and the bridge rule)

The final RMSNorm is the map `y_i = x_i · w_i / rms(x)` with
`rms(x) = √(mean(x²) + eps)`. Written `y = D(x)·x`, the diagonal gain on
coordinate `i` is `g_i(x) = w_i / rms(x)`, so its magnitude is
`|g_i(x)| = |w_i| / rms(x)`. The only physical fact needed is

```text
  mean(x²) ≥ 0   ⇒   rms(x) = √(mean(x²) + eps) ≥ √eps      for ALL x.
```

Hence `|g_i(x)| = |w_i| / rms(x) ≤ |w_i| / √eps ≤ ‖w‖∞ / √eps`, independent of
`x`. So `K_rms := ‖w‖∞ / √eps` bounds *every* diagonal gain — an `x`-uniform
Lipschitz/gain bound for the diagonal map. The worst case is reached only as
`x → 0`; for any real post-prefill residual the true gain is far smaller, so the
bound OVER-estimates and can only ever shrink the admissible band — a spurious
MISS, never a spurious admit.

**The bridge rule (what stays OUTSIDE the theorem).** The float `sqrt` is never
computed here. `√eps` enters as an OPAQUE positive parameter `r : Nat` (Int-scaled
magnitude), and `rms(x)` as an opaque parameter `rmsVal : Nat`. The single
certified premise is `hrms : r ≤ rmsVal` — *exactly* the physical fact
`√eps ≤ rms(x)` above. We also expose `r_le_rmsVal_of_eps_le_sq`, which DERIVES
`r ≤ rmsVal` from the squared form `eps ≤ rmsVal²` together with `r·r ≤ eps`
(`√eps`'s defining inequality, the bridge), so the premise is not free-floating —
but taking `r ≤ rmsVal` as the certified premise is the clean bridge and is what
the gain theorems consume.

## Modeling choice (Nat magnitudes — and why it is honest)

Weights are `w : Fin n → Int` (Int-scaled, faithful to the runtime's `f32`
weights up to the shared scale). We work in **Nat magnitudes** via `Int.natAbs`,
because the only quantity the gain bound reads is `|w_i|`, and the division
monotonicity lemmas the chain needs (`Nat.div_le_div_left` antitone-in-divisor,
`Nat.div_le_div_right` monotone-in-numerator) live cleanly in `Nat` in `Init`.
This is faithful: `|w_i| = (w_i).natAbs` exactly (`Int.natAbs` is the magnitude),
and `K_rms` is a ratio of magnitudes, so no sign information is lost. The
`‖w‖∞` is modelled as a parameter `wInf : Nat` with the per-coordinate hypothesis
`hw : ∀ k, (w k).natAbs ≤ wInf` — i.e. `wInf` is *an upper bound on the sup-norm*
(the runtime computes the exact max; any valid upper bound makes the gain bound
sound, and the exact max is the tightest such `wInf`).

Init-only discipline per `RUSTIC_CHURCH.md`: `import Init`, no Mathlib, no
`omega`, no `simp`/`decide` on open-variable goals. `decide` appears only on
CLOSED goals (the worked example / antitheorem literals). Division monotonicity
is the named cookbook chain `Nat.div_le_div_left` / `Nat.div_le_div_right`.
`#print axioms` is `propext` only.
-/

namespace Gnosis
namespace Aether
namespace RmsNormLipschitz

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The diagonal gain magnitude (Int weights, Nat magnitudes)
-- ═══════════════════════════════════════════════════════════════════════

/-- Magnitude of the RMSNorm diagonal gain on one coordinate, in Nat scale:
`|w_i| / rmsVal` where `|w_i| = (w i).natAbs` and `rmsVal` is the Int-scaled
`rms(x)` (an opaque parameter — the float `sqrt`/`mean` stay OUTSIDE per the
bridge rule). This is `|g_i(x)| = |w_i| / rms(x)`. -/
def gainMag {n : Nat} (w : Fin n → Int) (i : Fin n) (rmsVal : Nat) : Nat :=
  (w i).natAbs / rmsVal

/-- The certified worst-case gain bound `K_rms = ‖w‖∞ / √eps`, in Nat scale:
`wInf / r` where `wInf` bounds the sup-norm `‖w‖∞` and `r` is the Int-scaled
`√eps` (opaque, positive). This is exactly the runtime's
`k_rms_conservative_bound = ‖w‖∞ / √eps`. -/
def kRms (wInf r : Nat) : Nat := wInf / r

-- ═══════════════════════════════════════════════════════════════════════
-- §2  The bridge: `√eps ≤ rms(x)` from `eps ≤ rms(x)²`
-- ═══════════════════════════════════════════════════════════════════════

/-- **The √-bridge as an honest derivation (optional input to the gain bound).**
The certified premise the gain theorems consume is `r ≤ rmsVal` (`√eps ≤ rms(x)`).
This lemma shows that premise is not free-floating: it FOLLOWS from the squared
inequality `eps ≤ rmsVal²` (which holds because `mean(x²) ≥ 0` ⇒
`rms(x)² = mean(x²) + eps ≥ eps`) together with `r·r ≤ eps` (the defining
inequality of `r = √eps` at this Int scale — the float `sqrt` itself stays
OUTSIDE, only this inequality crosses the bridge). Chain: `r·r ≤ eps ≤ rmsVal·rmsVal`,
then the square-monotonicity contrapositive — if `rmsVal < r` then
`rmsVal·rmsVal < r·r` (`Nat.mul_lt_mul_of_lt_of_le`), contradicting `r·r ≤ rmsVal·rmsVal`.
Closed via the no-`omega` `Nat.lt_or_ge` split below; axiom-free. -/
theorem r_le_rmsVal_of_eps_le_sq {r eps rmsVal : Nat}
    (hr : 0 < r)
    (hsqrt : r * r ≤ eps)
    (heps : eps ≤ rmsVal * rmsVal) :
    r ≤ rmsVal := by
  -- r*r ≤ rmsVal*rmsVal, and squaring is strictly monotone, so r ≤ rmsVal.
  have hsq : r * r ≤ rmsVal * rmsVal := Nat.le_trans hsqrt heps
  -- Contrapositive: if rmsVal < r then rmsVal*rmsVal < r*r, contradiction.
  match Nat.lt_or_ge rmsVal r with
  | Or.inr hge => exact hge
  | Or.inl hlt =>
      -- rmsVal < r ⇒ rmsVal*rmsVal < r*r (strict square monotonicity)
      have hstrict : rmsVal * rmsVal < r * r :=
        Nat.mul_lt_mul_of_lt_of_le hlt (Nat.le_of_lt hlt) hr
      exact absurd hsq (Nat.not_le_of_lt hstrict)

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The gain bound (the certificate core)
-- ═══════════════════════════════════════════════════════════════════════

/--
**`gain_bounded` — every diagonal gain is ≤ `K_rms`, the certificate core.**
Given a per-coordinate sup-norm bound `|w i| ≤ wInf` and the certified physical
premise `r ≤ rmsVal` (`√eps ≤ rms(x)`) with `r > 0`, the gain magnitude on
coordinate `i` is bounded by `K_rms = wInf / r`:

```text
  gainMag w i rmsVal  =  |w i| / rmsVal  ≤  |w i| / r  ≤  wInf / r  =  kRms wInf r.
```

Two named cookbook steps:
* `Nat.div_le_div_left` (antitone in divisor): dividing by the LARGER `rmsVal`
  gives no more than dividing by the smaller `r` — this is where `r ≤ rmsVal`
  (the `√eps ≤ rms(x)` fact) does its work;
* `Nat.div_le_div_right` (monotone in numerator): the smaller numerator `|w i|`
  divides to no more than `wInf`.

Chained by `Nat.le_trans`. No `omega`. -/
theorem gain_bounded {n : Nat} (w : Fin n → Int) (i : Fin n)
    (wInf r rmsVal : Nat)
    (hw : (w i).natAbs ≤ wInf)
    (hr : 0 < r)
    (hrms : r ≤ rmsVal) :
    gainMag w i rmsVal ≤ kRms wInf r := by
  unfold gainMag kRms
  -- Step 1 (antitone in divisor): |w i| / rmsVal ≤ |w i| / r.
  have hdiv : (w i).natAbs / rmsVal ≤ (w i).natAbs / r :=
    Nat.div_le_div_left hrms hr
  -- Step 2 (monotone in numerator): |w i| / r ≤ wInf / r.
  have hnum : (w i).natAbs / r ≤ wInf / r :=
    Nat.div_le_div_right hw
  exact Nat.le_trans hdiv hnum

/--
**`k_rms_is_uniform_bound` — `K_rms` is `x`-uniform across all coordinates.**
The bound `kRms wInf r` (the runtime's `K_rms = ‖w‖∞ / √eps`) bounds the gain on
EVERY coordinate `i`, for EVERY `rms(x)` value `rmsVal ≥ r`. The bound on the
right does not depend on `i` or on `rmsVal` — it is the single Lipschitz constant
for the entire diagonal map, independent of the input `x`. This is exactly the
"independent of `x`" claim the runtime relies on. -/
theorem k_rms_is_uniform_bound {n : Nat} (w : Fin n → Int)
    (wInf r : Nat)
    (hw : ∀ k, (w k).natAbs ≤ wInf)
    (hr : 0 < r) :
    ∀ (i : Fin n) (rmsVal : Nat), r ≤ rmsVal →
      gainMag w i rmsVal ≤ kRms wInf r := by
  intro i rmsVal hrms
  exact gain_bounded w i wInf r rmsVal (hw i) hr hrms

/-- **Tightness at the worst case.** The bound is attained (as equality at the
worst-case `rms(x) = √eps`, i.e. `rmsVal = r`) for the coordinate whose magnitude
equals the sup-norm: if `|w i| = wInf` and `rmsVal = r`, the gain equals `K_rms`.
This certifies the bound is the WORST case (reached only as `x → 0`), not a loose
over-estimate at that point. -/
theorem gain_attains_k_rms {n : Nat} (w : Fin n → Int) (i : Fin n)
    (wInf r : Nat)
    (hwEq : (w i).natAbs = wInf) :
    gainMag w i r = kRms wInf r := by
  unfold gainMag kRms
  exact congrArg (· / r) hwEq

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Concrete worked example (the runtime's own unit-test numbers, scaled)
-- ═══════════════════════════════════════════════════════════════════════

/-! The runtime test `k_rms_is_winf_over_sqrt_eps` uses `‖w‖∞ = 3`, `eps = 0.25`,
giving `√eps = 0.5` and `K_rms = 3 / 0.5 = 6`. Scaled by 2 to integers:
`wInf = 8`, `r (=√eps) = 2`, and we serve a coordinate with `|w i| = 8` at a
typical post-prefill `rmsVal = 4` (`rms(x) = 2·√eps`). The gain
`8 / 4 = 2 ≤ 8 / 2 = 4 = K_rms` holds — the bound dominates, with slack because
`rmsVal > r`. Routed through `gain_bounded`, so it is a live carrier of the
general theorem. -/

/-- A single-coordinate weight vector with `|w 0| = 8` (the scaled `‖w‖∞`). -/
def exW : Fin 1 → Int := fun _ => 8

/-- **The worked serve.** With `wInf = 8`, `r = √eps = 2`, `rmsVal = 4`, the gain
on coordinate 0 is `8/4 = 2`, bounded by `K_rms = 8/2 = 4`. Routes through
`gain_bounded`. -/
theorem ex_gain_bounded :
    gainMag exW ⟨0, by decide⟩ 4 ≤ kRms 8 2 :=
  gain_bounded exW ⟨0, by decide⟩ 8 2 4
    (by decide) (by decide) (by decide)

/-- The worked numbers compute as claimed: gain `= 2`, `K_rms = 4`. Closed
`decide` on the literal Nat divisions. -/
theorem ex_gain_values :
    gainMag exW ⟨0, by decide⟩ 4 = 2 ∧ kRms 8 2 = 4 := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Antitheorem (Sardis parity: the `√eps ≤ rms(x)` premise is load-bearing)
-- ═══════════════════════════════════════════════════════════════════════

/--
**Sharpness: dropping `r ≤ rmsVal` (`√eps ≤ rms(x)`) breaks the bound.** The
premise `hrms : r ≤ rmsVal` is not decorative. If `rms(x)` is allowed to fall
BELOW `√eps` (`rmsVal < r`) — the physically impossible regime the bridge fact
`mean(x²) ≥ 0` rules out — the gain EXCEEDS `K_rms`. Witness: `wInf = 8`, `r = 4`
(so `K_rms = 8/4 = 2`), but `rmsVal = 2 < r`, giving gain `8/2 = 4 > 2 = K_rms`.

This is the formal signature of "a name that liveth, and is dead": a τ-estimator
that trusted `K_rms = ‖w‖∞/√eps` while letting `rms(x) < √eps` would UNDER-estimate
the gain and could admit a wrong token. The premise `√eps ≤ rms(x)` (proved for
ALL `x` by `mean(x²) ≥ 0`) is exactly what forbids that — it is load-bearing.
Closed `decide` over the literal Nat divisions. -/
theorem gain_exceeds_k_rms_when_premise_dropped :
    ¬ (gainMag exW ⟨0, by decide⟩ 2 ≤ kRms 8 4) := by
  -- gain = 8/2 = 4, kRms = 8/4 = 2, and ¬ (4 ≤ 2).
  show ¬ ((8 : Int).natAbs / 2 ≤ (8 : Nat) / 4)
  decide

end RmsNormLipschitz
end Aether
end Gnosis
