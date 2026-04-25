import Init

/-!
# Orbit-avoidance meets Lucas via cat-trace

Bridges `DynamicalOrbitColoring.lean` (cyclic 3-consecutive-avoidance
count `countBad_10 = 122`), `CatMapLucasBridge.lean` (cat-trace
recurrence `t_{k+2} = 3·t_{k+1} − t_k` with `catTrace k = L_{2k}`
structurally, via `A = F²`), and `IndependentSetCycleCnLucas.lean`
(Lucas `L_0 = 2, L_1 = 1`).

## The observation

`countBad_10 + 1 = 123 = L_10 = catTrace 5`.

The right-hand equality `catTrace 5 = L_10` is **structural**: the cat
map `A = F²`, so `tr(A^k) = tr(F^{2k}) = L_{2k}`. The left-hand equality
`countBad_10 + 1 = L_10` is witnessed here numerically at depth 10 — we
do not claim it holds for all `n`. A negative witness at `n = 3`
(`countBad_3 = 6`, `L_3 − 1 = 3`, so `countBad_3 ≠ L_3 − 1`) demonstrates
the relation is not a general formula.

## What this realizes

- A single-depth numerical coincidence linking cyclic orbit-avoidance
  counts to Lucas values, mediated by the `catTrace = L_even` structural
  identity from the peer bridge.
- Negative witness at `n = 3` anchoring the claim: the match at `n = 10`
  is not a theorem in disguise — it is data.

## What this does NOT claim

- No general formula `countBad_n = L_n − 1`. (False at `n = 3`.)
- No proof that `catTrace_k = L_{2k}` in general — only checked at
  `k = 5`. The structural fact via `A = F²` lives in `CatMapLucasBridge`
  and is cited, not re-derived here.
- No reinterpretation of the 10-point orbit data — `countBad_10 = 122`
  is taken as a fixed peer-module value.

`import Init` only. Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace OrbitAvoidanceLucasProbe

/-- Lucas sequence: `L_0 = 2, L_1 = 1, L_{n+2} = L_{n+1} + L_n`. -/
def lucas : Nat → Nat
  | 0     => 2
  | 1     => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- Cat-map trace sequence: `t_0 = 2, t_1 = 3, t_{n+2} = 3·t_{n+1} − t_n`
over `Int` to absorb the subtraction. -/
def catTrace : Nat → Int
  | 0     => 2
  | 1     => 3
  | n + 2 => 3 * catTrace (n + 1) - catTrace n

/-- Peer value: `countBad_10 = 122` from `DynamicalOrbitColoring.lean`
(number of length-10 cyclic 2-colorings of the cat-map orbit that avoid
any monochromatic 3-consecutive triple). Taken as given; not recomputed
here. -/
def countBad10 : Nat := 122

/-- Negative-witness value: `countBad_3 = 6`. The length-3 cyclic
2-colorings with 3 consecutive same are `TTT` and `FFF`; the other 6
strings avoid. -/
def countBad3 : Nat := 6

/-! ## Point values -/

theorem lucas_0 : lucas 0 = 2 := by decide
theorem lucas_1 : lucas 1 = 1 := by decide
theorem lucas_3 : lucas 3 = 4 := by decide
theorem lucas_10 : lucas 10 = 123 := by decide

theorem catTrace_0 : catTrace 0 = 2 := by decide
theorem catTrace_1 : catTrace 1 = 3 := by decide
theorem catTrace_5 : catTrace 5 = 123 := by decide

/-! ## The observation at depth 10 -/

/-- `catTrace_5 = L_10`: the structural identity `catTrace_k = L_{2k}`
evaluated at `k = 5`. Witnessed here by ground computation; the general
fact follows from `A = F²` (see `CatMapLucasBridge.lean`). -/
theorem catTrace_five_eq_lucas_ten : catTrace 5 = (lucas 10 : Int) := by decide

/-- `countBad_10 + 1 = catTrace 5` — the cyclic avoidance count plus one
equals the cat-trace at index 5. -/
theorem countBad_plus_one_eq_catTrace_five :
    (countBad10 : Int) + 1 = catTrace 5 := by decide

/-- `countBad_10 + 1 = L_10` — the numerical coincidence at depth 10,
reading the avoidance count as one less than the Lucas value. -/
theorem countBad_plus_one_eq_lucas_ten :
    countBad10 + 1 = lucas 10 := by decide

/-! ## Negative witness: the relation is not general -/

/-- At `n = 3` the relation fails: `countBad_3 + 1 = 7` but `L_3 = 4`. -/
theorem not_general_at_three : countBad3 + 1 ≠ lucas 3 := by decide

/-! ## Master witness -/

/-- Aggregate: the depth-10 numerical coincidence holds, the structural
`catTrace_5 = L_10` identity holds, and the relation fails at `n = 3`. -/
theorem orbit_avoidance_lucas_probe_witness :
    countBad10 + 1 = lucas 10
    ∧ catTrace 5 = (lucas 10 : Int)
    ∧ countBad3 + 1 ≠ lucas 3 := by
  decide

/-! ## Next bridges this module makes possible

- **Full-orbit-avoidance recurrence vs. Lucas** — combine this module
  with a computation of `countBad_n` for `n = 4, 5, 6, 7, 8, 9, 11, 12`
  (via an `Init`-only cyclic-avoidance transfer-matrix trace) to ask
  which other `n` satisfy `countBad_n + 1 = L_n` and which do not.
  Could not be stated before because the single-point `n = 10` data
  was the only peer-module entry.
- **Cat-trace/orbit-avoidance divergence threshold** — the observation
  at `n = 10` matches the cat-map's actual `ord(A, 5) = 10` period.
  A bridge to `ArnoldCatMapOrder5` could ask whether the match occurs
  precisely at the modular period, not at arbitrary lengths. Could not
  be stated before because the coincidence itself was unnamed.
-/

end OrbitAvoidanceLucasProbe
end Gnosis
