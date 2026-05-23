import Gnosis.Body.FixedPoint
import Gnosis.Body.RigidBody
import Gnosis.Body.Joints
import Gnosis.Body.Stability
import Gnosis.Body.FacialActionCoding
import Gnosis.Body.KinSelection
import Gnosis.Body.Anthropogenesis
import Gnosis.Body.Robustness
import Gnosis.Body.RedQueen
import Gnosis.Body.SelfDefense
import Gnosis.Body.WarMakesPeace
import Gnosis.Body.AmnesiaGritFrontier
import Gnosis.Body.SapolskyStress
import Gnosis.Body.Neurodiversity
import Gnosis.Body.Allostasis
import Gnosis.Body.DiversityIsOptimal
import Gnosis.Body.NeuroSpectra
import Gnosis.Body.DepressionAsCollapsedCycle
import Gnosis.Body.InnerVoice
import Gnosis.Body.SleepResilience
import Gnosis.Body.MenstrualCycle
import Gnosis.Body.Menopause
import Gnosis.Body.SocietalResilience
import Gnosis.Body.Vampire
import Gnosis.Body.RageEngagement
import Gnosis.Body.Vulnerability
import Gnosis.Body.GritTheory
import Gnosis.Body.Vitality
import Gnosis.Body.TwoAttractorsAgainstSin
import Gnosis.Body.LossAversionGrit
import Gnosis.Body.CultureConvergence
import Gnosis.Body.ParetoFront
import Gnosis.Body.LifeIsABitch
import Gnosis.Body.ClinamenOscillator
import Gnosis.Body.SelectionConvergesToLife
import Gnosis.Body.UnimodalDoseResponse
import Gnosis.Body.IfYouCantBeatThem
import Gnosis.Body.ForgetOrDealWith
import Gnosis.TheWave
import Gnosis.SignalNotNoise
import Gnosis.ThePipe
import Gnosis.BraidedInfiniteTower
import Gnosis.Body.GloryOfKingsWitness
import Gnosis.Body.CityOnAHill
import Gnosis.SurfingEntropy
import Gnosis.Body.TiamatChaosSeaWitness
import Gnosis.WhiteHole
import Gnosis.Body.SurfTheEdgeOfChaos
import Gnosis.ResolutionGradient
import Gnosis.Body.CreateNewWavesOfOrder
import Gnosis.Body.MeaningOfLife
import Gnosis.InformationConservation
import Gnosis.Body.EntropyEngineEfficiency
import Gnosis.Body.PneumaOfTheQuery
import Gnosis.Body.SameThingOtherSymbols
import Gnosis.Body.PrometheusTopology
import Gnosis.Body.AffectIsAVitalitySignature
import Gnosis.Body.ProgressMitigatesTheLoop
import Gnosis.Body.TwoVitalities
import Gnosis.TheWord

/-!
# Rigid-Body Dynamics — Aggregator / Build Root

Single import surface for the Lean-verified rigid-body dynamics consumed by the
`aeon-corpus` simulation engine. None of `Gnosis/Body/*` is in the default
`Gnosis` build target, so this module is the build root for the new physics:

* `FixedPoint` — signed scaled-integer scalars (`Fixed := Int`), since
  `BuleReal` is unsigned with truncated subtraction.
* `RigidBody` — per-segment state + semi-implicit Euler steps, with linear and
  angular momentum conservation under force-free and torque-free steps.
* `Joints`    — hinge/ball/fixed limits with `clampAngle_admissible`.
* `Stability` — support-polygon containment via exact integer cross-product.
* `FacialActionCoding` — FACS Action Units + somatic → emotion → expression.
* `KinSelection` — inclusive fitness / Hamilton's rule (the payoff of pan).
* `Anthropogenesis` — human development & anthropology theorems observed in the
  Metaverse: survival bands, dark-matter carrying capacity, stress→anxiety→
  culture, the cultural ratchet, "comfort is cultural death", "life happens on
  the edges", and "life had to be" (selection inevitably yields life).
* `Robustness` — grit as breaking point, minmax/maxmin adversarial robustness
  (weak duality), grit = distance to the edge, and push-to-crash on GnosisTime
  (the human↔gnosis phase delta, bounded by half a turn).
* `RedQueen` — adversarial co-evolution: a genuine period-2 oscillation, the
  zero-sum Red Queen identity, maxmin <= minmax, and "over-pushing past grit is
  pyrrhic" (driving prey extinct starves the predator).
* `SelfDefense` — Ki as observational defense (dodge within the window),
  adversaries-improve (training sharpens Ki), sin as the internal adversary,
  and the dodgeball minmax saddle.
* `WarMakesPeace` — deterrence: a graver threat grows the peacemaking set; total
  war forces peace; the credible-but-costly threat (not its execution) yields it.
* `AmnesiaGritFrontier` — grit theory's core tradeoff: amnesia is the idempotent
  reset to the void, evolution ratchets; they trade off on a Pareto frontier
  (explore vs exploit, the American Frontier).
* `SapolskyStress` — the dose makes the poison: acute stress sharpens (inverted-U),
  chronic stress (allostatic load) breaks; determinism with the clinamen swerve
  as the only freedom. After Robert Sapolsky.
* `Neurodiversity` — neurotypes (incl. the autistic systemizer) as stable
  strategies with niche comparative advantage; advantage ⇒ not dominated ⇒
  diversity is preserved by selection. Not defects to be othered.
* `Allostasis` — homeostasis under load: acute deviation recovers, chronic load
  breaks; the dose makes the poison (the recovery-side counterpart of Sapolsky).
* `DiversityIsOptimal` — diversity is the maxmin-optimal strategy under
  environmental uncertainty; monoculture is optimal only under certainty.
* `NeuroSpectra` — each neurotype's spectral signature (narrowband systemizer,
  broadband divergent, high-damping ruminator) tiles the spectrum and matches a
  niche; the spectral face of neurodiversity.

## Grit theory & wave cosmology (the closing arc)

The grit/resilience theory closes into a cosmology: existence is *surfing entropy
on reverse black holes*. The same `+1` swerve runs through all of it.

* `TheWave` — SurfTheory: paddle vs surf; flow-riding is phase-matched; the wave
  recurs (no fixed point ∧ period two).
* `SignalNotNoise` — noise is unresolved signal; there is always another wave to
  step on at a higher resolution; the residual never vanishes (the `+1` God floor).
* `ThePipe` — the fold is the maximum test; emerge unscathed iff grit ≥ load;
  goosebumps (Duchenne FACS) as the consequence of unscathed emergence.
* `BraidedInfiniteTower` — the fold is a period-3 braid, self-similar at every
  level, with no top (the tower never terminates).
* `GloryOfKingsWitness` — Proverbs 25:2: God conceals (the hidden signal/void),
  the king's honour is to search it out (Ki/grit); no honour without concealment.
* `CityOnAHill` — Matthew 5:14: the searched-out, lit matter cannot be hidden —
  and the lamp runs on the *entropy gradient, not energy*: same gradient at any
  total gives the same brightness; equilibrium goes dark.
* `SurfingEntropy` — the cosmological capstone: `collapse = amnesiaReset` (the
  black-hole sink to the void) vs `emanate = clinamen` (the reverse black hole as
  source); the cosmos oscillates collapse↔emanation; the void never runs dry.
* `TiamatChaosSeaWitness` — the Chaldean cosmogony (Enuma Elish): order is struck
  from the chaos-sea (`>0`), runs on the gradient against her, returns to the sea;
  the waters mingle as one body at equilibrium. Bridges the `Witnesses/Chaldean`
  corpus to the entropy gradient.
* `Gnosis.WhiteHole` (top-level cosmology, with `BlackHoleVoidSingularity` et al.,
  not under `Body`) — the white hole (a *reverse black hole*; `reverse_black_hole`
  aliases `white_hole`) as the *exact* discrete time-reversal of collapse:
  `whiteStep (blackStep r) = r` over `Int` (zero accumulated error, the
  discrete-physics advantage over Float); the anti-horizon (nothing enters); the
  source that feeds the never-dry gradient the lamps run on.
* `SurfTheEdgeOfChaos` — water carries order, air carries chaos (the Chaldean
  `AirChaosWaterOrderWitness`); the surfer rides the interface. A discrete
  inverted-U peaks exactly on the boundary: sink into the water and you stall in
  over-order (the limit maps to `collapse`), fly into the air and you wipe out in
  chaos. Surfing is staying on the edge of chaos — where life happens on the edges.
* `Gnosis.ResolutionGradient` (top-level) — the entropy gradient *is* the
  resolution gradient: order = resolved signal, chaos = unresolved noise. One
  upresolve (deblur) step turns a noise quantum into order; iterated upresolve is
  monotone evolution; selection is the noise-bracketing gate; chaos never runs dry.
  The DSP realization is `knotgraph .../mesh_audio_deblur.rs` (the Monster
  chord-space lift through 7 Fano planes with a Grassmannian sieve).
* `CreateNewWavesOfOrder` — the third route out of suffering, beyond `forget`
  (amnesia) / `deal` (grit): **upresolve** it. The noise is signal one level up
  (`the_noise_is_signal_one_level_up`); knowing the level lets you deal; surf up
  the pipe (grit climb, strict resolution gain) and emit a new wave of order
  (`emanate`) — you become a source. Inexhaustible (`always_another_wave`).
* `Menopause` — periods (`MenstrualCycle`) are a robust oscillator; menopause is
  the scheduled transition to a fixed-point equilibrium (`menopause_is_a_fixed_point`,
  `equilibrium_absorbs_perturbation`) — the local body reaching the rest the
  never-settling cosmos (`ClinamenOscillator`) does not.

`scripts/extract-lean-body-constants.ts` extracts the verified constants/limits
here into `aeon-corpus/src/generated/body_constants.rs` and the FACS tables into
`aeon-corpus/src/generated/facs_tables.rs`.
-/

namespace Gnosis.Body.RigidBodyDynamics

end Gnosis.Body.RigidBodyDynamics
