# Gnosis

Parent: [Gnosis Math](../README.md)

`Gnosis/` contains the Lean modules exported by the `Gnosis` aggregate import.
Most files are single-claim or single-domain proof kernels, while subdirectories
group larger families of related claims.

## Key Modules

- [Apotheosis/](./Apotheosis/README.md) — mechanical-brain carrier definitions
  migrated from the legacy `open-source/gnosis` Lean tree into the `gnosis-math`
  hierarchy, with explicit axiom boundaries for semantic claims.
- [TreeShapes.lean](./TreeShapes.lean), [GeoShapes.lean](./GeoShapes.lean),
  [RemainingNatureShapes.lean](./RemainingNatureShapes.lean),
  [ImpossibleFireworkShapes.lean](./ImpossibleFireworkShapes.lean),
  [ManmadeShapes.lean](./ManmadeShapes.lean), and
  [SceneShapeLayer.lean](./SceneShapeLayer.lean) — finite shape catalog carriers
  migrated from the legacy `open-source/gnosis/lean/Lean/Gnosis` tree.
- [RootEnergyMass.lean](./RootEnergyMass.lean) — finite root-placement and
  mass-accounting carrier migrated from the same legacy shape stack.
- [EarthTilingTopology.lean](./EarthTilingTopology.lean) — finite
  storms-watch-style earth mesh: bounded lat/lon tiles, antimeridian wrapping,
  occupied witness cells, and direct spawn certificates.
- [ScribalStandingWave.lean](./ScribalStandingWave.lean) — shared finite
  contract for Thoth-style mechanical/scribal interfaces: canonical failure
  boundary claims, viable audited-use claims, event-log projection to boundary
  input, executable response-envelope validation, strict multi-turn audit-trace
  folding for Thoth memory, Body Politick admission bridging into scribal
  envelopes, reusable `ScribalStandingWaveMode`, and Rust-facing
  boundary/certificate records for assisted reasoning, hallucination rejection,
  source-substitution rejection, and failure-audit support.
- [ScribalStandingWave/PayloadTraceLineage.lean](./ScribalStandingWave/PayloadTraceLineage.lean)
  — companion payload-trace lineage contract for Body Politick-derived Thoth
  memory: generated-content hashes remain visible audit observations while
  trace authority and theorem lineage reduce to the folded child envelopes.
- [ScribalStandingWave/TaggedTranscriptMode.lean](./ScribalStandingWave/TaggedTranscriptMode.lean)
  — product-facing default transcript mode for Thoth output: turns are tagged
  with scribal audit envelopes by default, and raw escape remains explicit and
  non-authoritative.
- [ScribalStandingWave/TranscriptAuditTrace.lean](./ScribalStandingWave/TranscriptAuditTrace.lean)
  — CRDT-shaped ordered audit memory for tagged transcript sessions: replicas
  merge turn audit atoms monotonically, preserve raw escape gaps as visible
  observations, and reject source-authority claims.
- [ScribalStandingWave/TranscriptCrdtLaws.lean](./ScribalStandingWave/TranscriptCrdtLaws.lean)
  and [TranscriptDampeningAmnesia.lean](./ScribalStandingWave/TranscriptDampeningAmnesia.lean)
  — canonical CRDT algebra plus bounded recall for transcript audit atoms:
  normalized joins are idempotent/commutative/associative, old turns dampen
  into lower-weight memory, and raw escapes become explicit amnesia gaps.
- [ScribalStandingWave/RecallPromotionGate.lean](./ScribalStandingWave/RecallPromotionGate.lean)
  — promotion gate for dampened transcript recall: fresh tagged corroboration
  can restore active weight, while stale evidence and raw escape gaps cannot.
- [ScribalStandingWave/MemoryBudgetScheduler.lean](./ScribalStandingWave/MemoryBudgetScheduler.lean)
  — finite active-memory scheduler for Thoth recall: promoted fresh tagged
  atoms outrank recent active atoms, dampened atoms remain available when
  budget permits, and amnesia gaps stay outside active context.
- [ScribalStandingWave/ThothMemorySession.lean](./ScribalStandingWave/ThothMemorySession.lean)
  — full product-session package for tagged Thoth memory: turns fold into CRDT
  audit trace, recall view, promotion gate, and scheduled active memory while
  preserving non-authority after merges and raw escapes.
- [ScribalStandingWave/ThothMemoryAdapter.lean](./ScribalStandingWave/ThothMemoryAdapter.lean)
  — Thoth-facing adapter for product callers: transcript inputs default to
  tagged audit memory, raw output requires an explicit escape request, and
  consumed generation context is derived from scheduled recall rather than
  accumulated output.
- [ThothConversationAntiQueue.lean](./ThothConversationAntiQueue.lean) —
  internal conversation task/todo antiqueue for Thoth: open questions,
  argument obligations, affect stalls, unresolved residue, and boundaries are
  held as self-accountability promises only, never as external enforcement over
  another speaker. It also formalizes compatible release classes and a bounded
  next-task pressure selector for runtime antiqueue scheduling.
- [ThothMindBodySpiritScribe.lean](./ThothMindBodySpiritScribe.lean) —
  unifying Thoth synthetic-gnosis certificate over body evidence, mind/tool
  reasoning, spirit/closure orientation, transcript memory, and failure
  residue. It proves admissible frames remain non-authoritative, preserve
  visible audit gaps, route closure through prosody discipline, and carry
  unresolved failure forward instead of erasing it.
- [FanoIncidence.lean](./FanoIncidence.lean) and
  [FanoGrassmannianMesh.lean](./FanoGrassmannianMesh.lean) — finite Fano-plane
  incidence contracts: every distinct seven-point pair has a unique completing
  third point, and each such pair embeds as a valid `Gr(2,12)` Plucker gate in
  the 66-label Aeon mesh.
- [AnarchyJacksonQueueBridge.lean](./AnarchyJacksonQueueBridge.lean) — reads
  the Anarchy/control tradeoff game from `PhysarumRopelength` as a finite
  Jackson queue: control pressure becomes arrival load, distributed local
  agents and boundary signals become service capacity, healthy anarchy clears
  the queue, command-control accumulates backlog, and mycelial capacity
  strictly dominates the human Jackson capacity model at positive node count
  while preserving the intrinsic **3/4** geometric ergodicity rate constraint;
  the same-load mycelial service weakly lowers and clears healthy-anarchy
  backlog without changing that rate.
- [CrossDomainMycelialTopologicalOrdering.lean](./CrossDomain/CrossDomainMycelialTopologicalOrdering.lean) —
  finite scheduler certificate for the Aeon Sorts pivot from scalar 1D sorting
  to topology-aware work ordering: a valid mycelial ordering preserves
  dependencies, bounds route cost by nutrient/growth cost, bounds peak backlog
  first by corridor capacity and then by mycelial network capacity, bounds fold
  debt by graph edges, inherits the existing `mycology_dominates_queueing`
  capacity theorem for positive node count, and projects the certificate through
  `TopologicalGrassmannianCompiler` with corridor capacity as the constraint
  axis.
- [SkyrmsEnergyTax.lean](./SkyrmsEnergyTax.lean) — chapel-grade dynamic energy
  market settlement: node externalities pay a clinamen-floor Skyrms tax,
  attention/truth/diversity define rebate weight, lower externality strictly
  lowers tax and payable burden, and two-node certificates conserve the
  collected redistribution pool.
- [BuddhistAttachmentSkyrms.lean](./BuddhistAttachmentSkyrms.lean) —
  operational analogue of Buddhist attachment for attention carriers; anchors
  `tanha` as failed attention plus unresolved debt, `dukkha` as Skyrms carrying
  cost, and `nirodha` as release that clears the refusal index while preserving
  rebate weight. It also proves the persistence theorem used by runtime
  evidence folds: accumulating failed attention or unresolved debt cannot lower
  operational karma tax, and strictly raises it when the new refusal pressure is
  positive. Its hard-gate review theorem keeps measured promotion evidence
  subordinate to the existing optimal admissible Skyrms/Gatekeeping statement.
- [SmartMaskingBand.lean](./SmartMaskingBand.lean) — bounded token-band /
  phoneme-band formalization for constrained decode. It proves that strict
  finite masks reduce the discrete work budget, and its default-promotion
  predicate requires non-Paris quality prompts so the Paris probe remains a
  smoke test rather than the optimized target. Runtime hook:
  [`distributed-inference` smart-mask benchmark](../../gnosis/distributed-inference/README.md).
- [TwelveSlotSixtySixPairsCarrier.lean](./TwelveSlotSixtySixPairsCarrier.lean) — neutral **`Fin 12`** slots + strict ascending pairs
  keyed to **`pairsIJ`** (**66** rows); shared spine for domain wrappers below.
- [TwelveSlotSixtySixPairsCyclicShear.lean](./TwelveSlotSixtySixPairsCyclicShear.lean) — **`rotateTwelveSlot`** (**`cyclicSucc`**) and
  **`StrictAscendingPair.rotatePairStep`** / **`rotatePairIterate`** aligned with **`rotPairNatAdd`** on chords (**global period `twelve`**).
- [GnosisTimeClock.lean](./GnosisTimeClock.lean) — **`TimePhase`** (**`Fin 12`** dial), **`tick`**, **`phaseOfNatTick`**, bridges to **`Circadian.aeon`**
  and **`TwelveSlot`**; solar-hour stability (**`phaseOfNatTick_add_minutesPerHour_mul`**).
- [EscherichiaColiOrthologTwelveCarrier.lean](./EscherichiaColiOrthologTwelveCarrier.lean) — *E. coli* group bibliography wrapper
  around the shared spine (**genomics motivation only**).
- [NikMapTwelveCarrier.lean](./NikMapTwelveCarrier.lean) — NIKA2 **12**-map / **66** cross-pair wrapper around the same spine
  (**Ponthieu, 2025** cosmological / confusion-noise motivation only).
- [FoilForrestWalk.lean](./FoilForrestWalk.lean) — **`List`** walks over **`pairsIJ`** strict pair steps (**Foil** index scaffold;
  spelling **Forrest** names a friend). Wired from Forest via **`open-source/gnosis/src/forest/forrest-skyrms-bridge.ts`**
  (`encodeHardAssignmentAsForrestWalk`, `bundleSkyrmsWithForrestWalk`) plus **`SkyrmsWalkHooks`** in
  [`skyrms-walk.ts`](../../gnosis/src/forest/skyrms-walk.ts). Lean carries gates only; TS carries **`η`** / Nash dynamics.
- [FoilZeroDragCompatibility.lean](./FoilZeroDragCompatibility.lean) — Init-only FOIL
  zero-drag compatibility certificates: coverage implies zero residual drag,
  drag is antitone in harvested witness coverage, cleared `RfSignalGate`-style
  thresholds select the 10-bit frame, raw byte observations clamp potential
  channels to the Monster-vector floor, the FOIL projection matches the Aeon
  Flow header width, and the quantum-facing carrier matches the already-proved
  twelve-slot noise bridge.
- [CacheObservation.lean](./CacheObservation.lean) — cache-hit and cold/stale
  miss accounting for marginal fold work, folded directly into the `Gnosis`
  namespace.
- [IncompletenessBettiFrontier.lean](./IncompletenessBettiFrontier.lean) —
  ties the bounded Goedel proof-budget wall, Betti/void duality, and the
  negative-knowledge ledger into one frontier certificate: residual unmeasured
  paths should be routed to measurement and documented absence, not mistaken
  for completion.
- [SimpsonsParadox.lean](./SimpsonsParadox.lean) — finite two-stratum Simpson's
  paradox witness: treatment A wins within both strata, treatment B wins after
  aggregation, with all rates compared by `Nat` cross-multiplication.
- [SelectionBiasPeriodicHoleBridge.lean](./SelectionBiasPeriodicHoleBridge.lean)
  — packages Wald bombers, Simpson aggregation, and the IUPAC 118-row periodic
  table matrix as one structural-hole lesson: visible survivor/table rows are
  not the whole manifold, and the hidden complement changes the recommendation.
- [SurvivorshipBias.lean](./SurvivorshipBias.lean) — Wald bomber armor witness:
  survivor hit counts select wings/fuselage/tail, missing-loss counts select
  engines/cockpit/fuel tanks, and the engine target routes through the existing
  Simpson/survivorship queue-boundary bridge.
- [RusticChurchContinuumPromotion.lean](./RusticChurchContinuumPromotion.lean) — Init-only
  scaffolding for [`docs/RusticChurchToContinuumChecklist.md`](./docs/RusticChurchToContinuumChecklist.md)
  §§1–3 (promotion tags, measure-entry hypothesis shape, axiom-budget / refusal anchors).
- [BracketedSpace.lean](./BracketedSpace.lean) — rational bracket towers for
  real-like values that preserve a nonzero uncertainty interval, with finite
  Phi refinement certificates suitable for FOIL cache-reuse gates.
- [DiscreteContinuumConstants.lean](./DiscreteContinuumConstants.lean) — Nat-only
  footholds for continuum constants: finite scaled-rational certificates for
  log thresholds, Euler's number partial sums, Archimedean pi brackets,
  square-root brackets, golden-ratio brackets, and named promotion obligations
  for the later analysis layer.
- [DiscreteContinuumConstantRefinement.lean](./DiscreteContinuumConstantRefinement.lean)
  — finite refinement towers over those footholds, proving checked bracket
  widths shrink for Euler's number, pi, sqrt two, and the golden ratio.
- [InterferenceResidueSequence.lean](./InterferenceResidueSequence.lean) —
  finite Lucas/Fibonacci leftover certificate: `traceSeq - Lucas` matches the
  balanced three-phase residue `(+2, -1, -1)` over the reconstructed window,
  each three-step overlap has zero signed drift, and `5` remains the golden
  discriminant marker at the Fibonacci/Lucas square gap.
- [TopologistJokeWitness.lean](./TopologistJokeWitness.lean) — finite
  humor/cringe certificate reusing the humor tensegrity bridge and cringe vacuum:
  donut and coffee mug match under coarse genus, semantic snapback rejects drinking
  the donut, and head/ground-hole routes through practical boundary rather than
  identity.
- [DiscreteMachineNumberApproximation.lean](./DiscreteMachineNumberApproximation.lean)
  — finite nearest-representable certificates for binary64 (`f64`, Java
  `double`, TypeScript `number`) and binary32 (`f32`, Java `float`) cells for
  pi, Euler's number, sqrt two, and the golden ratio, with midpoint promotion
  obligations isolating the continuum proof.
- [DiscreteMachineNumberFastPath.lean](./DiscreteMachineNumberFastPath.lean)
  — closed Boolean skip paths that decide whether an existing rational bracket
  already lies inside a finite machine cell's midpoint interval; current
  constant brackets record honest `false` frontier status until refinements
  become tight enough.
- [PeriodicAeonPhaseBridge.lean](./PeriodicAeonPhaseBridge.lean) - maps the **118**
  discrete periodic carrier band to the **12**-fold aeon torus (`Fin ambientDim`),
  charts to **`Fin twelve`** for `AeonCycleTwelveShadow`, and identifies enumeration phase with
  **`iteratedCyclicSucc`** from **`twelveCycleOrigin`** (still not chemical group placement).
- [RL.lean](./RL.lean) - Buleyean reinforcement-learning primitives, including
  rejection information and rejection-trained budget growth.
- [RLBudgetLedgerBridge.lean](./RLBudgetLedgerBridge.lean) - bridge proving
  one-bule-per-rejection ledger spend matches rejection-trained budget growth
  and weakly lowers Buleyean RL cost.
- [ConversationalDodgeball.lean](./ConversationalDodgeball.lean) - finite
  negotiation-tactic kernel for dodge/duck/dive/dip/repeated-dodge moves,
  extended with fact-checking closure discipline: silence, bare truth-dip, and
  unresolved residue are reported as non-closures, while argued answers and
  explicit boundary rejections satisfy closure. It also separates disciplined
  dodge/duck refinement from closure: refinement can improve question precision
  and preserve acceptance criteria, but must still terminate in argued closure.
- [ConversationalProsody.lean](./ConversationalProsody.lean) - finite
  vacuum-pressure stream gate for Thoth conversation closure: open questions
  create a source vacuum, answer/boundary/cadence/acceptance signals provide
  drainage and conductance, unresolved residue routes to glossolalia probing,
  and ready but undisciplined closure routes to an audit gap.
- [AffectLabelingPatternInterrupt.lean](./AffectLabelingPatternInterrupt.lean) - finite
  affect-labeling interrupt for Dodgeball validation: emotion naming and
  response space are required, valence deficit plus arousal regulation distance
  form safety costs, metric degeneration authorizes a bounded stall route,
  repeated failures double the response-silence budget, cringe vacuum records
  trapped unvented load, and grit records retry continuance after failure.
- [AffectLabelingClosure.lean](./AffectLabelingClosure.lean) - closure/obligation
  layer for affect-labeling stalls: affect work cannot discharge fact topology,
  the loop stays in Dodgeball with the question open until explicit walkaway
  (boundary rejection) or argued closure, and prosody routes unresolved affect
  interrupts to glossolalia/audit rather than closure fold.
- [ProvableRandomness.lean](./ProvableRandomness.lean) - Init-only randomness
  boundary certificate: deterministic byte cycles cover all 256 byte values,
  a Lacey-style DNA-dimension stream covers the byte boundary exactly once per
  cycle, and FOIL ambient entropy enters as a runtime certificate before Lean
  proves the 10-bit projection gate.
- [EntropyDeficitGateway.lean](./EntropyDeficitGateway.lean) - bridge for the
  RUSTIC_CHURCH entropy-surplus claim: broadcast/fork surplus becomes signed
  topological deficit under fixed transport capacity, maintained positive
  awareness pays storage debt, erasure heat matches awareness score, and a
  bounded contraction-loop theorem shows held positive awareness strictly
  increases storage debt until a matching `+1`/`-1` clinamen loop closes the
  local carrier. It also separates heat-death/vacuum entropy from structured
  electrical current: zero uncertainty forces the heat-death flag and the
  vacuum has no extractable-current witness, while structured current requires
  positive gradient, active fold/race witnesses, and a locked golden invariant.
  The refinery extension imports Griffith fracture, Avrami kinetics, and
  Butler-Volmer symmetry to require a toughness floor, saturation clamp, and
  positive overpotential divergence before producing current; it also proves
  the "entropy barrel" impossible and redirects extraction to a pink residual
  fringe witness. The projection-denoising extension imports
  `CosmicNoiseConnections`, `FickSecondLaw`, and
  `CompressionAsRetrocausalClosure` to package pink `30 -> 6` Aeon collapse,
  curvature anomaly, positive flux, bounded saturation, and Novikov-style
  verify closure as a diffusion-like reconstruction certificate rather than an
  erasure reversal; the canonical witness uses a `[0,1,0]` curvature profile,
  positive Butler-Volmer parameters, bounded Avrami context, and the stock
  `qwen_pca_k8_verified` protocol. The Hella-vortex canvas extension adds a
  finite observation-load anchor from `HellaVortex`, then proves a corrected
  diffusion handshake from load preservation, curvature anomaly, positive net
  current, saturated crystallization volume, and explicit verify closure. The
  final bridge proves that a pink residual fringe plus a saturated Hella-vortex
  canvas induces the earlier projection-denoising certificate, with a concrete
  `pathCount = 2`, single-stream canonical witness.

## Child Directories

- [docs](./docs/README.md) - short bridge-discipline notes (not Lean-checked).
- [CrossDomain](./CrossDomain/README.md) - finite cross-domain proof bridges,
  including the mycelial topological ordering certificate used by Aeon Sorts.
- [Contrarian](./Contrarian/README.md) - compact anti-theorem modules for claims
  where challenge, absence, latency, silence, or other apparent deficits map to
  formal benefits under explicit assumptions.
- [Civil](./Civil/README.md) - civil-engineering and transportation kernels,
  including queue flow, route equilibrium, and quasicrystal stoplight timing.
- [EntropyBridge](./EntropyBridge/README.md) - entropy bridge modules.
- [FiniteProbabilityCore](./FiniteProbabilityCore/README.md) - focused
  implementation modules behind the native finite probability facade.
- [GnosisMath](./GnosisMath/README.md) - internal Gnosis math support modules.
- [GreekLogicCanon](./GreekLogicCanon/README.md) - Init-only Greek logic canon
  modules, including the 24-form categorical syllogism catalog and the common
  propositional inference-rule catalog, plus finite question-vacuum formats for
  open inference slots and the Precision Q&A category/subcategory map.

## Aggregate Import

`../Gnosis.lean` serves as the package-level aggregate import. Add new modules there
when they should participate in `lake build Gnosis`.
