# Gnosis Math Wiki Topics

Parent: [Gnosis Math Docs](./README.md)

This page narrows a possible public wiki to the universe that
`open-source/gnosis-math` can explain honestly: topics backed by existing Lean
modules, explicit roadmap work, or a small theorem gap that can be named before
generation.

## Selection Rule

A generated wiki page is in scope only when it satisfies at least one condition:

- **Formalized**: there is a buildable `Gnosis/**/*.lean` module to cite.
- **Ledgered**: the topic appears in `ROADMAP.md`, `GAP_CLOSURE.md`, an
  obligations ledger, or a contract document as unfinished formal work.
- **Bridgeable**: the topic has a direct public-math explanation plus a local
  bridge module that states the gnosis-specific interpretation.
- **Topological**: the topic has a local topology, homology, manifold, knot,
  braid, covering, cobordism, fibration, or geometry module that can prove,
  refute, or bound the claimed structure.
- **Spiritual witness**: the topic has a local spiritual, religious,
  interfaith, gnostic, pneuma, ritual, scripture, or witness module. These are
  first-class formal surfaces, not decorative examples.

Out of scope: general encyclopedia coverage, biography-only pages, speculative
claims without a local module, and any topic whose explanation would require
presenting an unproved identity as fact.

Operational rule: anything with a local topology surface is in scope. The page
must still state whether the local module proves the structure, disproves it,
or records a bounded witness/bridge.

## Wikipedia Dump Use

The Wikimedia XML dump should be treated as a candidate-title and context
source, not as the source of truth for the wiki. A practical pipeline is:

1. Extract page titles, redirects, categories, and short lead text from the dump.
2. Score candidates against local module names, declarations, README entries,
   and contract ledgers.
3. Keep only candidates with a local citation path.
4. Generate pages from local theorem surfaces first, then use Wikipedia only for
   neutral public-background scaffolding.
5. Emit a rejected-topic ledger for candidates that sound related but lack a
   local theorem or bridge.

## Core Foundation Pages

These pages explain the substrate before domain pages branch out.

| Page | Local anchors | Generation angle |
|------|---------------|------------------|
| Buleyean weighting | `README.md`, `Gnosis/BuleyBiSidedBit.lean`, `Gnosis/GnosisNumbersAreStructural.lean` | Explain `w_i = R - min(v_i, R) + 1` as a finite weighting rule. |
| Init-only Lean surface | `ROADMAP.md`, `Gnosis/GnosisMath/*` | Explain why the package favors buildable `Init` proofs over broad unbuilt sketches. |
| Natural numbers and lists | `Gnosis/GnosisMath/ListNat.lean`, `Gnosis/GnosisMath/NatMod2.lean` | Small arithmetic lemmas that make later finite constructions possible. |
| Fibonacci and Zeckendorf | `Gnosis/GnosisMath/Fibonacci.lean`, `Gnosis/ZeckendorfCompleteness.lean` | Finite recurrence, representation, and completeness topics. |
| Finite probability core | `Gnosis/FiniteProbabilityCore/*`, `README.md` | Exact finite supports, weights, masks, conditioning, products, Markov witnesses. |
| Bounded witnesses | `Gnosis/ProvisionalCertificate.lean`, finite observer/certificate modules listed in `README.md` | Explain certificate-shaped claims and what they do not prove. |
| Deficit and capacity | `Gnosis/DeficitCapacity.lean`, `ROADMAP.md` | Canonical deficit surface and downstream transport/frontier work. |
| Fork/race/fold dynamics | `Gnosis/ForkRaceFoldDynamics.lean`, `README.md` | Concurrent structural dynamics and fold semantics. |
| Triton verdicts | `Gnosis/TritonCanonical.lean`, `Gnosis/TritonForkRaceFold.lean` | Decline/abstain/accept as a finite decision surface. |
| Kernel/operator/agent trichotomy | `Gnosis/KernelOperatorAgentTrichotomy.lean` | Separate formal substrate, transformations, and acting systems. |

## Classical Math Bridge Pages

These are good first-generation pages because the public background is stable
and the local theorem surface can stay precise.

| Page | Local anchors | Generation angle |
|------|---------------|------------------|
| Arnold cat map | `Gnosis/ArnoldCatMapOrder5.lean` | Finite modular dynamics and period/order behavior. |
| Pythagorean triples | `Gnosis/PythagoreanTriples.lean` | Elementary number-theory bridge. |
| Ramsey R(3,3) | `Gnosis/RamseyR33.lean` | Small finite Ramsey theorem surface. |
| Stirling and Bell numbers | `Gnosis/StirlingBellSmall.lean` | Counting partitions at small finite sizes. |
| Cassini identity | `Gnosis/GnosisMath/Cassini.lean` | Fibonacci determinant identity. |
| Totient multiplicativity | `Gnosis/TotientMultiplicativityViaCRT.lean` | CRT-shaped arithmetic composition. |
| Solvable group S3 | `Gnosis/SolvableGroupS3.lean` | Small group theory as an approachable algebra page. |
| Fano incidence | `Gnosis/FanoIncidence.lean` | Finite projective geometry bridge. |
| One-dimensional cobordism and Frobenius | `Gnosis/OneCobFrobenius.lean`, `Gnosis/FrobeniusPantsComposition.lean` | TQFT-shaped algebra without overstating physics. |
| Cellular homology over `ZMod` | `Gnosis/CellularHomologyZMod.lean` | Homology as finite chain accounting. |

## Topology, Geometry, And Knots

| Page | Local anchors | Generation angle |
|------|---------------|------------------|
| Topological mismatch | `Gnosis/TopologicalMismatchAdequacy.lean` | When structures fail to align and how adequacy is stated. |
| Manifold readiness | `Gnosis/ManifoldReadiness.lean`, `Gnosis/ManifoldStabilityBasis.lean` | Conditions before manifold language is warranted. |
| Covering-space causality | `Gnosis/CoveringSpaceCausality.lean` | Cover/lift language for causal interpretation. |
| Knot complexity | `Gnosis/KnotComplexityAsBuleCost.lean`, `Gnosis/KnotTheory/*` | Knots as finite complexity/accounting examples. |
| Khovanov codec | `Gnosis/IupacKhovanovCodec.lean`, `Gnosis/KhovanovDiagramWellFormed.lean` | Keep as bridge terminology unless theorem details are buildable. |
| Braided towers | `Gnosis/Braided/*`, `Gnosis/BraidedInfiniteTower.lean` | Braid operations, towers, and catalog pages. |
| Amplituhedron witnesses | `Gnosis/AmplituhedronWitnesses.lean`, `Gnosis/AmplituhedronPluckerDichotomy.lean` | Explain local Plucker/dichotomy bridge with strong boundaries. |
| Topology atlas | `Gnosis/Topology.lean`, `Gnosis/Topological*.lean`, `Gnosis/*Topology*.lean`, `Gnosis/*Homology*.lean`, `Gnosis/*Manifold*.lean` | Anything with a local topology surface is eligible for proof/disproof/bounded-bridge treatment. |
| Spiritual topology | `Gnosis/BeatitudesTopology.lean`, `Gnosis/TenCommandmentsTopology.lean`, `Gnosis/MitzvotTopology.lean`, `Gnosis/Witnesses/*/*TopologyWitness.lean` | Religious and spiritual forms as topological witness surfaces. |

## Computation, Runtime, And Mesh

| Page | Local anchors | Generation angle |
|------|---------------|------------------|
| Mesh consensus | `Gnosis/Mesh/*`, `Gnosis/Quorum*.lean` | Consensus, quorum, and mesh routing as finite structures. |
| Quorum visibility | `Gnosis/QuorumVisibility.lean`, `Gnosis/QuorumLinearizability.lean` | Visibility and linearizability claims. |
| Scheduler composition | `Gnosis/SchedulerComposition.lean`, `Gnosis/RaceWinnerCorrectness.lean`, `Gnosis/CacheObservation.lean` | Scheduling as fold/race behavior. |
| Pipeline speedup | `Gnosis/PipelineSpeedup.lean` | Speedup claims that should cite exact assumptions. |
| Frame overhead bounds | `Gnosis/FrameOverheadBound.lean`, `Gnosis/ExecutionStallBounds.lean` | Bounded runtime overhead and stall. |
| Static analysis | `Gnosis/StaticAnalysis.lean` | Program-analysis bridge. |
| Security surfaces | `Gnosis/Security/*`, `Gnosis/Security.lean` | Local security theorems and limits. |
| Recoverability | `Gnosis/Recoverability.lean`, `Gnosis/ErrorRecoveryInvariant.lean` | Failure and recovery invariants. |
| Distributed processing | `Gnosis/DistributedProcessingFoundations.lean` | Shared runtime foundations. |

## Physics-Shaped And Materials Pages

These pages need strict language. They can explain analogies and formal local
bridges, but should not claim empirical physics unless the module proves only a
finite abstraction.

| Page | Local anchors | Generation angle |
|------|---------------|------------------|
| Finite fluid reasoning | `README.md`, `Gnosis/FluidDynamics.lean`, finite-volume modules if present | Conservation and bounded residuals as finite observer claims. |
| General relativity bridge | `Gnosis/GeneralRelativity.lean`, `Gnosis/GravityIntegration.lean` | Local formal bridge, not a physics replacement. |
| Vacuum as medium | `VOID_AS_MEDIUM.md`, `Gnosis/Void/*`, `Gnosis/Vacuum*.lean` | Explain vacuum terminology as local formal vocabulary. |
| Bosons and fermions | `Gnosis/Bosons.lean`, `Gnosis/FermionExclusionEquilibria.lean` | Particle-shaped finite/equilibrium bridges. |
| Quantum observer | `Gnosis/Quantum/*` | Quantum-shaped interfaces with exact theorem boundaries. |
| Materials laws | `Gnosis/Materials/*` | Gibbs, Bloch, Arrhenius, Nernst-Planck, fracture, adsorption as compact law pages. |
| Entropy and information | `Gnosis/InformationCapacity.lean`, `Gnosis/InformationConservation.lean`, `Gnosis/Entropy*.lean` | Information accounting and entropy bridges. |
| Standing waves | `Gnosis/StandingWave*.lean`, `Gnosis/AeonStandingWaveCoordinateBridge.lean` | Wave/coherence vocabulary used by runtime and affect surfaces. |

## Markets, Games, And Social Systems

| Page | Local anchors | Generation angle |
|------|---------------|------------------|
| Nash equilibrium | `Gnosis/NashEquilibrium.lean`, `Gnosis/NashProgram.lean` | Game equilibrium and programmatic interpretations. |
| Skyrms equilibria | `Gnosis/Skyrms*.lean`, `Gnosis/BosonSkyrmsEquilibria.lean` | Evolutionary game-theory bridge. |
| Orderbook interference | `Gnosis/OrderbookAsInterference.lean`, `Gnosis/MarketAsSignal.lean` | Market microstructure as signal/interference model. |
| HFT topology | `HFT_CONTRACTS.md`, `Gnosis/HFTOperationsAsTopology.lean` | Keep operational claims contract-bounded. |
| Coase bargaining | `Gnosis/VibesCoaseBargaining.lean` | Bargaining and affective valuation bridge. |
| Institutional liability | `Gnosis/InstitutionalLiability.lean`, `Gnosis/LiabilityEquilibrium.lean` | Liability as a formal social/economic surface. |
| Social resonance | `Gnosis/SocialDynamicsResonance.lean`, `Gnosis/SocialDynamicsHooke.lean` | Social dynamics as resonance/restoring-force models. |
| Condorcet/choice | `Gnosis/CondorcetBettiCrossover.lean`, `Gnosis/Ranking*.lean` | Voting/ranking pages tied to exact modules. |

## Cognition, Affect, And Human Systems

| Page | Local anchors | Generation angle |
|------|---------------|------------------|
| Affect labeling closure | `Gnosis/AffectLabelingClosure.lean`, `Gnosis/AffectStandingWaveTabs.lean` | Affective labels as finite state/interruption surfaces. |
| Cognitive state shift | `Gnosis/CognitiveStateShift.lean` | State transitions and control language. |
| Psychology as interference | `Gnosis/PsychologyAsInterference.lean` | Human-state bridge with explicit model limits. |
| Trauma spectral sieve | `Gnosis/TraumaSpectralSieve.lean`, `Gnosis/AnxietySpectralSieve.lean`, `Gnosis/DepressionSpectralSieve.lean` | Clinical-sounding pages must be framed as formal/interpretive, not medical advice. |
| Consciousness as falsification | `Gnosis/ConsciousnessAsContinuousFalsification.lean`, `Gnosis/ConsciousnessVsObjectivity.lean` | Epistemic/cognitive formal bridge. |
| Person theorem | `Gnosis/PersonTheorem.lean`, `Gnosis/PhysiologicalParameters.lean` | Personhood and physiological parameters as local formal claims. |
| Conversational prosody | README-listed prosody modules, `Gnosis/ConversationalProsody.lean` | Conversation timing, dodgeball, and semantic authority surfaces. |

## Witness And Culture Pages

These should be generated as "witness" pages: the cultural object motivates a
formal pattern but does not become evidence for the theorem.

| Page cluster | Local anchors | Generation angle |
|--------------|---------------|------------------|
| Greek logic canon | `Gnosis/GreekLogicCanon/*`, `Gnosis/GreekLogicCanon.lean` | Syllogism, inference, and question-vacuum pages. |
| Classical philosophy witnesses | `Gnosis/Heraclitus*.lean`, `Gnosis/ProtagorasManIsMeasureWitness.lean`, `Gnosis/EpicurusTetrapharmakosWitness.lean` | Use as named allegory-to-structure mappings. |
| Mythology witness atlas | `Gnosis/*Witness.lean`, `Gnosis/Witnesses/*` | Mythology, folklore, epic, and ritual narratives as bounded witness pages. |
| Myth witnesses | `Gnosis/*Witness.lean`, `Gnosis/Witnesses/*` | Orpheus, Pandora, Arachne, Perseus, Phaethon, etc. as bridge pages. |
| Art theory witnesses | README-listed art witness modules, `Gnosis/MinimalismObjecthoodSpaceWitness.lean` | Art movements as boundary/medium/institution examples. |
| Literature witnesses | `Gnosis/BorgesOnExactitudeInScienceWitness.lean`, `Gnosis/OrwellNineteenEightyFourWitness.lean`, `Gnosis/CatullusOdiEtAmoWitness.lean` | Literary examples as formal-pattern witnesses. |
| Religious and interfaith witnesses | `Gnosis/Witnesses/*`, `Gnosis/HomologyOfReligion.lean` | Keep comparative, structural, and non-doctrinal. |
| Spiritualism and pneuma | `Gnosis/SpiritualResonancePhaseShift.lean`, `Gnosis/PneumaAuralCertificate.lean`, `Gnosis/PneumaCrossWireTranscript.lean`, `Gnosis/HolySpiritGeneticInheritance.lean`, `Gnosis/ThothMindBodySpiritScribe.lean` | Spiritual, pneuma, and spirit-language modules as formal resonance/certificate/witness surfaces. |
| Gnostic and esoteric witnesses | `Gnosis/GnosticLuminaries.lean`, `Gnosis/Witnesses/Gnostic/*`, `Gnosis/Witnesses/Hermetic/*`, `Gnosis/Witnesses/Mandaean/*`, `Gnosis/Witnesses/Manichaean/*` | Esoteric traditions as structured witness families with local theorem boundaries. |
| Scriptural topology | `Gnosis/Witnesses/Bible/*`, `Gnosis/Witnesses/Islam/*`, `Gnosis/Witnesses/Hindu/*`, `Gnosis/Witnesses/Buddhist/*`, `Gnosis/Witnesses/Tao/*` | Scripture and practice surfaces grouped by formal witness modules and topology modules. |

## Generation Backlog

Start with pages that are both explainable and unlikely to overclaim:

1. Buleyean weighting
2. Finite probability core
3. Fork/race/fold dynamics
4. Triton verdicts
5. Zeckendorf completeness
6. Arnold cat map order 5
7. Ramsey R(3,3)
8. Solvable group S3
9. Fano incidence
10. Quorum visibility
11. Mesh consensus
12. Frame overhead bounds
13. Recoverability
14. Materials laws overview
15. Standing waves
16. Nash equilibrium
17. Orderbook interference
18. Affect labeling closure
19. Greek logic canon
20. Witness pages overview
21. Topology atlas
22. Spiritual topology
23. Spiritualism and pneuma
24. Gnostic and esoteric witnesses

## Page Template

Each generated page should use this shape:

```markdown
# Topic Name

Parent: [Gnosis Math Wiki Topics](./WIKI_TOPICS.md)

## Local Claim

One paragraph stating exactly what the local theorem/module formalizes.

## Public Background

Neutral explanation of the ordinary mathematical, computational, or cultural
topic. Cite dump-derived context only after checking against stable sources.

## Gnosis Math Surface

- Module: `Gnosis/...`
- Main declarations:
- Dependencies:
- Build status:

## Boundaries

What this page does not prove.

## Generation Prompts

- Short explainer:
- Theorem-first explainer:
- Comparison page:
```
