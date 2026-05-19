# Finite Probability Core

Parent: [Gnosis](../README.md)

This directory contains the focused implementation modules for
`Gnosis.FiniteProbabilityCore`. All files remain in the
`Gnosis.FiniteProbabilityCore` namespace; the parent
[`FiniteProbabilityCore.lean`](../FiniteProbabilityCore.lean) facade preserves
the historical import path.

## Modules

- [RatiosDistributions.lean](./RatiosDistributions.lean) - exact ratios,
  finite mass, singleton distributions, and positive total-mass witnesses.
- [Events.lean](./Events.lean) - Boolean event masks, complements, unions,
  intersections, disjoint/exhaustive masks, and exact event mass laws.
- [Conditioning.lean](./Conditioning.lean) - conditioning by finite support
  reweighting and positive conditioned-total witnesses.
- [DistributionTransforms.lean](./DistributionTransforms.lean) - pushforward
  witnesses, product-distribution records, and finite independence arithmetic.
- [BayesTotalProbability.lean](./BayesTotalProbability.lean) - exact ratio
  multiplication, conditional probability, Bayes-style cross multiplication,
  and total probability over finite partitions.
- [ResidualObservers.lean](./ResidualObservers.lean) - probability residual
  state, observer promotion, budget monotonicity, and no-hidden-defect closure.
- [Core.lean](./Core.lean) - compatibility facade for the foundation modules
  above.
- [Foundation.lean](./Foundation.lean) - stable umbrella import for the
  foundation layer.
- [ChannelsKernels.lean](./ChannelsKernels.lean) - mass-conserving finite
  probability channels, channel composition, and row-wise finite stochastic
  kernels.
- [Programs.lean](./Programs.lean) - finite probability programs, program
  residual state, lossless programs, and program composition.
- [Processes.lean](./Processes.lean) - process contracts, program-to-process
  lowering, process composition, identity/triple accounting, and independent
  product processes.
- [ProcessChains.lean](./ProcessChains.lean) - process-list accounting,
  process chains, bounded shadow equivalence, and additive transitivity.
- [InformationAccounting.lean](./InformationAccounting.lean) - visible/shadow
  information scores and finite data-processing inequalities for processes,
  chains, and kernels.
- [MarkovWitnesses.lean](./MarkovWitnesses.lean) - kernel composites, finite and
  stationary Markov witnesses, and pleroma mattress accounting aliases.
- [ProcessesChains.lean](./ProcessesChains.lean) - compatibility facade for the
  process, chain, information, and Markov modules above.
- [ApproximationTowers.lean](./ApproximationTowers.lean) - finite approximation
  steps, tower residual/depth accounting, refinement, and shrink certificates.
- [Dynamics.lean](./Dynamics.lean) - stable umbrella import for channels,
  kernels, processes, chains, information accounting, Markov witnesses, and
  approximation towers.
- [SnowshoeCompletedCovers.lean](./SnowshoeCompletedCovers.lean) - finite
  horizons, completed-infinite interfaces, snowshoe surfaces, generic finite
  covers, cover exhaustion, and process/Markov cover exporters.
- [CalculusExporters.lean](./CalculusExporters.lean) - observer-pattern
  adapters that export queue, thermodynamic, mesh-routing, attention, and
  finite-approximation residual states as finite probability processes.
- [BoundedWitnessInterface.lean](./BoundedWitnessInterface.lean) - first-class
  `BoundedWitnessAdapter` interface for domains that emit the shared bounded
  witness certificate shape.
- [BoundedWitnessRecipe.lean](./BoundedWitnessRecipe.lean) - minimal toy-domain
  recipe showing that a new residual state plus one adapter inherits witness
  construction, shadow coverage, pipeline residual accounting, process-chain
  lowering, and no-hidden-defect reuse.
- [Interfaces.lean](./Interfaces.lean) - stable umbrella import for
  completed-infinite covers, snowshoe surfaces, generic cover exporters, and
  calculus exporters.
- [RuntimeCertificate.lean](./RuntimeCertificate.lean) - compact runtime mirror
  records for finite probability process, kernel, cover, completed-interface,
  topology-trace residual, checker-compactness, observer-acceptance, and
  bounded shadow-equivalence certificates.
- [ImportSmoke.lean](./ImportSmoke.lean) - build-only target that imports the
  layer umbrellas and the broad facade together to catch accidental cycles.

## Import Map

```text
RatiosDistributions
  -> Events
  -> Conditioning
  -> DistributionTransforms
  -> BayesTotalProbability
  -> ResidualObservers
  -> Core

Core -> ChannelsKernels -> Programs -> Processes -> ProcessChains
  -> InformationAccounting -> MarkovWitnesses -> ProcessesChains
  -> ApproximationTowers -> SnowshoeCompletedCovers -> CalculusExporters
  -> RuntimeCertificate -> BoundedWitnessInterface

Foundation -> Core
Dynamics -> ChannelsKernels + ProcessesChains + ApproximationTowers
Interfaces -> SnowshoeCompletedCovers + CalculusExporters
```

`FiniteProbabilityCore.lean` imports the public facades and remains the broad
compatibility import for callers that need the whole finite probability stack.

## Runtime Topology Contract

[`runtime_topology_contract.json`](./runtime_topology_contract.json) is the
machine-readable naming contract between Lean theorem mirrors in
`Gnosis.FiniteProbabilityCore.RuntimeCertificate` and the `@a0n/aeon-logic`
runtime exports. It pins the names for topology residual sums, checker
compactness, positive visible mass, observer acceptance, and bounded
shadow-equivalence witnesses so runtime certificates and Lean proof obligations
cannot drift silently.

The broader reusable pattern is:
`observedSurface + residualShadow + observerBudget + theoremWitness`.
`RuntimeBoundedWitnessCertificate` formalizes that pattern in Lean, while
`RuntimeTopologyProbabilityCertificate.toBoundedWitness` shows topology traces
are one concrete instance.

Domain adapters make the same certificate shape available for the current
bounded runtime surfaces:

- `queueBoundedWitness`
- `thermodynamicBoundedWitness`
- `meshRoutingBoundedWitness`
- `attentionBoundedWitness`
- `finiteApproximationBoundedWitness`

Each adapter has a matching `*_shadow_covered` theorem that recovers the core
observer-budget obligation from the certificate.

`RuntimeBoundedWitnessPipeline` folds a list of bounded witnesses into one
accepted composite certificate. `witnessBoundedPipelineTheorem` states that the
pipeline residual equals the sum of witness residuals, and
`runtime_bounded_witness_pipeline_shadow_covered` recovers the composite
observer-budget obligation. `RuntimeBoundedWitnessPipeline.toProcessChain`
lowers that accepted pipeline into `FiniteProbabilityProcessChain`, and
`runtime_bounded_witness_pipeline_process_chain_no_hidden_defect` reuses the
existing process-chain no-hidden-defect theorem. The concrete
`boundedWitnessWorkflowExamplePipeline` carries queue-to-finite-approximation
residual `33`, lowered process-chain residual `33`, and an end-to-end
no-hidden-defect theorem.

[`bounded_witness_adapter_contract.json`](./bounded_witness_adapter_contract.json)
is the lintable adapter contract for this interface. It ties each Lean adapter
name to its TypeScript runtime domain name and residual fields, and can be
checked from the repo root with
`node scripts/check-bounded-witness-contract.mjs` or the repo-owned target
`pnpm run a0 -- run open-source-gnosis-math:bounded-witness-contract`.

The same rows are mirrored inside Lean as
`boundedWitnessAdapterContractEntries`. Theorems such as
`bounded_witness_adapter_contract_queue_domain` prove that the contract row for
each Lean adapter resolves to the adapter's canonical runtime domain, while
`bounded_witness_adapter_certificate_witness_matches_shadow` proves every
adapter-generated certificate carries the same residual as its theorem witness.
That closes the loop: Lean owns the certificate invariant, JSON owns the
cross-language row artifact, and `a0` fails when the TypeScript runtime metadata
drifts from either.

`BoundedWitnessRegistryEntry` lifts those rows into a typed finite registry: a
contract row plus the certificate it emits, a proof that the row resolves to the
adapter's runtime domain, and a proof that the certificate witness matches the
residual shadow. `boundedWitnessRegistryToPipeline` derives an accepted
`RuntimeBoundedWitnessPipeline` from any such registry once the summed residual
fits the observer budget. The canonical workflow now flows through
`boundedWitnessWorkflowExampleRegistry`, so the queue-to-finite-approximation
pipeline is generated from registered bounded runtime surfaces rather than a
separate hand-maintained witness list.

`BoundedWitnessDomain` is the finite enum for the current canonical bounded
runtime universe. `boundedWitnessDomains` lists all five cases, and
`BoundedWitnessDomain.contractEntry` derives the canonical contract row for
each case. `bounded_witness_workflow_example_registry_complete` proves the
example registry covers exactly that finite domain list; adding a new canonical
surface now has one obvious proof obligation: extend the enum, contract row,
runtime metadata, registry certificate, and `a0` contract check together.
