import Gnosis.FiniteProbabilityCore.Core
import Gnosis.FiniteProbabilityCore.ChannelsKernels
import Gnosis.FiniteProbabilityCore.ProcessesChains
import Gnosis.FiniteProbabilityCore.ApproximationTowers
import Gnosis.FiniteProbabilityCore.SnowshoeCompletedCovers
import Gnosis.FiniteProbabilityCore.CalculusExporters
import Gnosis.FiniteProbabilityCore.Foundation
import Gnosis.FiniteProbabilityCore.Dynamics
import Gnosis.FiniteProbabilityCore.Interfaces
import Gnosis.FiniteProbabilityCore.RuntimeCertificate
import Gnosis.FiniteProbabilityCore.BoundedWitnessInterface

/-!
# Finite Probability Core

Compatibility facade for the focused native finite-probability stack.

The definitions remain in `Gnosis.FiniteProbabilityCore`; this file only
preserves the historical import path while the implementation is split into:

* `Core` for exact ratios, finite distributions, events, conditioning, Bayes,
  products, and residual observers.
* `ChannelsKernels` for mass-conserving channels and row-wise finite kernels.
* `ProcessesChains` for programs, processes, product processes, process chains,
  information accounting, and finite Markov witnesses.
* `ApproximationTowers` for refinement towers and shrink certificates.
* `SnowshoeCompletedCovers` for finite horizons, completed-infinite interfaces,
  snowshoe surfaces, and generic finite covers.
* `CalculusExporters` for observer-pattern adapters used by finite calculus
  modules.
* `Foundation`, `Dynamics`, and `Interfaces` as stable layer-level umbrellas.
* `RuntimeCertificate` for compact runtime mirrors of process, kernel, cover,
  completed-interface, topology, and bounded-witness certificates.
* `BoundedWitnessInterface` for the first-class adapter contract used by
  bounded runtime surfaces.
-/
