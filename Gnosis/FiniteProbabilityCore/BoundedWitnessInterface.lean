import Gnosis.FiniteProbabilityCore.RuntimeCertificate

namespace Gnosis
namespace FiniteProbabilityCore

/-!
# Bounded Witness Interface

First-class interface layer for bounded runtime surfaces. A domain implements
`BoundedWitnessAdapter` by providing a residual function and a stable domain
name; the generic constructor then emits the shared
`RuntimeBoundedWitnessCertificate` shape.
-/

/-!
This module intentionally re-exports the bounded witness adapter contract from
`RuntimeCertificate`. It exists as the stable first-class import path for
callers that only need the adapter interface layer.
-/

end FiniteProbabilityCore
end Gnosis
