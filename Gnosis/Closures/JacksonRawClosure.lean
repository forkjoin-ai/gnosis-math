import Gnosis.JacksonQueueing

namespace Gnosis

/-- Raw envelope bound placeholder. -/
def JacksonTrafficData.rawEnvelopeBound {ι : Type} (_data : JacksonTrafficData ι) : Nat := 0

/-- Second order throughput envelope placeholder. -/
def JacksonTrafficData.secondOrderThroughputEnvelope {ι : Type} (_data : JacksonTrafficData ι) (_i : ι) : Nat := 0

/-- Local throughput envelope placeholder. -/
def JacksonTrafficData.localThroughputEnvelope {ι : Type} (_data : JacksonTrafficData ι) (_i : ι) : Nat := 0

/-- Max incoming routing mass placeholder. -/
def JacksonTrafficData.maxIncomingRoutingMass {ι : Type} (_data : JacksonTrafficData ι) : Nat := 0

/-- Max external arrival placeholder. -/
def JacksonTrafficData.maxExternalArrival {ι : Type} (_data : JacksonTrafficData ι) : Nat := 0

/-- Min service rate placeholder. -/
def JacksonTrafficData.minServiceRate {ι : Type} (_data : JacksonTrafficData ι) : Nat := 0

end Gnosis