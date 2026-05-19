# CrossDomain

Parent: [Gnosis](../README.md)

`CrossDomain/` contains finite Lean bridge modules that translate one domain's
operational structure into another domain's proof vocabulary.

## Key Modules

- [CrossDomainMycelialTopologicalOrdering.lean](./CrossDomainMycelialTopologicalOrdering.lean) -
  finite certificate for topology-aware Aeon ordering: valid mycelial schedules
  preserve dependency edges, bound route cost, bind backlog first to corridor
  capacity and then to network capacity, bound fold debt, and reuse the
  queue/mycology capacity dominance theorem. It also records the Grassmannian
  projection boundary used by Aeon Sorts: graph nodes as states, corridor
  capacity as constraints.
- [CrossDomainQueueingMycologyEntanglement.lean](./CrossDomainQueueingMycologyEntanglement.lean) -
  capacity contrast between queueing and mycelial network models.
- [CrossDomainFungalNetworkRouting.lean](./CrossDomainFungalNetworkRouting.lean) -
  routing-efficiency bridge for fungal growth-map style scheduling.
- [CrossDomainQueueingMycologySpanningTrees.lean](./CrossDomainQueueingMycologySpanningTrees.lean) -
  spanning-tree witness shape for mycelial queue work.
