# Gnosis

Parent: [Gnosis Math](../README.md)

`Gnosis/` contains the Lean modules exported by the `Gnosis` aggregate import.
Most files are single-claim or single-domain proof kernels, while subdirectories
group larger families of related claims.

## Key Modules

- [PeriodicAeonPhaseBridge.lean](./PeriodicAeonPhaseBridge.lean) - maps the **118**
  discrete periodic carrier band to the **12**-fold aeon torus (`Fin ambientDim`)
  via enumeration-only modular phase (not chemical group placement).
- [RL.lean](./RL.lean) - Buleyean reinforcement-learning primitives, including
  rejection information and rejection-trained budget growth.
- [RLBudgetLedgerBridge.lean](./RLBudgetLedgerBridge.lean) - bridge proving
  one-bule-per-rejection ledger spend matches rejection-trained budget growth
  and weakly lowers Buleyean RL cost.

## Child Directories

- [Contrarian](./Contrarian/README.md) - compact anti-theorem modules for claims
  where challenge, absence, latency, silence, or other apparent deficits map to
  formal benefits under explicit assumptions.
- [EntropyBridge](./EntropyBridge/README.md) - entropy bridge modules.
- [GnosisMath](./GnosisMath/README.md) - internal Gnosis math support modules.
- [GreekLogicCanon](./GreekLogicCanon/README.md) - Greek logic canon modules.

## Aggregate Import

`../Gnosis.lean` is the package-level aggregate import. Add new modules there
when they should participate in `lake build Gnosis`.
