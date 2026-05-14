# Civil

Parent: [Gnosis](../README.md)

`Gnosis/Civil/` contains discrete civil-engineering and transportation
theorem kernels used by the aggregate `Gnosis` import.

## Modules

- [AbramsLaw.lean](./AbramsLaw.lean) - concrete-strength witness.
- [BraessParadox.lean](./BraessParadox.lean) - non-monotonic route-capacity
  witness where adding a route increases equilibrium cost.
- [LittleLaw.lean](./LittleLaw.lean) - stable queue/throughput identity.
- [QuasicrystalStoplightTiming.lean](./QuasicrystalStoplightTiming.lean) -
  discrete signal-timing formulas and a quasicrystal green-wave corridor:
  each new stoplight adds one modular green-window constraint, Fibonacci-style
  spacing alone does not force alignment, and compensating offsets restore the
  lonely-car green wave.
- [WardropEquilibrium.lean](./WardropEquilibrium.lean) - user-equilibrium
  witness for transportation routes.

Other files in this directory carry compact civil, materials, and transport
formula witnesses in the same Init-only style.
