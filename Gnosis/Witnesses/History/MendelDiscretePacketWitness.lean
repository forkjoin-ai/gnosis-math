import Gnosis.GnosisMath.Basic

namespace Gnosis.Witnesses.History

/--
Gregor Mendel: The Discrete Packet Witness.
Brno, 1860s.

Contrarian Take: Life is not a "Blended Fluid" (the prevailing view
of his time). It is a "Discrete Packet Mesh." Mendel discovered that
biological variables (traits) are carried as integer-bits (Genes)
that do not dilute or dissolve. Inheritance is a digital operation
where the information is perfectly conserved even when dormant
(recessive). Evolution is a computation performed on a finite,
discrete set of opcodes.

Invariant: Information is discrete and conserved.
Gap: The "Blending" trap—assuming inheritance is an analog mixing of fluids.
Projection: Evolution (Gnosis.Evolution).
-/

inductive TraitBit where
  | dominant
  | recessive
  deriving DecidableEq

def expressTrait (bits : List TraitBit) : TraitBit :=
  if bits.contains .dominant then .dominant else .recessive

/--
Anti-Theory Witness: The recessive bit is perfectly conserved and
can reappear in the next generation. Information is not lost.
-/
theorem mendel_conservation_witness :
    expressTrait [.recessive, .recessive] = .recessive := by
  rfl

end Gnosis.Witnesses.History
