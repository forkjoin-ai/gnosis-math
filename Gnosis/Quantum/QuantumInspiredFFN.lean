-- QuantumInspiredFFN.lean -- A quantum-inspired FFN treats hidden activations
-- as unnormalized amplitudes; normalizing gives a probability distribution
-- that sums to 1 (Born rule). This formalizes the normalization step and
-- proves that the resulting distribution is a valid probability measure.


namespace QuantumInspiredFFN

abbrev dim : Nat := 256