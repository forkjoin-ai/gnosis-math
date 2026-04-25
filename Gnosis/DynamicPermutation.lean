-- DynamicPermutation.lean -- Runtime head routing as an Equiv on Fin n.
-- Any routing that permutes candidate indices before attention is a
-- bijective self-map. Applying σ then σ⁻¹ is identity, so routing
-- composed with its inverse preserves argmax / argmin (and every other
-- rank-based query). This is the formal backbone for Angle 5b's
-- topology-agnostic head TP: the order in which workers return partial
-- head outputs doesn't affect the final aggregate, as long as the inverse
-- re-permutation is applied before the output projection.


namespace DynamicPermutation

abbrev dim : Nat := 32   -- number of attention heads for gemma4-31b