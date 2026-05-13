import Init
import Gnosis.BuleyeanProbability
import Gnosis.NonEmpiricalPrediction

namespace Gnosis
namespace NonEmpiricalPrediction

/-!
# Structural hole → Buleyean space (many choices, one distinguished hole)

For `n ≥ 2` and a chosen `i₀ : Fin n`, put the full aggregated void on the
distinguished index and zero elsewhere.  Functoriality is *parametrized* by
`i₀`; different choices give different `voidBoundary` embeddings of the same
scalar hole data.

`toBuleyeanSpace_mendeleev`: the distinguished choice’s Buleyean weight is
exactly `interpolationWeight` — an instance of `mendeleev_is_complement`.
-/

def voidBoundaryOfDistinguishedHole {n : Nat} (h : StructuralHole) (i₀ : Fin n) :
    Fin n → Nat :=
  fun j => if j = i₀ then h.neighborVoidSum else 0

theorem voidBoundaryOfDistinguishedHole_bounded {n : Nat} (h : StructuralHole) (i₀ : Fin n)
    (j : Fin n) :
    voidBoundaryOfDistinguishedHole h i₀ j ≤ h.neighborRoundsSum := by
  unfold voidBoundaryOfDistinguishedHole
  by_cases hji : j = i₀
  · subst hji
    simp
    exact h.hVoidLe
  · simp [hji]

def StructuralHole.toBuleyeanSpace {n : Nat} (h : StructuralHole) (hn : 2 ≤ n) (i₀ : Fin n) :
    BuleyeanSpace where
  numChoices := n
  nontrivial := hn
  rounds := h.neighborRoundsSum
  positiveRounds := h.hRoundsPos
  voidBoundary := voidBoundaryOfDistinguishedHole h i₀
  bounded := voidBoundaryOfDistinguishedHole_bounded h i₀

theorem toBuleyeanSpace_weight_at_hole {n : Nat} (h : StructuralHole) (hn : 2 ≤ n) (i₀ : Fin n) :
    (h.toBuleyeanSpace hn i₀).weight i₀ = h.interpolationWeight := by
  unfold BuleyeanSpace.weight StructuralHole.interpolationWeight StructuralHole.toBuleyeanSpace
  simp [voidBoundaryOfDistinguishedHole, Nat.min_eq_left h.hVoidLe]

theorem toBuleyeanSpace_mendeleev {n : Nat} (h : StructuralHole) (hn : 2 ≤ n) (i₀ : Fin n) :
    h.interpolationWeight = (h.toBuleyeanSpace hn i₀).weight i₀ :=
  (toBuleyeanSpace_weight_at_hole h hn i₀).symm

end NonEmpiricalPrediction
end Gnosis
