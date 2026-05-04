
namespace Gnosis

def quorumReplicaCountFromPositiveDebt (debt : Nat) : Nat :=
  2 * debt

def quorumFailureBudgetFromPositiveDebt (debt : Nat) : Nat :=
  debt - 1

theorem positive_debt_embedding_yields_strict_majority
    {debt : Nat}
    (hDebt : 0 < debt) :
    2 * quorumFailureBudgetFromPositiveDebt debt <
      quorumReplicaCountFromPositiveDebt debt := by
  unfold quorumFailureBudgetFromPositiveDebt quorumReplicaCountFromPositiveDebt
  -- Goal: 2 * (debt - 1) < 2 * debt
  -- debt - 1 < debt because debt > 0; then multiply by 2 > 0.
  exact (Nat.mul_lt_mul_left (by decide : 0 < 2)).mpr
    (Nat.sub_lt hDebt (by decide : 0 < 1))

