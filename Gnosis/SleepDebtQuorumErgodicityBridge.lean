
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
  omega

