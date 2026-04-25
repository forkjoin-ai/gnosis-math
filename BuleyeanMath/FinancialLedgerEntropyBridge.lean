
namespace BuleyeanMath

structure FinancialLedgerEntropyAssumptions where
  ledgerTransactions : Nat
  entropyHeat : Nat
  bridgeExact : ledgerTransactions = entropyHeat
  transactionsPositive : 0 < ledgerTransactions

theorem financial_ledger_entropy_bridge_exact
    (assumptions : FinancialLedgerEntropyAssumptions) :
    0 < assumptions.ledgerTransactions ->
    assumptions.ledgerTransactions = assumptions.entropyHeat ->
    0 < assumptions.entropyHeat := by
  intro hPos hEq
  rw [←hEq]
  exact hPos

end BuleyeanMath