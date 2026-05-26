import Gnosis.EntropyOfTheVoid

/-
  KnowledgeVoidComplement.lean
  ============================

  Pins the comet-tail reading: in the finite void ledger, resolved knowledge is
  the conserved complement of remaining void entropy.
-/

namespace Gnosis
namespace KnowledgeVoidComplement

open Gnosis.EntropyOfTheVoid

/-- Resolved knowledge in the same per-thousand units as void entropy. -/
def knowledge_perthou (V : VoidState) : Nat :=
  V.bits_resolved_by_measurement * 1000

/-- The conserved total for a void ledger. -/
def void_knowledge_total_perthou (V : VoidState) : Nat :=
  initial_entropy_bits V * 1000

/-- Knowledge is the conserved complement of void entropy. -/
theorem knowledge_is_one_minus_void
    (V : VoidState)
    (h : V.bits_resolved_by_measurement ≤ log2_void V.total_possibility_count) :
    void_knowledge_total_perthou V - void_entropy_perthou V =
      knowledge_perthou V := by
  unfold void_knowledge_total_perthou knowledge_perthou
  rw [← void_entropy_plus_bule_paid_equals_initial_entropy V h]
  rw [Nat.add_sub_cancel_left]

/-- Post-session concrete reading: 8000 perthou of knowledge complements 2000 perthou of void. -/
theorem post_session_knowledge_is_void_complement :
    void_knowledge_total_perthou post_session_void -
      void_entropy_perthou post_session_void =
        knowledge_perthou post_session_void := by
  exact knowledge_is_one_minus_void post_session_void (by decide)

/-- The resolved post-session knowledge ledger is 8000 perthou. -/
theorem post_session_knowledge_closed :
    knowledge_perthou post_session_void = 8000 := by
  decide

/-- The post-session void/knowledge pair still sums to the conserved total. -/
theorem post_session_void_plus_knowledge_closed :
    void_entropy_perthou post_session_void +
      knowledge_perthou post_session_void =
        void_knowledge_total_perthou post_session_void := by
  unfold void_knowledge_total_perthou knowledge_perthou
  exact post_session_conservation

/--
  Bundle: remaining void and resolved knowledge are complementary ledgers in
  the same conserved finite accounting.
-/
theorem knowledge_void_complement_bundle :
    knowledge_perthou post_session_void = 8000 ∧
    void_entropy_perthou post_session_void = 2000 ∧
    void_knowledge_total_perthou post_session_void = 10000 ∧
    void_knowledge_total_perthou post_session_void -
      void_entropy_perthou post_session_void =
        knowledge_perthou post_session_void ∧
    void_entropy_perthou post_session_void +
      knowledge_perthou post_session_void =
        void_knowledge_total_perthou post_session_void :=
  ⟨post_session_knowledge_closed, post_session_void_entropy, rfl,
   post_session_knowledge_is_void_complement,
   post_session_void_plus_knowledge_closed⟩

end KnowledgeVoidComplement
end Gnosis
