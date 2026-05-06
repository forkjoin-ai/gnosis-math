import Init
import Gnosis.Ranking

/-!
# Ranking ↔ Fork/Race/Fold (minimal bridge)

**Fork** materializes branching evidence (here: the same `3 * k + r` spine as the pleromatic engine,
reproved `Init`-only). **Race** selects a local winner (`Fin 3` residue). **Fold** compresses back along
the spine (`n / 3`).

The ranking payoff is structural: a **dictator fold** is a genuine *profile → social* map that
factors through one voter (`ranking_dictator_is_fold_realization`). A **majority race** on the
Condorcet profile does **not** compose to a transitive relation (`majority_race_not_transitive`).
-/

namespace Gnosis
namespace RankingFrfBridge

open Ranking (Alt3 Voter2 Profile2 dictSocStrict majorityPrefers majority_not_transitive)

/-! ## Numeric fork / race / fold (Triton spine, `Init` only) -/

/-- Branch position `k` into three children `3k`, `3k+1`, `3k+2` (fork); selecting residue `r` is the race. -/
def frfFork (k r : Nat) : Nat :=
  3 * k + r

/-- Same combinator as `frfFork`; named for the race step in the narrative. -/
abbrev frfRace := @frfFork

/-- Fold: quotient out the fork factor of three. -/
def frfFold (n : Nat) : Nat :=
  n / 3

theorem frf_fold_inverts_fork_at_zero (k : Nat) : frfFold (frfFork k 0) = k := by
  unfold frfFork frfFold
  rw [Nat.add_zero, Nat.mul_comm]
  exact Nat.mul_div_cancel k (by decide : (0 : Nat) < 3)

theorem frf_fold_recovers_base (k r : Nat) (hr : r < 3) : frfFold (frfFork k r) = k := by
  unfold frfFork frfFold
  have h_swap : 3 * k + r = r + 3 * k := Nat.add_comm _ _
  rw [h_swap, Nat.add_mul_div_left r k (by decide : (0 : Nat) < 3)]
  rw [Nat.div_eq_of_lt hr, Nat.zero_add]

/-! ## Typed fold: profiles → social strict orders -/

/-- A fold rule maps profiles to binary social strict comparisons on `Alt3`. -/
abbrev ProfileFold :=
  Profile2 → (Alt3 → Alt3 → Prop)

/-- Dictator `d` induces the fold `p ↦ dictSocStrict d p`. -/
def dictatorFold (d : Voter2) : ProfileFold :=
  fun p => dictSocStrict d p

/-- The dictator fold **is** the realization of copying voter `d` (definitional factorization). -/
theorem ranking_dictator_is_fold_realization (d : Voter2) (p : Profile2) (a b : Alt3) :
    dictatorFold d p a b ↔ dictSocStrict d p a b :=
  Iff.rfl

/-! ## Majority race does not compose (Condorcet obstruction) -/

theorem majority_race_not_transitive :
    ¬∀ a b c : Alt3,
      majorityPrefers a b = true → majorityPrefers b c = true → majorityPrefers a c = true := by
  intro htrans
  rcases majority_not_transitive with ⟨h01, h12, h02⟩
  have hbad :=
    htrans (⟨0, by decide⟩ : Alt3) (⟨1, by decide⟩) (⟨2, by decide⟩) h01 h12
  rw [h02] at hbad
  nomatch hbad

/-- Dictator fold is well-behaved on the `Fin 2` slice; majority race is not globally transitive. -/
theorem ranking_frf_core_certificate (d : Voter2) (p : Profile2) (a b : Alt3) :
    (dictatorFold d p a b ↔ dictSocStrict d p a b) ∧
      frfFold (frfFork 7 2) = 7 ∧
        ¬∀ x y z : Alt3,
            majorityPrefers x y = true → majorityPrefers y z = true → majorityPrefers x z = true :=
  ⟨ranking_dictator_is_fold_realization d p a b,
    frf_fold_recovers_base 7 2 (by decide),
    majority_race_not_transitive⟩

end RankingFrfBridge
end Gnosis
