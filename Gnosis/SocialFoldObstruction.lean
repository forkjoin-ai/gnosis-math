import Init
import Gnosis.Ranking

/-!
# Social fold obstruction (Condorcet cycle → no global strict order)

**Discrete content (proved).** On the cyclic `Fin 3` majority profile from `Gnosis.Ranking`, there is
**no** binary relation `R` on alternatives that (i) contains every strict majority edge, (ii) is
transitive, and (iii) is asymmetric. Equivalently: there is no **strict total order** (hence no
injective **fold** into a line) that **respects all pairwise majority races** on this profile.

This packages the “hole” intuition without homology: the majority tournament carries an **oriented
3-cycle**; a transitive asymmetric relation cannot contain all three forward edges.

**Ledger boundary (not proved here).** Chichilnisky-style impossibility for **continuous** social
welfare maps on positive-dimensional preference manifolds, Sen’s minimal-liberty paradox, and
sheaf/topos models of epistemic aggregation require further infrastructure (`Mathlib` topology,
propositional modal logic, or bespoke finite universes beyond this file).
-/

namespace Gnosis
namespace SocialFoldObstruction

open Ranking (Alt3 majorityPrefers majority_cycle_0_1 majority_cycle_1_2 majority_cycle_2_0)

/-- Strict majority edge on the Condorcet witness profile. -/
def MajorityStrict (a b : Alt3) : Prop :=
  majorityPrefers a b = true

theorem majority_strict_01 : MajorityStrict (⟨0, by decide⟩ : Alt3) (⟨1, by decide⟩ : Alt3) :=
  majority_cycle_0_1

theorem majority_strict_12 : MajorityStrict (⟨1, by decide⟩ : Alt3) (⟨2, by decide⟩ : Alt3) :=
  majority_cycle_1_2

theorem majority_strict_20 : MajorityStrict (⟨2, by decide⟩ : Alt3) (⟨0, by decide⟩ : Alt3) :=
  majority_cycle_2_0

/--
No relation can **extend** strict Condorcet majority, stay **transitive**, and stay **asymmetric**
on `Alt3`: transitivity would force `0` ahead of `2`, but majority forces `2` ahead of `0`.
This is the formal “fold to a line contradicts local races” obstruction on this finite witness.
-/
theorem condorcet_cycle_forbids_transitive_extension (R : Alt3 → Alt3 → Prop)
    (hExt : ∀ a b, MajorityStrict a b → R a b)
    (hTrans : ∀ a b c, R a b → R b c → R a c)
    (hAsymm : ∀ a b, R a b → ¬ R b a) : False := by
  let z : Alt3 := ⟨0, by decide⟩
  let o : Alt3 := ⟨1, by decide⟩
  let t : Alt3 := ⟨2, by decide⟩
  have r01 : R z o := hExt z o majority_strict_01
  have r12 : R o t := hExt o t majority_strict_12
  have r20 : R t z := hExt t z majority_strict_20
  have r02 : R z t := hTrans z o t r01 r12
  exact absurd r02 (hAsymm t z r20)

end SocialFoldObstruction
end Gnosis
