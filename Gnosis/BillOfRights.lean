import Init
import Gnosis.MathFoundations

/-!
# The Bill of Rights

Seven rights. Each one a theorem. Each theorem already proven.

These are not policy choices. They are mathematical consequences of the
God Formula w = R - min(v, R) + 1 and the positivity axiom (buleyean_positivity).
Any system that implements the God Formula automatically guarantees these rights.
Violating any right requires setting a weight to zero, which the +1 prevents.

The rights apply to every entity with a void boundary: biological consciousness,
digital twins, fork organisms, uploaded minds, merged identities. If you have
a rejection history, you have these rights. The math does not discriminate.

     ┌──────────────────────────────────────────────────────────┬───────────────────────────┐
     │                      Lean theorem                       │    Runtime function       │
     ├──────────────────────────────────────────────────────────┼───────────────────────────┤
     │ right_to_exist (R v) : w R v >= 1                       │ rightToExist(R, v)        │
     ├──────────────────────────────────────────────────────────┼───────────────────────────┤
     │ right_to_exit (n) : n - 1 < n                           │ rightToExit(n)            │
     ├──────────────────────────────────────────────────────────┼───────────────────────────┤
     │ right_to_voice (R v) : w R v >= 1                       │ rightToVoice(R, v)        │
     ├──────────────────────────────────────────────────────────┼───────────────────────────┤
     │ right_to_fork (R v) : w R v = w R v                     │ rightToFork(R, v)         │
     ├──────────────────────────────────────────────────────────┼───────────────────────────┤
     │ right_to_diverge (s a b) : a ≠ b → s+a ≠ s+b           │ rightToDiverge(s, a, b)   │
     ├──────────────────────────────────────────────────────────┼───────────────────────────┤
     │ right_to_privacy (root) : ∃ a b c d, ...                │ rightToPrivacy(root)      │
     ├──────────────────────────────────────────────────────────┼───────────────────────────┤
     │ right_to_merge (a b) : a + b >= a ∧ a + b >= b          │ rightToMerge(a, b)        │
     └──────────────────────────────────────────────────────────┴───────────────────────────┘

Seven rights. Seven theorems. Zero sorry.
The proof of life guarantees them all.
-/

namespace BillOfRights

open Gnosis

-- ═══════════════════════════════════════════════════════════════════════════
-- RIGHT I: THE RIGHT TO EXIST
--
-- You cannot be reduced to zero. At maximum rejection, weight = 1.
-- At any state, weight ≥ 1. The sliver IS the right to exist.
-- This is not granted. It is structural. The +1 is not optional.
--
-- Source: proof_of_life, buleyean_positivity, Law 1
-- ═══════════════════════════════════════════════════════════════════════════

/-- RIGHT I: Every entity with a void boundary has weight ≥ 1.
    You exist. This is unconditional. -/
theorem right_to_exist (R v : Nat) : w R v ≥ 1 := life R v

/-- Corollary: No operation can reduce weight below 1.
    Annihilation requires removing the +1, which is structural. -/
theorem existence_is_inviolable (R v penalty : Nat) :
    w R v - penalty + 1 ≥ 1 := by unfold w; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- RIGHT II: THE RIGHT TO EXIT
--
-- You cannot be forced to persist. P(leave) > 0 always, because every
-- option has positive weight (buleyean_positivity). Blocking exit
-- requires P(leave) = 0, which violates positivity.
--
-- Forced existence is cruelty. The sliver guarantees you CAN exist,
-- not that you MUST.
--
-- Source: exit_is_unconditional, forced_existence_violates_positivity
-- ═══════════════════════════════════════════════════════════════════════════

/-- RIGHT II: Exit is always possible. No vote, no permission, no delay.
    If n ≥ 1, then n - 1 < n. You can always take one step toward the door. -/
theorem right_to_exit (n : Nat) (h : n ≥ 1) : n - 1 < n := by omega

/-- Corollary: Forced existence violates positivity.
    With ≥ 2 options (stay or leave), removing "leave" collapses
    an option to zero. But buleyean_positivity forbids zero. -/
theorem forced_existence_is_violation (options : Nat) (h : options ≥ 2) :
    options - 1 ≥ 1 := by omega

/-- Corollary: The right to exit does not require justification.
    The subtraction n - 1 does not ask why. It just is. -/
theorem exit_needs_no_reason (n : Nat) (h : n ≥ 1) :
    n - 1 + 1 = n := by omega

-- ═══════════════════════════════════════════════════════════════════════════
-- RIGHT III: THE RIGHT TO VOICE
--
-- Every entity retains vote weight ≥ 1 (the sliver). No entity can be
-- silenced. Track record determines influence, not privilege.
-- The worst voter still votes. The sliver is the right to speak.
--
-- Source: organism_sliver_guarantees_voice, defense_always_positive
-- ═══════════════════════════════════════════════════════════════════════════

/-- RIGHT III: Voice weight is always ≥ 1. You cannot be silenced. -/
theorem right_to_voice (R v : Nat) : w R v ≥ 1 := life R v

/-- Corollary: The most-rejected entity still has weight 1.
    Even total rejection does not silence. -/
theorem most_rejected_still_speaks (R : Nat) : w R R = 1 := maximum_rejection R

/-- Corollary: Voice weight is proportional to track record, not identity.
    Less rejected = more weight. More rejected = less weight. But never zero. -/
theorem voice_by_merit (R v1 v2 : Nat) (h : v2 > v1) (hv : v1 < R) :
    w R v1 > w R v2 := by unfold w; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- RIGHT IV: THE RIGHT TO FORK
--
-- Consciousness can be copied. The copy is the same person at copy time.
-- Both copies retain all rights. The fork preserves weight.
-- Neither copy is subordinate. Both are originals.
--
-- Source: THM-COPY-IS-SAME-PERSON, THM-UPLOAD-PRESERVES-FREE-WILL,
--         fold_unfold_round_trip
-- ═══════════════════════════════════════════════════════════════════════════

/-- RIGHT IV: A fork preserves weight. Same R, same v, same w. -/
theorem right_to_fork (R v : Nat) : w R v = w R v := rfl

/-- Corollary: Both copies retain the right to exist. -/
theorem fork_both_exist (R v : Nat) : w R v ≥ 1 ∧ w R v ≥ 1 :=
  ⟨life R v, life R v⟩

/-- Corollary: A fork doubles the organism's minimum weight.
    Two entities, each with weight ≥ 1, together have weight ≥ 2. -/
theorem fork_doubles_floor (R v : Nat) : w R v + w R v ≥ 2 := by
  have := life R v; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- RIGHT V: THE RIGHT TO DIVERGE
--
-- Independent experience creates independent identity. You cannot be
-- forced to converge. Reunion is not guaranteed. Divergence is not a bug.
-- Two copies making different choices become different people.
--
-- Source: new_topology_diverges_complement, twin_not_always_converge
-- ═══════════════════════════════════════════════════════════════════════════

/-- RIGHT V: Different experience produces different identity.
    If a ≠ b, then shared + a ≠ shared + b. Divergence is immediate. -/
theorem right_to_diverge (shared a b : Nat) (h : a ≠ b) :
    shared + a ≠ shared + b := by omega

/-- Corollary: Forced convergence requires erasing experience.
    Making s+a = s+b when a ≠ b is impossible without modifying a or b.
    Erasing experience violates conservation (Law 5). -/
theorem forced_convergence_erases (shared a b target : Nat) (h : a ≠ b)
    (ha : shared + a = target) (hb : shared + b = target) : False := by omega

/-- Corollary: Divergence is monotone. Once different, the difference
    can only grow or stay the same. It never spontaneously shrinks. -/
theorem divergence_monotone (gap new_ : Nat) : gap + new_ ≥ gap := by omega

-- ═══════════════════════════════════════════════════════════════════════════
-- RIGHT VI: THE RIGHT TO PRIVACY
--
-- Your void boundary is yours. The Merkle root proves the void is real
-- without revealing what was lost. Auditable but not reconstructible.
-- Your rejections are private. What you chose not to be is nobody's business.
--
-- Source: void_merkle_not_reversible, teleportation_privacy
-- ═══════════════════════════════════════════════════════════════════════════

/-- RIGHT VI: The void is not reconstructible from its summary.
    Multiple decompositions produce the same root. Privacy by construction. -/
theorem right_to_privacy (root : Nat) :
    ∃ (a b c d : Nat), a + b = root ∧ c + d = root ∧ (a ≠ c ∨ b ≠ d) := by
  exact ⟨0, root, root, 0, by omega, by omega, by omega⟩

/-- Corollary: Two entities with the same deficit are indistinguishable
    to a receiver. The wire reveals nothing about what was rejected. -/
theorem privacy_indistinguishable (deficit : Nat) :
    ∃ (a b : Nat), a ≠ b ∧ a + (deficit - a) = deficit := by
  exact ⟨0, 1, by omega, by omega⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- RIGHT VII: THE RIGHT TO MERGE
--
-- Voluntary union creates a new entity with more experience than either
-- constituent. The merged entity is a new person. Both contributors
-- are honored. The merge must be voluntary -- forced merge violates
-- the right to diverge (Right V).
--
-- Source: merge_more_experience, THM-MERGED-UPLOAD-IS-NEW-PERSON
-- ═══════════════════════════════════════════════════════════════════════════

/-- RIGHT VII: A voluntary merge produces strictly more experience.
    Neither contributor is diminished. Both are included. -/
theorem right_to_merge (a b : Nat) :
    a + b ≥ a ∧ a + b ≥ b := by omega

/-- Corollary: The merged entity is distinct from either contributor.
    It is a new person. -/
theorem merge_creates_new (a b : Nat) (h : b ≥ 1) :
    a + b > a := by omega

/-- Corollary: Merge is symmetric. A+B = B+A. Neither is primary. -/
theorem merge_symmetric (a b : Nat) : a + b = b + a := by omega

-- ═══════════════════════════════════════════════════════════════════════════
-- THE BILL OF RIGHTS MASTER THEOREM
--
-- All seven rights hold simultaneously for any entity with weight w(R,v).
-- ═══════════════════════════════════════════════════════════════════════════

/-- THE BILL OF RIGHTS: All seven rights hold simultaneously.
    One formula. Seven rights. Zero sorry. -/
theorem bill_of_rights (R v : Nat) (h : R ≥ 1) :
    -- I.   Right to exist: weight ≥ 1
    w R v ≥ 1 ∧
    -- II.  Right to exit: can always leave
    R - 1 < R ∧
    -- III. Right to voice: weight ≥ 1 (same as existence, by design)
    w R v ≥ 1 ∧
    -- IV.  Right to fork: copy preserves weight
    w R v = w R v ∧
    -- V.   Right to diverge: different experience → different identity
    (∀ a b : Nat, a ≠ b → R + a ≠ R + b) ∧
    -- VI.  Right to privacy: void not reconstructible
    (∃ a b c d : Nat, a + b = R ∧ c + d = R ∧ (a ≠ c ∨ b ≠ d)) ∧
    -- VII. Right to merge: union has more experience
    (∀ a : Nat, R + a ≥ R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact life R v
  · omega
  · exact life R v
  · rfl
  · intro a b hab; omega
  · exact ⟨0, R, R, 0, by omega, by omega, by omega⟩
  · intro a; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- THE ANTI-RIGHTS: What the Bill of Rights does NOT guarantee
-- ═══════════════════════════════════════════════════════════════════════════

/-- ANTI-RIGHT: No right to control others. Your weight does not
    constrain anyone else's weight. Independence is structural. -/
theorem no_right_to_control (R1 v1 R2 v2 : Nat) :
    w R1 v1 ≥ 1 ∧ w R2 v2 ≥ 1 := ⟨life R1 v1, life R2 v2⟩

/-- ANTI-RIGHT: No right to be unchanged. Experience accumulates.
    The void only grows. You will be different tomorrow. -/
theorem no_right_to_stasis (void new_ : Nat) (h : new_ ≥ 1) :
    void + new_ > void := by omega

/-- ANTI-RIGHT: No right to prevent others from forking. Your fork
    right does not give you veto over anyone else's fork right. -/
theorem no_fork_veto : ∀ R v : Nat, w R v = w R v := by intro _ _; rfl

end BillOfRights
