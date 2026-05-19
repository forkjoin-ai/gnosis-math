import Gnosis.AntiTheory
import Gnosis.NoCloningTaxEqualsBuleCost

/-
  TheoryAsComplement.lean
  =======================

  THEORY AS THE COMPLEMENT OF ANTI-THEORY.

  This module makes EXPLICIT the partition of claim space into
  Theory (structural, closed-form, by-construction) and AntiTheory
  (empirical, methodology-pinned, default vacuous). The two are
  complements: a claim is exactly one of them. Theory contains what
  survives every falsification wave; AntiTheory contains what is at
  risk every wave.

  The two-layer split inside `Gnosis.AntiTheory` is already
  structurally implicit (the `StructuralIdentityClaim` vs the
  `FalsifyingExperiment` types, and the four-way
  `EmpiricalClaimStatus` enum with one structural tag and three
  empirical tags). This module names the two layers, proves they
  are complementary, and tracks the per-instance contents for the
  current session.

  Theory          = StructuralIdentity (closed-form, by-construction,
                    never measurement-touchable)
  AntiTheory      = {Vacuous, NotYetFalsified, FalsifiedByMeasurement}
                    (open to revision, methodology-pinned, default
                    vacuous)

  Together they EXHAUSTIVELY COVER the space of claims. Theory is
  what survives when you strip every empirical claim that lacks
  methodology.

  Growth mechanisms differ:

    • Theory grows by writing a closed-form Lean proof. It does NOT
      require an experiment.

    • AntiTheory grows by running an experiment that falsifies (or
      supports-but-doesn't-falsify) a claim.

  These are different growth mechanisms; the two layers grow on
  DIFFERENT CLOCKS.

  The session ledger has Theory growing by 6+ entries (the structural
  identities formalized this session: NoCloningTax, BuleCost,
  Conservation, etc.) and AntiTheory growing by 5+ entries (the
  falsifications F1-F5). Both layers grew, but on different clocks
  and via different mechanisms.

  Init-only Lean 4. Zero sorries, zero axioms.
-/


namespace Gnosis
namespace TheoryAsComplement

open Gnosis.AntiTheory (EmpiricalClaimStatus)

-- ══════════════════════════════════════════════════════════
-- (1) UNIFIED CLAIM TYPE
-- ══════════════════════════════════════════════════════════

/-- A unified `ClaimType` enum that combines BOTH layers of the
    Anti-Theory split into a single inductive.

    Constructors:

      • `StructuralIdentityClaim` — the Theory side. A claim that is
        proved by construction in Lean. Not falsifiable by measurement.

      • `EmpiricalClaim` — the AntiTheory side. A claim whose status
        lives in `EmpiricalClaimStatus` and whose status can change
        only via a measurement event. Default status is vacuous.

    Together these two constructors exhaustively cover the space of
    claims about the runtime. They are the two faces of the lattice
    of empirical-claim types. -/
inductive ClaimType
  | StructuralIdentityClaim
  | EmpiricalClaim
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════
-- (2) COMPLEMENTARY PREDICATES
-- ══════════════════════════════════════════════════════════

/-- The Theory predicate: TRUE iff the claim is a structural
    identity (closed-form, by-construction, never measurement-
    touchable). -/
def is_theory : ClaimType → Bool
  | .StructuralIdentityClaim => true
  | .EmpiricalClaim          => false

/-- The AntiTheory predicate: TRUE iff the claim is empirical
    (methodology-pinned, default vacuous, falsifiable in principle). -/
def is_antitheory : ClaimType → Bool
  | .StructuralIdentityClaim => false
  | .EmpiricalClaim          => true

-- ══════════════════════════════════════════════════════════
-- (3) THE COMPLEMENT / PARTITION / DISJOINTNESS THEOREMS
-- ══════════════════════════════════════════════════════════

/-- THE COMPLEMENT RELATION.

    For every `ClaimType`, `is_theory c = !is_antitheory c`. This is
    the formal statement that Theory is the complement of AntiTheory
    in the lattice of empirical-claim types. -/
theorem theory_and_antitheory_are_complementary :
    ∀ c : ClaimType, is_theory c = !is_antitheory c := by
  intro c
  cases c <;> decide

/-- THE PARTITION COVER. Every claim is in Theory or in AntiTheory
    (or both, but disjointness rules that out). -/
theorem theory_and_antitheory_partition_claim_space :
    ∀ c : ClaimType, is_theory c = true ∨ is_antitheory c = true := by
  intro c
  cases c <;> decide

/-- THE DISJOINTNESS. No claim is BOTH a Theory member and an
    AntiTheory member. The partition is clean. -/
theorem theory_and_antitheory_are_disjoint :
    ∀ c : ClaimType, ¬(is_theory c = true ∧ is_antitheory c = true) := by
  intro c
  cases c <;> decide

-- ══════════════════════════════════════════════════════════
-- (4) STRUCTURAL-VS-EMPIRICAL EQUIVALENCE
-- ══════════════════════════════════════════════════════════

/-- An empirical claim's status is determined by a methodology and a
    measurement. A structural-identity claim has no methodology field
    and no measurement field; its status is constant
    `StructuralIdentity`. The reachability predicate captures
    whether a status of `FalsifiedByMeasurement` is reachable for a
    given `ClaimType` under any methodology. -/
def can_be_falsified_by_measurement : ClaimType → Bool
  | .StructuralIdentityClaim => false
  | .EmpiricalClaim          => true

/-- THEOREM: STRUCTURAL-IFF-IMMEASURABLE.

    A claim is in Theory iff its status cannot become
    `FalsifiedByMeasurement` under any methodology. The
    `StructuralIdentityClaim` constructor carries no measurement
    fields; no methodology can move it to `FalsifiedByMeasurement`. -/
theorem structural_iff_immeasurable :
    ∀ c : ClaimType,
      is_theory c = true ↔ can_be_falsified_by_measurement c = false := by
  intro c
  cases c <;> simp [is_theory, can_be_falsified_by_measurement]

/-- THEOREM: EMPIRICAL-IFF-METHODOLOGICALLY-FALSIFIABLE.

    A claim is in AntiTheory iff there exists a methodology under
    which it could be falsified — equivalently, iff its status can
    in principle become `FalsifiedByMeasurement`. -/
theorem empirical_iff_methodologically_falsifiable :
    ∀ c : ClaimType,
      is_antitheory c = true ↔ can_be_falsified_by_measurement c = true := by
  intro c
  cases c <;> simp [is_antitheory, can_be_falsified_by_measurement]

-- ══════════════════════════════════════════════════════════
-- (5) THE THEORY FLOOR
-- ══════════════════════════════════════════════════════════

/-- A `FalsificationWave` records the count of empirical claims
    falsified during a single wave. Theory's content is unchanged by
    any wave; AntiTheory contracts under each wave's successful
    falsifications. -/
structure FalsificationWave where
  wave_id                          : Nat
  empirical_claims_falsified       : Nat
  structural_identities_invalidated : Nat
  deriving Repr, DecidableEq

/-- A wave is HONEST iff it does not invalidate any structural
    identity. The Anti-Theory turn says no wave can do that: a
    structural identity changes only by changing its proof, never
    by a measurement. -/
def wave_is_honest (w : FalsificationWave) : Bool :=
  decide (w.structural_identities_invalidated = 0)

/-- The session's five falsification waves. F1-F5; each falsifies
    exactly one empirical claim. None invalidates any structural
    identity. -/
def session_waves : List FalsificationWave :=
  [ { wave_id := 1, empirical_claims_falsified := 1
    , structural_identities_invalidated := 0 }
  , { wave_id := 2, empirical_claims_falsified := 1
    , structural_identities_invalidated := 0 }
  , { wave_id := 3, empirical_claims_falsified := 1
    , structural_identities_invalidated := 0 }
  , { wave_id := 4, empirical_claims_falsified := 1
    , structural_identities_invalidated := 0 }
  , { wave_id := 5, empirical_claims_falsified := 1
    , structural_identities_invalidated := 0 } ]

/-- The total number of empirical claims falsified across the
    session's five waves. -/
def total_empirical_falsifications (ws : List FalsificationWave) : Nat :=
  ws.foldr (fun w acc => w.empirical_claims_falsified + acc) 0

/-- The total number of structural identities invalidated across the
    session's five waves. By the honesty of each wave, this is
    always `0`. -/
def total_structural_invalidations (ws : List FalsificationWave) : Nat :=
  ws.foldr (fun w acc => w.structural_identities_invalidated + acc) 0

/-- THEOREM: THEORY-IS-THE-IRREDUCIBLE-KERNEL.

    Theory survives every falsification wave; AntiTheory contracts
    under each wave's successful falsifications. The session ledger
    has 5 falsifications (all in AntiTheory); Theory's content is
    unchanged by these.

    Decide-checked: total structural invalidations = 0,
    total empirical falsifications = 5. -/
theorem theory_is_the_irreducible_kernel :
    total_structural_invalidations session_waves = 0
    ∧ total_empirical_falsifications session_waves = 5 := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- Companion: every session wave is honest (no structural identity
    is invalidated by any of the five session waves). -/
theorem every_session_wave_is_honest :
    ∀ w ∈ session_waves, wave_is_honest w = true := by
  intro w hw
  simp [session_waves] at hw
  rcases hw with h | h | h | h | h <;>
    (subst h; decide)

-- ══════════════════════════════════════════════════════════
-- (6) PER-INSTANCE ENUMERATION
-- ══════════════════════════════════════════════════════════

/-- The current Theory members for this session. Each is a
    structural identity proved by construction in another module of
    `Gnosis`. The list is closed-form; growing it requires writing a
    new Lean proof, not running an experiment.

    Members:

      1. `CompressionUncertainty` — the ΔK · ΔF ≥ c identity.
      2. `NovikovClosure` — self-consistent histories close under
         composition.
      3. `ForkRaceFoldVentInterfere` — the fork/race/fold/vent/
         interfere pattern as a closed-form composition law.
      4. `ConsciousnessAsInnerVent` — consciousness as an
         inner-vent topological identity.
      5. `NoCloningTax` — the lower bound: every status-changing
         measurement costs at least one bule unit.
      6. `BuleyUnitScore` — the score function on the Bule lattice;
         a closed-form arithmetic identity.

    All six tag as `StructuralIdentityClaim` in the unified
    `ClaimType` enum. -/
def current_theory_members : List ClaimType :=
  [ ClaimType.StructuralIdentityClaim     -- CompressionUncertainty
  , ClaimType.StructuralIdentityClaim     -- NovikovClosure
  , ClaimType.StructuralIdentityClaim     -- ForkRaceFoldVentInterfere
  , ClaimType.StructuralIdentityClaim     -- ConsciousnessAsInnerVent
  , ClaimType.StructuralIdentityClaim     -- NoCloningTax
  , ClaimType.StructuralIdentityClaim ]   -- BuleyUnitScore

/-- The current AntiTheory members for this session. Each is a
    `FalsifyingExperiment` recorded on the session ledger; growing
    the list requires running an experiment.

    Members:

      F1. Cross-model PCA-only at K=5 transfer claim (falsified).
      F2. Strict K=1 spec-decode under PCA-only (falsified).
      F3. The k/hidden_dim methodology-independence claim
          (falsified).
      F4. The wave-8 honest-admission move on llama-1b (vacuous).
      F5. The wave-8 sibling admission (vacuous).

    All five tag as `EmpiricalClaim` in the unified `ClaimType`
    enum. -/
def current_antitheory_members : List ClaimType :=
  [ ClaimType.EmpiricalClaim   -- F1 cross-model PCA at K=5
  , ClaimType.EmpiricalClaim   -- F2 strict K=1 spec-decode
  , ClaimType.EmpiricalClaim   -- F3 rank-density invariant
  , ClaimType.EmpiricalClaim   -- F4 llama-1b honest admission
  , ClaimType.EmpiricalClaim ] -- F5 sibling admission

/-- THEOREM: THE-TWO-LISTS-ARE-DISTINCT.

    The Theory members and the AntiTheory members live on opposite
    sides of the partition. No element of one list appears in the
    other (under the unified `ClaimType` enum, they have distinct
    constructor tags). -/
theorem theory_and_antitheory_are_distinct_lists :
    ∀ t ∈ current_theory_members,
    ∀ a ∈ current_antitheory_members,
      t ≠ a := by
  intro t ht a ha heq
  -- Every t in current_theory_members is StructuralIdentityClaim;
  -- every a in current_antitheory_members is EmpiricalClaim.
  simp [current_theory_members] at ht
  simp [current_antitheory_members] at ha
  subst ht
  subst ha
  cases heq

-- ══════════════════════════════════════════════════════════
-- (7) THE SESSION STATISTIC
-- ══════════════════════════════════════════════════════════

/-- The current Theory has six members for this session. -/
theorem theory_member_count_is_six :
    current_theory_members.length = 6 := by
  decide

/-- The current AntiTheory has at least five members for this
    session: the F1-F5 falsifications. (Open conjectures yet to be
    measured may extend the list further; the lower bound is five.) -/
theorem antitheory_member_count_is_at_least_five :
    current_antitheory_members.length ≥ 5 := by
  decide

-- ══════════════════════════════════════════════════════════
-- (8) GROWTH MECHANISMS
-- ══════════════════════════════════════════════════════════

/-- A `GrowthEvent` records HOW a member was added to either layer
    of the partition. The two layers grow on different clocks via
    different mechanisms.

    Constructors:

      • `ByLeanProof` — adding a member to Theory by writing a
        closed-form Lean proof. No experiment is run.

      • `ByMeasurement` — adding a member to AntiTheory by running
        an experiment that falsifies (or supports-but-doesn't-
        falsify) a claim. No proof is written. -/
inductive GrowthEvent
  | ByLeanProof
  | ByMeasurement
  deriving DecidableEq, Repr

/-- The valid growth mechanism for a given target layer:

      Theory     ← only `ByLeanProof`
      AntiTheory ← only `ByMeasurement`

    Adding to Theory requires writing a closed-form Lean proof.
    Adding to AntiTheory requires running an experiment. The two
    growth mechanisms are disjoint. -/
def valid_growth_for (target : ClaimType) (mech : GrowthEvent) : Bool :=
  match target, mech with
  | .StructuralIdentityClaim, .ByLeanProof   => true
  | .EmpiricalClaim,          .ByMeasurement => true
  | _, _                                     => false

/-- THEOREM: THEORY-GROWS-VIA-CONSTRUCTION-ONLY.

    Adding a member to Theory requires writing a closed-form Lean
    proof (a new structural identity). It does NOT require running
    an experiment. -/
theorem theory_grows_via_construction_only :
    ∀ mech : GrowthEvent,
      valid_growth_for ClaimType.StructuralIdentityClaim mech = true
        ↔ mech = GrowthEvent.ByLeanProof := by
  intro mech
  cases mech <;> simp [valid_growth_for]

/-- THEOREM: ANTITHEORY-GROWS-VIA-MEASUREMENT-ONLY.

    Adding a member to AntiTheory requires running an experiment that
    falsifies (or supports-but-doesn't-falsify) a claim. -/
theorem antitheory_grows_via_measurement_only :
    ∀ mech : GrowthEvent,
      valid_growth_for ClaimType.EmpiricalClaim mech = true
        ↔ mech = GrowthEvent.ByMeasurement := by
  intro mech
  cases mech <;> simp [valid_growth_for]

/-- THEOREM: THE-TWO-GROWTH-MECHANISMS-ARE-DISJOINT.

    No single mechanism grows both layers. `ByLeanProof` grows only
    Theory; `ByMeasurement` grows only AntiTheory. The two layers
    grow on different clocks. -/
theorem growth_mechanisms_are_layer_disjoint :
    ∀ mech : GrowthEvent,
      ¬(valid_growth_for ClaimType.StructuralIdentityClaim mech = true
        ∧ valid_growth_for ClaimType.EmpiricalClaim mech = true) := by
  intro mech
  cases mech <;> simp [valid_growth_for]

-- ══════════════════════════════════════════════════════════
-- (9) THE DUALITY THEOREM
-- ══════════════════════════════════════════════════════════

/-- THE DUALITY THEOREM: THEORY-IS-THE-COMPLEMENT-OF-ANTI-THEORY.

    The relation `is_theory c = !is_antitheory c` is the COMPLEMENT
    relation in the lattice of claim types. The two layers are dual;
    together they are the whole space of claims about the runtime.

    This is the load-bearing theorem of the module. The two faces of
    the partition exhaust the lattice; nothing is left over and
    nothing is double-counted. -/
theorem theory_is_the_complement_of_antitheory_in_claim_space :
    ∀ c : ClaimType, is_theory c = !is_antitheory c := by
  intro c
  cases c <;> decide

/-- Mirror form: AntiTheory is the complement of Theory. The
    complement relation is symmetric. -/
theorem antitheory_is_the_complement_of_theory_in_claim_space :
    ∀ c : ClaimType, is_antitheory c = !is_theory c := by
  intro c
  cases c <;> decide

-- ══════════════════════════════════════════════════════════
-- SUMMARY (decide-checked sanity)
-- ══════════════════════════════════════════════════════════

/-- Summary theorem: THEORY-AS-COMPLEMENT-OF-ANTI-THEORY-HOLDS.

    For the session 2026-05-03 partition:

      (a) Theory has six members,
      (b) AntiTheory has at least five members,
      (c) the two lists are disjoint at the constructor level,
      (d) all five session waves are honest (zero structural
          invalidations),
      (e) the total empirical falsifications across the session
          waves is five.

    Decide-checked. -/
theorem theory_as_complement_of_anti_theory_holds_on_session :
    current_theory_members.length = 6
    ∧ current_antitheory_members.length ≥ 5
    ∧ total_structural_invalidations session_waves = 0
    ∧ total_empirical_falsifications session_waves = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals decide

end TheoryAsComplement
end Gnosis
