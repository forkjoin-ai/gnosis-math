import Init
import Gnosis.FiniteDynamicsCore

/-!
# Sardis-gate admissibility (Rustic Church, Init-only) — the reflexive turn

`QualityMarginCacheAdmissibility` applies Revelation's Sardis warning ("a name that
thou livest, and art dead") to *model* cache hits: a green status over a wrong token
is forbidden. This module turns the **same gate on the corpus itself**. The unit of
admission is not a logit vector but a *claim* — a theorem name, module banner, or
lineage line — and the gate sorts it by the discipline `RUSTIC_CHURCH.md` already
states in prose: a name is not life; only the carrier still bearing weight under
`lake build` counts.

The encoding is deliberately minimal and honest. A `Claim` carries two `Nat`s:

* `carrier` — the count of obligations that actually close under `lake build` (the
  live witness: kernel-discharged proof weight).
* `label`   — the count its banner / name *asserts* are discharged.

A claim is **`Live`** (the manifesto's `StructuralByConstruction`) when the works bear
at least what the name claims (`label ≤ carrier`), and **`DeadName`** (Sardis-mode, the
manifesto's `VacuousNoExperimentSpecified`) when the name claims more than the carrier
bears (`carrier < label`). The gate `admits` is the decidable form of `Live`.

Three layers, all Init-only (named `Nat`/`Int` lemmas, **no `omega`**, no Mathlib, no
`simp`/`decide` on open-variable goals; `decide` only on closed `Nat` literals):

* **§1 The gate** — `live_iff_admits`, the dichotomy `live_or_dead`, exclusivity
  `not_live_and_dead`, and the Sardis refusal `dead_name_not_admitted`.
* **§2 Margin + tightness** — monotonicity (`more_carrier_preserves_live`,
  `more_label_cannot_revive`), the robustness bound `relabel_live_within_margin`
  (re-bannering within the honest headroom stays live), and the tightness antitheorem
  `relabel_dead_past_margin` with the closed flip witness `sardis_flip`: one claimed
  obligation past the margin tips a live claim into a dead name. This is `FRONTIER_CONTRACTS.md`
  in miniature — the emphatic-identity overclaim added with no new proof.
* **§3 The Gödel boundary, as an antitheorem** — `RUSTIC_CHURCH.md` (its opening
  section) claims that if `lake build` admits a Rustic-Church module, "internal
  consistency follows." That clause over-reaches: admission is a *local* carrier check;
  consistency is a *global* property; and (Gödel) no system proves its own consistency
  internally. `admission_does_not_force_consistency` is the honest replacement: admission
  cannot *force* an arbitrary global predicate, via `FiniteDynamicsCore.not_forced_by_witness`.

## What this does NOT prove

It does **not** prove the corpus consistent — that is the Gödel boundary, named in §3
and deliberately left open, not smuggled in. It proves the *gate* is sound within its
margin and tight beyond it, and that gate-passing is not consistency. Axioms: `propext`
only (the `decide` calls are closed and kernel-checked; the non-forcing schema is
axiom-free).
-/

namespace Gnosis
namespace SardisGateAdmissibility

/-- A corpus claim: `carrier` obligations actually close under `lake build`; the
banner / name *asserts* `label` of them. The whole Sardis warning lives in the
relation between these two numbers. -/
structure Claim where
  carrier : Nat
  label   : Nat

/-- **`Live` (StructuralByConstruction).** The works bear at least what the name
claims. -/
def Live (c : Claim) : Prop := c.label ≤ c.carrier

/-- **`DeadName` (Sardis-mode / VacuousNoExperimentSpecified).** The name claims more
than the carrier bears — "a name that thou livest, and art dead." -/
def DeadName (c : Claim) : Prop := c.carrier < c.label

/-- The decidable admission gate: the runtime form of `Live`. -/
def admits (c : Claim) : Bool := decide (c.label ≤ c.carrier)

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The gate: dichotomy, exclusivity, Sardis refusal
-- ═══════════════════════════════════════════════════════════════════════

/-- The gate decides `Live` exactly: `admits c = true ↔ Live c`. -/
theorem live_iff_admits (c : Claim) : Live c ↔ admits c = true := by
  unfold Live admits
  exact decide_eq_true_iff.symm

/-- Every claim is either live or a dead name — there is no third status (the
manifesto's two-layer sort is total). Init-only via `Nat.le_or_lt`. -/
theorem live_or_dead (c : Claim) : Live c ∨ DeadName c := by
  unfold Live DeadName
  exact (Nat.lt_or_ge c.carrier c.label).symm

/-- The two statuses are exclusive: no claim is simultaneously live and a dead name. -/
theorem not_live_and_dead (c : Claim) : ¬ (Live c ∧ DeadName c) := by
  intro h
  exact absurd h.left (Nat.not_le_of_lt h.right)

/-- **The Sardis refusal.** A dead name is not admitted: the gate returns `false`
exactly when the name out-runs the carrier. This is the operational point — the gate
cannot be passed by a label alone. -/
theorem dead_name_not_admitted (c : Claim) (h : DeadName c) : admits c = false := by
  unfold admits
  exact decide_eq_false (Nat.not_le_of_lt h)

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Margin (live witness) and tightness (Sardis signature)
-- ═══════════════════════════════════════════════════════════════════════

/-- Re-banner a claim: assert `delta` more discharged obligations without adding any
live carrier. The name grows, the works do not — the `FRONTIER_CONTRACTS.md` move. -/
def relabel (c : Claim) (delta : Nat) : Claim := { c with label := c.label + delta }

/-- **Monotone in works.** Adding live carrier never demotes a claim: the works can
only redeem the name. -/
theorem more_carrier_preserves_live (c : Claim) (extra : Nat)
    (h : Live c) : Live { c with carrier := c.carrier + extra } := by
  unfold Live at h ⊢
  exact Nat.le_trans h (Nat.le_add_right c.carrier extra)

/-- **Monotone in name (the wrong direction).** Inflating the banner without new works
never revives a dead name. -/
theorem more_label_cannot_revive (c : Claim) (extra : Nat)
    (h : DeadName c) : DeadName { c with label := c.label + extra } := by
  unfold DeadName at h ⊢
  exact Nat.lt_of_lt_of_le h (Nat.le_add_right c.label extra)

/-- **The margin bound (live witness).** If a claim has honest headroom `gamma`
(`label + gamma ≤ carrier`), then any re-bannering within that headroom (`delta ≤ gamma`)
stays live: scope you have actually earned can be claimed without going Sardis. -/
theorem relabel_live_within_margin (c : Claim) (gamma delta : Nat)
    (hmargin : c.label + gamma ≤ c.carrier) (hdelta : delta ≤ gamma) :
    Live (relabel c delta) := by
  unfold Live relabel
  show c.label + delta ≤ c.carrier
  exact Nat.le_trans (Nat.add_le_add_left hdelta c.label) hmargin

/-- **The tightness antitheorem (Sardis signature).** The bound is exactly tight: at
margin `gamma` (`carrier = label + gamma`), re-bannering one obligation past it
(`delta = gamma + 1`) tips the claim into a dead name. Beyond the earned headroom the
gate must refuse — as load-bearing as the bound itself. -/
theorem relabel_dead_past_margin (c : Claim) (gamma : Nat)
    (hexact : c.carrier = c.label + gamma) :
    DeadName (relabel c (gamma + 1)) := by
  unfold DeadName relabel
  show c.carrier < c.label + (gamma + 1)
  rw [hexact, ← Nat.add_assoc]
  exact Nat.lt_succ_self (c.label + gamma)

/-- A claim with 5 live obligations whose banner asserts exactly 5 (margin `gamma = 0`,
perfectly honest). -/
def honestClaim : Claim := { carrier := 5, label := 5 }

/-- **Closed flip witness.** `honestClaim` is `Live`; re-bannering it to assert one
obligation more than it bears (`delta = 1`) flips it to `DeadName`. The corpus
equivalent of an emphatic identity claim added with no new proof. Each conjunct is a
closed `Nat` goal, so `decide` is admitted by the Rustic Church contract. -/
theorem sardis_flip : Live honestClaim ∧ DeadName (relabel honestClaim 1) := by
  refine ⟨?_, ?_⟩
  · show (5 : Nat) ≤ 5; decide
  · show (5 : Nat) < 5 + 1; decide

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The Gödel boundary, as an antitheorem (the honest replacement)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Admission is not consistency.** `RUSTIC_CHURCH.md` claims in prose that if
`lake build` admits a Rustic-Church module, "internal consistency follows." That clause
over-reaches: admission is a *local* carrier check, consistency a *global* property, and
no system proves its own consistency internally. Formally, admission cannot *force* an
arbitrary global predicate `Consistent`: a single admitted claim for which `Consistent`
fails refutes "`Live` → `Consistent`" for all claims. This is
`FiniteDynamicsCore.not_forced_by_witness` instantiated on the gate — the honest,
Gödel-respecting replacement for the prose overclaim, in the corpus's own antitheorem
style. The corpus does not own the witness `w`; it owns the schema that turns any future
inconsistency-witness into a refutation of the overclaim. -/
theorem admission_does_not_force_consistency
    (Consistent : Claim → Prop) (w : Claim)
    (hw : Live w) (hnc : ¬ Consistent w) :
    ¬ (∀ c, Live c → Consistent c) :=
  Gnosis.FiniteDynamicsCore.not_forced_by_witness Live Consistent w hw hnc

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Master bundle
-- ═══════════════════════════════════════════════════════════════════════

/-- The gate's load-bearing facts as one carrier: decidability, totality of the sort,
exclusivity, and the closed Sardis flip. -/
theorem sardis_gate_bundle :
    (∀ c, Live c ↔ admits c = true) ∧
    (∀ c, Live c ∨ DeadName c) ∧
    (∀ c, ¬ (Live c ∧ DeadName c)) ∧
    (Live honestClaim ∧ DeadName (relabel honestClaim 1)) :=
  ⟨live_iff_admits, live_or_dead, not_live_and_dead, sardis_flip⟩

end SardisGateAdmissibility
end Gnosis
