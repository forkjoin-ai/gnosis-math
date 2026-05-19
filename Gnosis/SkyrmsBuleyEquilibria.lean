import Init
import Gnosis.GodFormula
import Gnosis.NashSkyrmsBuleyKernelLadder

namespace Gnosis
namespace SkyrmsBuleyEquilibria

open Gnosis (godWeight godWeight_ceiling)
open Gnosis.NashSkyrmsBuleyKernelLadder (skyrmsLevel buleyLevel)

/-!
# Explicit Skyrms and Buley equilibria

This module makes the two middle rungs explicit as executable equilibrium
contracts, in the same spirit as `NashProgram`:

- Skyrms equilibrium: convention-coordination fixed point.
- Buley equilibrium: temporal (past/present/future) closure fixed point.
- Both expose a vent channel and a God-weight certificate.
-/

/-- Unsigned gap on `Nat` (coordination disagreement). -/
def natGap (x y : Nat) : Nat :=
  if _ : x ≤ y then y - x else x - y

theorem natGap_self (x : Nat) : natGap x x = 0 := by
  unfold natGap
  simp

/-- `natGap` vanishes iff the operands coincide (**Init** lattice read on `Nat`). -/
theorem natGap_eq_zero_iff (x y : Nat) : natGap x y = 0 ↔ x = y := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy x y with xLt | heq | yLt
    · unfold natGap at h
      have hxy : x ≤ y := Nat.le_of_lt xLt
      rw [dif_pos hxy] at h
      have pos : 0 < y - x := Nat.sub_pos_of_lt xLt
      rw [h] at pos
      exact absurd pos (Nat.lt_irrefl _)
    · exact heq
    · unfold natGap at h
      have hxy : ¬ x ≤ y := Nat.not_le_of_gt yLt
      rw [dif_neg hxy] at h
      have pos : 0 < x - y := Nat.sub_pos_of_lt yLt
      rw [h] at pos
      exact absurd pos (Nat.lt_irrefl _)
  · intro hxy
    subst hxy
    exact natGap_self x

/-! ## Skyrms equilibrium (collective convention) -/

structure SkyrmsState where
  a1 : Nat
  a2 : Nat

/-- Coordination update to common target convention. -/
def skyrmsUpdate (target : Nat) (_s : SkyrmsState) : SkyrmsState :=
  { a1 := target, a2 := target }

/-- Skyrms equilibrium: both agents share one convention and are fixed by update. -/
def IsSkyrmsEquilibrium (target : Nat) (s : SkyrmsState) : Prop :=
  s.a1 = s.a2 ∧ skyrmsUpdate target s = s

/-- Vent as disagreement gap between conventions. -/
def skyrmsVent (s : SkyrmsState) : Nat := natGap s.a1 s.a2

/-- God-weight for Skyrms state at budget `R`. -/
def skyrmsWeight (R : Nat) (s : SkyrmsState) : Nat := godWeight R (skyrmsVent s)

theorem skyrms_equilibrium_has_zero_vent (target : Nat) (s : SkyrmsState)
    (h : IsSkyrmsEquilibrium target s) : skyrmsVent s = 0 := by
  unfold skyrmsVent
  rw [h.1]
  exact natGap_self s.a2

theorem skyrms_equilibrium_reaches_ceiling (R target : Nat) (s : SkyrmsState)
    (h : IsSkyrmsEquilibrium target s) :
    skyrmsWeight R s = R + 1 := by
  unfold skyrmsWeight
  rw [skyrms_equilibrium_has_zero_vent target s h]
  exact godWeight_ceiling R

theorem skyrms_hexad_witness :
    IsSkyrmsEquilibrium skyrmsLevel { a1 := skyrmsLevel, a2 := skyrmsLevel } := by
  constructor
  · rfl
  · rfl

/-! ## Buley equilibrium (retrocausal temporal closure)

Picture a **stone arch**: past and future read as the legs that **bear** the span; the
present is the **keystone**—the piece that sits at the apex and locks compression into
a single load path. In this model that load path is explicit: the present is the **joint**
where past and future meet in one number, `(past + future)/2` (floor average on `Nat`).

The full training or narrative trajectory is not a clean arch in isolation; treat it as a
**tangled Gordian knot** of dependencies. What stays formal is the **connection point**:
the same keystone is exactly where the temporal update may **close back on itself**—an
equilibrium is a state where that joint already matches the closure target and the operator
is **fixed** (`buleyUpdate s = s`). The distinguished locus is transition, not naive separation.
-/

structure BuleyState where
  past : Nat
  present : Nat
  future : Nat

/-- Temporal closure operator (retrocausal balancing):
present becomes midpoint of past/future (Nat floor average). -/
def buleyUpdate (s : BuleyState) : BuleyState :=
  { past := s.past
    present := (s.past + s.future) / 2
    future := s.future }

/-- Buley equilibrium: temporal closure already holds and update is fixed. -/
def IsBuleyEquilibrium (s : BuleyState) : Prop :=
  s.present = (s.past + s.future) / 2 ∧ buleyUpdate s = s

/-- Vent as temporal mismatch between realized present and closure target. -/
def buleyVent (s : BuleyState) : Nat :=
  natGap s.present ((s.past + s.future) / 2)

def buleyWeight (R : Nat) (s : BuleyState) : Nat := godWeight R (buleyVent s)

theorem buley_equilibrium_has_zero_vent (s : BuleyState)
    (h : IsBuleyEquilibrium s) : buleyVent s = 0 := by
  unfold buleyVent
  rw [h.1]
  exact natGap_self ((s.past + s.future) / 2)

/-- Temporal vent vanishes iff **Buley** closure already holds (midpoint + fixed update). -/
theorem buleyVent_eq_zero_iff (s : BuleyState) :
    buleyVent s = 0 ↔ IsBuleyEquilibrium s := by
  constructor
  · intro hz
    unfold buleyVent at hz
    have hm : s.present = (s.past + s.future) / 2 :=
      (natGap_eq_zero_iff _ _).mp hz
    refine ⟨hm, ?_⟩
    cases s with
    | mk past present future =>
      dsimp only [buleyUpdate]
      rw [← hm]
  · intro h
    exact buley_equilibrium_has_zero_vent s h

theorem buley_equilibrium_reaches_ceiling (R : Nat) (s : BuleyState)
    (h : IsBuleyEquilibrium s) :
    buleyWeight R s = R + 1 := by
  unfold buleyWeight
  rw [buley_equilibrium_has_zero_vent s h]
  exact godWeight_ceiling R

/-! ### Dynamical contraction: **`buleyUpdate` folds any present slack in one step** -/

/--
One **`buleyUpdate`** application **always lands on** `IsBuleyEquilibrium` — the present tile is forced
onto the midpoint of the pinned `(past,future)` pair regardless of the legacy present value.

This formalizes deterministic “re-fold’’ of mismatch into closure **without any uniqueness claim** —
many equilibria remain compatible once the midpoint law holds.
-/
theorem isBuleyEquilibrium_buleyUpdate (s : BuleyState) :
    IsBuleyEquilibrium (buleyUpdate s) := by
  constructor <;> rfl

/-- Auxiliary: **`buleyUpdate` agrees with identity** exactly when the midpoint law holds on `present`. -/
theorem buleyUpdate_eq_self_of_midpoint (s : BuleyState)
    (h : s.present = (s.past + s.future) / 2) : buleyUpdate s = s := by
  cases s
  simp_all [buleyUpdate]

/-- Projection is **idempotent** along the **`buleyUpdate`** map. -/
theorem buleyUpdate_idempotent (s : BuleyState) :
    buleyUpdate (buleyUpdate s) = buleyUpdate s := by
  rfl

/-- Off-equilibrium start still yields **`buleyVent = 0`** after one closure fold. -/
theorem buleyVent_zero_after_buleyUpdate (s : BuleyState) :
    buleyVent (buleyUpdate s) = 0 :=
  buley_equilibrium_has_zero_vent _ (isBuleyEquilibrium_buleyUpdate s)

/--
Any **`Buley` equilibrium** induces an **aligned Skyrms** certificate: both convention coordinates
sit on the sealed present (target-coherent lockstep).

This is consistency between rungs (**Skyrms** convention inside **Buley** closure); it is not “Skyrms
implies Buley’’.
-/
theorem buley_equilibrium_induces_aligned_skyrms (s : BuleyState)
    (_h : IsBuleyEquilibrium s) :
    IsSkyrmsEquilibrium s.present { a1 := s.present, a2 := s.present } := by
  constructor <;> rfl

/-- **`Buley` equilibria are not unique** — many distinct `(past,future)` pairs share the same sealed present. -/
theorem buley_equilibrium_nonunique_witness :
    ∃ s₁ s₂ : BuleyState,
      s₁ ≠ s₂ ∧
      IsBuleyEquilibrium s₁ ∧
      IsBuleyEquilibrium s₂ :=
  let s₁ : BuleyState := { past := 2, present := 2, future := 2 }
  let s₂ : BuleyState := { past := 1, present := 2, future := 3 }
  have h₁₂ : s₁ ≠ s₂ := by
    intro hs
    cases congrArg BuleyState.past hs
  have hm₁ : @BuleyState.present s₁ = (s₁.past + s₁.future) / 2 := by
    show (2 : Nat) = (2 + 2) / 2
    native_decide
  have hm₂ : @BuleyState.present s₂ = (s₂.past + s₂.future) / 2 := by
    show (2 : Nat) = (1 + 3) / 2
    native_decide
  have hEq₁ : IsBuleyEquilibrium s₁ :=
    ⟨hm₁, buleyUpdate_eq_self_of_midpoint s₁ hm₁⟩
  have hEq₂ : IsBuleyEquilibrium s₂ :=
    ⟨hm₂, buleyUpdate_eq_self_of_midpoint s₂ hm₂⟩
  ⟨s₁, s₂, h₁₂, hEq₁, hEq₂⟩

theorem buley_decad_witness :
    IsBuleyEquilibrium { past := buleyLevel, present := buleyLevel, future := buleyLevel } := by
  constructor
  · decide
  · rfl

/-! ## Joint certificate (explicit middle-rung equilibrium layer) -/

theorem skyrms_buley_joint_equilibrium_certificate (R : Nat) :
    skyrmsWeight R { a1 := skyrmsLevel, a2 := skyrmsLevel } = R + 1 ∧
    buleyWeight R { past := buleyLevel, present := buleyLevel, future := buleyLevel } = R + 1 := by
  refine ⟨?_, ?_⟩
  · exact skyrms_equilibrium_reaches_ceiling R skyrmsLevel
      { a1 := skyrmsLevel, a2 := skyrmsLevel } skyrms_hexad_witness
  · exact buley_equilibrium_reaches_ceiling R
      { past := buleyLevel, present := buleyLevel, future := buleyLevel } buley_decad_witness

/-! ## Strict dominance chain on equilibrium levels -/

/-- Dominance as strict level superiority. -/
def Dominates (x y : Nat) : Prop := x > y

/-- Nash anchor level from the ladder. -/
def nashLevel : Nat := Gnosis.NashSkyrmsBuleyKernelLadder.nashLevel

theorem skyrms_strictly_dominates_nash :
    Dominates skyrmsLevel nashLevel := by
  unfold Dominates skyrmsLevel nashLevel
  decide

theorem buley_strictly_dominates_skyrms :
    Dominates buleyLevel skyrmsLevel := by
  unfold Dominates buleyLevel skyrmsLevel
  decide

theorem buley_strictly_dominates_nash :
    Dominates buleyLevel nashLevel := by
  unfold Dominates buleyLevel nashLevel
  decide

/-- Combined strict dominance chain requested:
`Buley > Skyrms > Nash`. -/
theorem buley_skyrms_nash_strict_chain :
    Dominates buleyLevel skyrmsLevel ∧
    Dominates skyrmsLevel nashLevel ∧
    Dominates buleyLevel nashLevel := by
  exact ⟨buley_strictly_dominates_skyrms,
    skyrms_strictly_dominates_nash,
    buley_strictly_dominates_nash⟩

/-! ## Temporal-role interpretation -/

inductive TemporalRole where
  | past
  | present
  | future
  deriving DecidableEq, Repr

/-- Nash rung as present-time anchor. -/
def nashTemporalRole : TemporalRole := .present

/-- Skyrms rung as past-time convention memory. -/
def skyrmsTemporalRole : TemporalRole := .past

/-- Buley rung as future-time retrocausal closure target. -/
def buleyTemporalRole : TemporalRole := .future

theorem nash_is_present : nashTemporalRole = .present := rfl
theorem skyrms_is_past : skyrmsTemporalRole = .past := rfl
theorem buley_is_future : buleyTemporalRole = .future := rfl

theorem temporal_role_assignment_certificate :
    nashTemporalRole = .present ∧
    skyrmsTemporalRole = .past ∧
    buleyTemporalRole = .future := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Temporal coordination scopes ("who sees which moments")

Interpretation ladder for training / buleyean-rl sequencing:

- **Nash (`present`).** Coordination anchored at the current step only —
  no explicit coupling to accumulated history or projected continuation.
- **Skyrms (`past`).** Convention coordination uses backward-looking stability;
  scope includes everything up to **and including** the present ledger, but does
  not treat the unknowable continuation as fixed.
- **Buley (`future`).** Retrocausal **closure**: the present fold is constrained
  by *both* archived past and stipulated future endpoints — so the future mode
  is not "separate" from past and present.

**Scope.** This section formalizes ontology for the *coordination object's* temporal span and
pairs it with discrete closure operators (`TimeIndex`, scopes, `buleyUpdate`). It does **not**
nor refutes closed timelike curves (CTCs) as physics. Globally hyperbolic Lorentzian geometry is
one modelling tradition; solutions of Einstein's equations with CTCs are another—it is coherent
(for some energy-condition and cosmic-censorship viewpoints, controversial) to treat CTC-containing
sectors as unresolved rather than absurd. Readers who intend a physical reading must supply a
separate layered model—the present module only certifies coordinated closure on the algebraic side.

**Arrow (discrete)—the certificate-grade sense of “time’’ here.**

`Gnosis` does not certify a continuum thermodynamic arrow or a Lorentzian causal orientation in this module.
The discernible **direction** is carried by **stability structure**, not by a void:

- **`buleyUpdate`** folds toward **midpoint closure** once **`past`** and **`future`** are pinned; without those legs—or any fixed target—you are in an untyped **vacuum** where mismatch has **nothing definite to drain toward** (**`buleyVent`** has no asymmetric story).
- **Skyrms** needs a **declared convention `target`**; **Nash** (here, present-only modality) anchors on the **immediate coordinate** alone.

The arrow therefore shows up **exactly as strongly as** the stability contract you supply—even “only’’ is enough: one **`Is*Equilibrium`**, zero vent, or one **`buleyUpdate`** re-fold turns underdetermination into something a proof can discriminate.

What *is* pinned is still a workable **orientation package**:

1. **Step morphisms** — `Nat` succession and **`buleyUpdate`** advance or **re-fold** the formal state along a definite direction rule (slack present → midpoint on pinned legs in one **`buleyUpdate`** shot).
2. **Axis labels** — `TimeIndex.{pastIdx,presentIdx,futureIdx}` name the coarse **triple** `{Past,Present,Future}` coordination refers to before any metric (*cf.* **`TemporalRole`** for ladder tagging).
3. **Vent monotone toward closure** — **mismatch (`buleyVent`/`skyrmsVent`) drains to zero** at equilibrium while **`godWeight` hits ceiling `R + 1`**: a discrete “condense’’ reading—alignment over rejection—matching the **`+1`** clinamen underneath `GodFormula`.
4. **Scope refinement** — `nashScope → skyrmsScope → buleyScope` is a **(strict) widening** of what coordination may depend on (**`CoordinationScope` subsumption**): an informational “later rung remembers more indices’’ trajectory; see ascent bridges in **`Gnosis/NSBTemporalLadderAscent.lean`**.

Treat that quartet as **`Gnosis`’s algebraic arrow**: strong enough for proofs, modest enough **not** to smuggle continuum physics unless you adjoin a layered model explicitly.

For a complementary **purely discrete** cyclic tick (**Peano `+1` modular wrap on `Fin n`**, periodic worldline—also forward-step “arrow’’ with eventual return), see **`Gnosis/DiscreteClosedTimelikeStep.lean`**.
-/

/-- Coarse markers on the time axis (orthogonal to ladder `TemporalRole` labels). -/
inductive TimeIndex where
  | pastIdx
  | presentIdx
  | futureIdx
  deriving DecidableEq, Repr

abbrev CoordinationScope := TimeIndex → Prop

/-- Nash scope: **only** the present moment. -/
def nashScope : CoordinationScope
  | .presentIdx => True
  | .pastIdx | .futureIdx => False

/-- Skyrms scope: past **and** present; **not** the future as a fixed object. -/
def skyrmsScope : CoordinationScope
  | .pastIdx | .presentIdx => True
  | .futureIdx => False

/-- Buley scope: **all** moments — future closure couples the full axis. -/
def buleyScope : CoordinationScope := fun _ => True

/-- Scope subsumption: `S₁` is at least as wide as `S₂`. -/
def ScopeSubsumes (S₁ S₂ : CoordinationScope) : Prop :=
  ∀ m, S₂ m → S₁ m

theorem buley_scope_subsumes_skyrms : ScopeSubsumes buleyScope skyrmsScope := by
  intro m hm
  cases m <;> trivial

theorem buley_scope_subsumes_nash : ScopeSubsumes buleyScope nashScope := by
  intro m hm
  cases m <;> first | trivial | contradiction

theorem skyrms_scope_subsumes_nash : ScopeSubsumes skyrmsScope nashScope := by
  intro m hm
  cases m <;> first | trivial | cases hm

/-- **Future is not separate** from past and present under Buley:
all three indices lie in scope. -/
theorem buley_future_not_isolated_from_past_present :
    buleyScope TimeIndex.pastIdx ∧
    buleyScope TimeIndex.presentIdx ∧
    buleyScope TimeIndex.futureIdx := by
  refine ⟨trivial, trivial, trivial⟩

/-- **Present (Nash) is separate** from past and from future: both are out of scope. -/
theorem nash_present_separate_from_past_and_future :
    ¬ nashScope TimeIndex.pastIdx ∧ ¬ nashScope TimeIndex.futureIdx := by
  simp [nashScope]

/-- **Past (Skyrms) includes present** but **excludes** future as fixed term. -/
theorem skyrms_includes_present_excludes_future :
    skyrmsScope TimeIndex.pastIdx ∧
    skyrmsScope TimeIndex.presentIdx ∧
    ¬ skyrmsScope TimeIndex.futureIdx := by
  simp [skyrmsScope]

/-- **Future (Buley) contains all** moments on the axis. -/
theorem buley_scope_is_universal (m : TimeIndex) : buleyScope m := trivial

/-- Retrocausal closure (discrete): present is the joint fold of past and future. -/
theorem buley_present_is_midpoint_of_past_future (s : BuleyState)
    (h : IsBuleyEquilibrium s) :
    s.present = (s.past + s.future) / 2 :=
  h.1

end SkyrmsBuleyEquilibria
end Gnosis
