import Init

namespace Gnosis
namespace SkymeshTeleport

/-!
# Skymesh teleport admission — Init-only shape

Mirrors `open-source/gnosis/rtlsdr-mock-sim/{skymesh-witness,skymesh}.ts`.

Two air-gapped RTL-SDR stations derive a witness from the SAME ambient sky and
each is admitted to the `geodesicLength:0` cached replay iff:

  1. it locked a witness off the air (`locked`),
  2. that witness AGREES with the reference -- a resilient top-K dominant-band
     overlap, `minShared ≤ shared` (`agree`),
  3. the protocol69 projection is canonical, broadcast XOR operand = 69
     (`projectionOk`), and
  4. no live foil veto (`foilOk = ¬ foilDenied`).

Per the Rustic Church bridge rule, the RF/hardware truth (that two NESDRs really
hear the same carrier) stays OUTSIDE Lean; here we prove only the finite
admission algebra: the four gates, the fail-closed boundaries, the resilience of
the agreement rule, the canonical projection, and geodesicLength = 0. No `omega`,
no `simp`/`decide` on open goals; `decide` only on closed numerics.
-/

/-- protocol69 broadcast symbol. -/
def broadcastSymbol : Nat := 66
/-- Local FOIL operand. -/
def localFoilOperand : Nat := 7
/-- Canonical projection value. -/
def expectedProjection : Nat := 69
/-- A teleported cache replay does not traverse compute space. -/
def geodesicLength : Nat := 0

/-- protocol69 projection: broadcast XOR local FOIL operand. -/
def projection (b o : Nat) : Nat := Nat.xor b o

/-- The canonical key projects to 69 (closed numeric). -/
theorem canonical_projection :
    projection broadcastSymbol localFoilOperand = expectedProjection := by
  decide

/-- A forged broadcast symbol (67, an attacker's near-miss) does NOT project to 69. -/
theorem forged_projection_not_canonical :
    projection 67 localFoilOperand ≠ expectedProjection := by
  decide

/-- A teleport replay never traverses compute space. -/
theorem geodesic_is_zero : geodesicLength = 0 := rfl

/--
Resilient witness agreement: the two stations share at least `minShared` of their
top-K dominant bands, modeled by the overlap count `shared`.
-/
def Agree (shared minShared : Nat) : Prop := minShared ≤ shared

/-- Agreement is monotone: more shared bands cannot break a lock. -/
theorem agree_monotone {shared shared' minShared : Nat}
    (h : Agree shared minShared) (hmono : shared ≤ shared') :
    Agree shared' minShared :=
  Nat.le_trans h hmono

/--
Resilience: with K top bands and threshold K-1, one band may differ between the
two receivers (the real gain/noise gap) and they still agree.
-/
theorem agree_tolerates_one_flip (k : Nat) : Agree (k - 1) (k - 1) :=
  Nat.le_refl (k - 1)

/-- Sharing all K top bands agrees at any threshold up to K. -/
theorem agree_full_share {shared minShared : Nat} (h : minShared ≤ shared) :
    Agree shared minShared := h

/-- Concrete: two shared bands meet a threshold of two. -/
theorem agree_two_of_three : Agree 2 2 := Nat.le_refl 2
/-- Concrete: one shared band fails a threshold of two (a different sky). -/
theorem disagree_one_of_three : ¬ Agree 1 2 := by
  unfold Agree
  decide

/-- The four admission gates for one station (mirrors `admitStation`). -/
structure Admission where
  /-- A witness was locked off the air. -/
  locked : Prop
  /-- The witness agrees with the reference (Skymesh: the same sky). -/
  agree : Prop
  /-- The protocol69 projection is canonical (= 69). -/
  projectionOk : Prop
  /-- No live foil veto. -/
  foilOk : Prop

/-- A station teleports iff all four gates hold. -/
def Admitted (a : Admission) : Prop :=
  a.locked ∧ a.agree ∧ a.projectionOk ∧ a.foilOk

theorem admitted_needs_lock (a : Admission) (h : Admitted a) : a.locked := h.1
theorem admitted_needs_agree (a : Admission) (h : Admitted a) : a.agree := h.2.1
theorem admitted_needs_projection (a : Admission) (h : Admitted a) : a.projectionOk := h.2.2.1
theorem admitted_needs_foil (a : Admission) (h : Admitted a) : a.foilOk := h.2.2.2

/-- The full shape: admission is exactly the conjunction of the four gates. -/
theorem admitted_iff (a : Admission) :
    Admitted a ↔ (a.locked ∧ a.agree ∧ a.projectionOk ∧ a.foilOk) :=
  Iff.rfl

/-- Unlocked: no witness off the air yet -> denied. -/
theorem unlocked_denied (a : Admission) (h : ¬ a.locked) : ¬ Admitted a :=
  fun adm => h (admitted_needs_lock a adm)

/-- MISS: a different sky (no agreement) -> denied. -/
theorem miss_denied (a : Admission) (h : ¬ a.agree) : ¬ Admitted a :=
  fun adm => h (admitted_needs_agree a adm)

/-- Fail-closed on a forged key: a non-canonical projection denies. -/
theorem forged_projection_denied (a : Admission) (h : ¬ a.projectionOk) : ¬ Admitted a :=
  fun adm => h (admitted_needs_projection a adm)

/-- Fail-closed on a live foil veto. -/
theorem foil_veto_denied (a : Admission) (h : ¬ a.foilOk) : ¬ Admitted a :=
  fun adm => h (admitted_needs_foil a adm)

/--
The teleport-security theorem: a station that genuinely heard the same sky
(`agree` holds) but presents a FORGED key (`¬ projectionOk`) is still DENIED. You
cannot teleport a computation you cannot prove you own, even with the right sky.
-/
theorem genuine_sky_forged_key_denied
    (a : Admission) (_hAgree : a.agree) (hForged : ¬ a.projectionOk) :
    ¬ Admitted a :=
  forged_projection_denied a hForged

end SkymeshTeleport
end Gnosis
