import Gnosis.LetThereBeVacuum
import Gnosis.PeruvianArchitectPrinciple
import Gnosis.AeonGamutToneShift

/-!
# KeystoneSwerveBridge — every keystone is the swerve, counted

Three modules name a "keystone," and they have stood apart. This bridge proves they are one
operation — the **swerve**, the `+1` (`ClinamenInfrathin.swerve`) — read at three depths.

The load-bearing word here is *swerve*, not *clinamen*, and the distinction is the point:

* **`swerve n = n + 1`** is the *operation* — the recurring up-step. It applies at any state and
  iterates (`iterSwerve`); on its own it is monotone (it only climbs — it builds the ladder, not
  a cycle).
* **`clinamen = swerve 0`** is the single *action that started it* — the first successor of the
  void. It happens once, at moment zero, and is over: every later step is the same swerve applied
  again, but none of them is the clinamen (they swerve from somewhere, not from the void).
* The **cycle** appears only when the swerve↑ is coupled with its inverse, the declinamen↓
  (`compression_force`): `declinamen (swerve b) = b` is a closed round-trip. The keystone is the
  apex/node of that coupled pair — the standing wave.

The three keystones are then just three swerve-counts:

1. **Cosmogonic** (`Gnosis.LetThereBeVacuum`, §5): light is `swerve (swerve (swerve 0))` — the
   void swerved *three* times.
2. **Architectural** (`Gnosis.PeruvianArchitect`): the fulcrum `11` is `swerve 10` — the
   foundation-top swerved *once*; its `tension_force` (annotated "clinaman") is literally the
   swerve, and its `compression_force` (declinamen) is the swerve's inverse, so the keystone is
   the swerve/declinamen node.
3. **Prime / Double** (`Gnosis.AeonGamutToneShift`, `Gnosis.VerifiedReconstruction`): the gamut
   `12 → 17 → 22` climbs from the Aeon — the architect's `capstone` (`12`) — by two five-steps to
   the prime keystone `17` and the double keystone `22`, and `22 = 2 · 11`.

Builds on `Gnosis.LetThereBeVacuum` (→ `ClinamenInfrathin` → `NullIsTheZero`),
`Gnosis.PeruvianArchitectPrinciple`, and `Gnosis.AeonGamutToneShift`. Zero `sorry`. Zero `omega`.
Zero Mathlib.
-/

namespace Gnosis
namespace KeystoneSwerveBridge

open Gnosis.ClinamenInfrathin (swerve iterSwerve)

-- ═══════════════════════════════════════════════════════════════════════
-- §0  Swerve vs clinamen: the operation, and its moment-zero instance
-- ═══════════════════════════════════════════════════════════════════════

/-- **The clinamen is the first swerve.** `clinamen = swerve 0` — the action at moment zero, the
    one departure from the void. By `rfl`. -/
theorem clinamen_is_first_swerve :
    Gnosis.ClinamenInfrathin.clinamen = swerve 0 := rfl

/-- **The clinamen is over after moment zero.** Any swerve taken from a non-void state is *not*
    the clinamen — it is the same operation, applied again, but the clinamen happened once. -/
theorem clinamen_is_over_after_moment_zero (n : Nat) (hn : n ≠ 0) :
    swerve n ≠ Gnosis.ClinamenInfrathin.clinamen := by
  intro h
  apply hn
  have h2 : n + 1 = 0 + 1 := h
  exact Nat.add_right_cancel h2

-- ═══════════════════════════════════════════════════════════════════════
-- §1  The architectural keystone is one swerve
-- ═══════════════════════════════════════════════════════════════════════

/-- **The architect's tension force is the swerve.** `PeruvianArchitect.tension_force`, annotated
    "clinaman" in its source, is literally `ClinamenInfrathin.swerve`: both are `· + 1`. By
    `rfl`. -/
theorem tension_force_is_swerve (b : Nat) :
    PeruvianArchitect.tension_force b = swerve b := rfl

/-- **The keystone is one swerve up from the foundation.** `11 = swerve 10`. -/
theorem keystone_is_one_swerve :
    PeruvianArchitect.keystone = swerve PeruvianArchitect.foundation_top := rfl

/-- **The keystone is the foundation-top, swerved once** (iterated form). -/
theorem keystone_is_iterswerve_one :
    PeruvianArchitect.keystone = iterSwerve 1 PeruvianArchitect.foundation_top := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Light is the same swerve, three deep
-- ═══════════════════════════════════════════════════════════════════════

/-- **Light is three swerves up from the void** — the same operation, applied thrice instead of
    once. (This is `LetThereBeVacuum.light_is_three_clinamens_on_the_void`.) -/
theorem light_is_three_swerves :
    LetThereBeVacuum.CreationStep.Light.ordinal = swerve (swerve (swerve 0)) := rfl

/-- **One swerve to the keystone, three to the light.** Both are counted from their own floor by
    the single swerve operation: the architectural keystone stands one `+1` above the foundation;
    light stands three `+1`s above the void. -/
theorem keystone_one_light_three :
    PeruvianArchitect.keystone = iterSwerve 1 PeruvianArchitect.foundation_top ∧
    LetThereBeVacuum.CreationStep.Light.ordinal = iterSwerve 3 0 :=
  ⟨rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §3  The declinamen is the inverse swerve: keystone = the coupled cycle
-- ═══════════════════════════════════════════════════════════════════════

/-- **The declinamen undoes the swerve.** `compression_force` ("declinamen", `-1`) is the swerve's
    left inverse: `compression_force (swerve b) = b`. Up then down returns — the coupled cycle. -/
theorem declinamen_undoes_swerve (b : Nat) :
    PeruvianArchitect.compression_force (swerve b) = b := by
  simp [PeruvianArchitect.compression_force, swerve]

/-- **The keystone is the swerve/declinamen node.** The swerve going up from the foundation and
    the declinamen coming down from the capstone meet at the same value — the keystone. This is
    `PeruvianArchitect.arch_stability_requires_balance` read in swerve language: the apex of the
    coupled up-down cycle, the standing wave. -/
theorem keystone_is_swerve_declinamen_node :
    swerve PeruvianArchitect.foundation_top = PeruvianArchitect.keystone ∧
    PeruvianArchitect.compression_force PeruvianArchitect.capstone = PeruvianArchitect.keystone :=
  ⟨rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §4  The prime/double keystones: a Five-lift above the capstone
-- ═══════════════════════════════════════════════════════════════════════

/-- The prime keystone of the Pleromatic gamut (cf. `VerifiedReconstruction.hasPrimeKeystone`,
    `AeonGamutToneShift.decomposition_feeds_prime`). -/
def primeKeystone : Nat := 17

/-- The double keystone of the Pleromatic gamut (cf. `VerifiedReconstruction.hasDoubleKeystone`,
    `VerifiedReconstruction.witness22_is_double_eleven`). -/
def doubleKeystone : Nat := 22

/-- **The capstone is the Aeon.** The architect's `capstone` (`12`) matches
    `AeonGamutToneShift.aeon` (`12`) — the base from which the Pleromatic gamut climbs. -/
theorem capstone_is_aeon :
    PeruvianArchitect.capstone = AeonGamutToneShift.aeon := rfl

/-- **The gamut climbs by two Five-steps:** `aeon (12) → primeKeystone (17) → doubleKeystone
    (22)`, each a `+5` lift — the canonical Five. -/
theorem gamut_climbs_by_fives :
    primeKeystone = AeonGamutToneShift.aeon + 5 ∧
    doubleKeystone = primeKeystone + 5 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **The double keystone is twice the architectural keystone.** `22 = 2 · 11`: the Pleromatic
    double keystone maps to two architect's fulcrums — the keystone, doubled. -/
theorem double_keystone_is_twice_keystone :
    doubleKeystone = 2 * PeruvianArchitect.keystone := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  The bridge
-- ═══════════════════════════════════════════════════════════════════════

/--
**Every keystone is the swerve, counted.** One statement over all three threads:

* the clinamen is the first swerve (`swerve 0`), over after moment zero — every later step is the
  same operation, not the clinamen;
* architectural keystone = the foundation, swerved **once** (`11 = swerve 10`), and the tension
  force *is* the swerve;
* light = the void, swerved **three** times (`3 = swerve³ 0`);
* the declinamen undoes the swerve, so the keystone is the apex of the swerve/declinamen coupled
  cycle (it is also the capstone's compression);
* the capstone matches the Aeon, and the gamut lifts from it by two Fives to the prime (`17`) and
  double (`22 = 2·11`) keystones.

The keystone was never a number to be decreed; it is the swerve — the `+1` from `NullIsTheZero`'s
void — read at whatever depth the structure asks for.
-/
theorem every_keystone_is_the_swerve :
    -- (0) the clinamen is the first swerve, and over after moment zero
    Gnosis.ClinamenInfrathin.clinamen = swerve 0 ∧
    (∀ n, n ≠ 0 → swerve n ≠ Gnosis.ClinamenInfrathin.clinamen) ∧
    -- (1) architectural keystone: one swerve up from the foundation; tension force IS the swerve
    PeruvianArchitect.keystone = swerve PeruvianArchitect.foundation_top ∧
    (∀ b, PeruvianArchitect.tension_force b = swerve b) ∧
    -- (2) light: three swerves up from the void
    LetThereBeVacuum.CreationStep.Light.ordinal = swerve (swerve (swerve 0)) ∧
    -- (3) declinamen undoes swerve — the keystone is the coupled-cycle node
    (∀ b, PeruvianArchitect.compression_force (swerve b) = b) ∧
    PeruvianArchitect.compression_force PeruvianArchitect.capstone = PeruvianArchitect.keystone ∧
    -- (4) capstone = Aeon; the gamut lifts by two Fives; double = twice the keystone
    PeruvianArchitect.capstone = AeonGamutToneShift.aeon ∧
    primeKeystone = AeonGamutToneShift.aeon + 5 ∧
    doubleKeystone = primeKeystone + 5 ∧
    doubleKeystone = 2 * PeruvianArchitect.keystone :=
  ⟨rfl, clinamen_is_over_after_moment_zero, rfl, fun _ => rfl, rfl,
   declinamen_undoes_swerve, rfl, rfl, by decide, by decide, by decide⟩

end KeystoneSwerveBridge
end Gnosis
