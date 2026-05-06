import Init
import Gnosis.GodFormula

namespace Gnosis
namespace CapGnosisScaffold

open Gnosis (godWeight godWeight_ceiling godWeight_conservation godWeight_antitone)

/-!
# CAP–Gnosis scaffold (ledger honesty)

Distributed CAP (**Consistency**, **Availability**, **Partition tolerance**) is **not** modeled here:
no message channels, no network partitions, no failure detectors, no serializability predicate on logs.

What **is** modeled (from **`Gnosis.GodFormula`**) is a **fixed-budget** score

`w(R, v) = R - min(v, R) + 1`

and the **rejection** parameter **`v : Nat`**, read as a **vent / rejection-radius** in the
ledger (not a physical distance, not a network RTT, not a light-cone unless you add axioms).

## What the math actually says (not “`w ∝ 1 / v`”)

For **`v ≤ R`**, **`godWeight_conservation`** gives the **affine** identity

`w + v = R + 1`.

So **weight and rejection are complementary** along a line of constant **`R + 1`**; increasing **`v`**
decreases **`w`** with **slope 1 in v** (see **`godWeight_antitone`**, **`godWeight_explicit_linear`** below),
**not** a multiplicative inverse `w = k / v` (which would be false in this model for small integers).

**Strong** vs **eventual** below are **only** names for **`v = 0`** vs **`v > 0`** in this **Nat** vent;
linking them to real **strong** / **eventual** consistency, or to a **Buley** time bound, is **not** a
theorem in this file — it is an **interpretation** you can layer on after you supply morphisms from
this ledger to a distributed runtime (or to **`SkyrmsBuleyEquilibria`**, **`BuleyWalrasGnosisCertificate`**, etc.).

**“`R` bounded by the speed of light”** is **out of scope** for `Init` — you would need physical
units, a causal structure, and a map from distributed rounds to **Buley**’s discrete clock. This
module does **not** import those.
-/

/-- **Ledger reading only:** zero vent (maps to a “no mismatch’’ / **strong-ledger** story in prose). -/
def StrongLedger (v : Nat) : Prop :=
  v = 0

/-- **Ledger reading only:** positive vent (maps to an “eventual / slack’’ story in prose). -/
def EventualLedger (v : Nat) : Prop :=
  0 < v

/-- Closed form of **`godWeight`** when rejections stay inside the budget. -/
theorem godWeight_explicit_linear {R v : Nat} (hv : v ≤ R) : godWeight R v = R - v + 1 := by
  unfold godWeight
  rw [Nat.min_eq_left hv]

/-- At fixed **`R`**, **zero** vent **maximizes** God-weight among all **`v ≤ R`**. -/
theorem godWeight_maximal_at_strong_ledger (R v : Nat) (hv : v ≤ R) :
    godWeight R v ≤ godWeight R 0 := by
  have h0R : 0 ≤ R := Nat.zero_le R
  exact godWeight_antitone R 0 v h0R hv (Nat.zero_le v)

/-- **Complementarity “tradeoff’’** (the honest replacement for “inverse proportionality”):
weight plus rejection exhausts the **`R + 1`** line when **`v ≤ R`**. -/
theorem consensus_vent_weight_line (R v : Nat) (hv : v ≤ R) : godWeight R v + v = R + 1 :=
  godWeight_conservation R v hv

/-- **Not** multiplicative inverse proportionality: **`w * v`** is **not** invariant in **`v`** at fixed **`R`**
(would be needed for **`w ∝ 1 / v`** with one scalar). Same **`R = 3`**, **`v = 1`** vs **`v = 2`** yields products **3** vs **4**. -/
theorem w_times_v_not_constant_across_v : godWeight 3 1 * 1 ≠ godWeight 3 2 * 2 := by
  simp [godWeight]

end CapGnosisScaffold
end Gnosis
