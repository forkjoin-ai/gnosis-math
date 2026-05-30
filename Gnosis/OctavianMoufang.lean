/-
  OctavianMoufang
  ===============

  Pushes the octavian loop (proven CLOSED with identity + inverses in
  `OctavianLoop`) toward the full Moufang structure.

  Foundation (this file, 240² = 57600 checks each, cheap):
    * left alternative   :  (xx)y = x(xy)
    * right alternative   :  y(xx) = (yx)x
    * flexible            :  (xy)x = x(yx)

  These three alternative laws are the algebraic root of the Moufang
  identities (Artin: any two elements of an alternative algebra generate
  an associative subalgebra → diassociativity → Moufang). They are the
  honest, fast first rung; the degree-3 Moufang identities themselves
  (240³ ≈ 13.8M triples) are attacked in `OctavianMoufangCubic`.

  All `native_decide`, reusing `OctavianLoop.octavians` / `omul`.
  No sorry, no new axioms.
-/

import Gnosis.OctavianLoop

namespace Gnosis.OctavianMoufang

open Gnosis.OctavianLoop

-- ══════════════════════════════════════════════════════════
-- ALTERNATIVITY + FLEXIBILITY  (degree-2, the Moufang root)
-- ══════════════════════════════════════════════════════════

/-- Left alternative law: (x·x)·y = x·(x·y) for all octavians. -/
theorem octavian_left_alternative :
    octavians.all (fun x => octavians.all (fun y =>
      decide (omul (omul x x) y = omul x (omul x y)))) = true := by
  native_decide

/-- Right alternative law: y·(x·x) = (y·x)·x for all octavians. -/
theorem octavian_right_alternative :
    octavians.all (fun x => octavians.all (fun y =>
      decide (omul y (omul x x) = omul (omul y x) x))) = true := by
  native_decide

/-- Flexible law: (x·y)·x = x·(y·x) for all octavians. -/
theorem octavian_flexible :
    octavians.all (fun x => octavians.all (fun y =>
      decide (omul (omul x y) x = omul x (omul y x)))) = true := by
  native_decide

/-- The octavian loop is an alternative loop: left-alternative,
    right-alternative, and flexible all hold. This is the degree-2
    foundation the degree-3 Moufang identities rest on. -/
theorem octavian_is_alternative :
    (octavians.all (fun x => octavians.all (fun y =>
        decide (omul (omul x x) y = omul x (omul x y)))) = true)
    ∧ (octavians.all (fun x => octavians.all (fun y =>
        decide (omul y (omul x x) = omul (omul y x) x))) = true)
    ∧ (octavians.all (fun x => octavians.all (fun y =>
        decide (omul (omul x y) x = omul x (omul y x)))) = true) :=
  ⟨octavian_left_alternative, octavian_right_alternative, octavian_flexible⟩

end Gnosis.OctavianMoufang
