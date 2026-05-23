import Init
import Gnosis.Body.FacialActionCoding

/-!
# Facial Expression Pipeline — the live-face math, formalized

Backs the AU-driven face built in `aeon-corpus` / `monster-studio`:

  facial measurement  →  (tracker)  →  FACS AU weight  →  (blend)  →  deformation

A *sovereign* tracker measures the face (e.g. mouth aperture for AU26) and emits
an Action-Unit **weight**; those weights blend the per-AU muscle morphs into a
facial **deformation**. This file proves the guarantees that make the pipeline
*honest*:

* **Neutral faithfulness** (`track_neutral`): a face at its calibrated baseline
  yields zero AU activation — the tracker never hallucinates expression.
* **Neutral identity** (`displace_zero`): zero AU weights deform nothing — the
  rest pose is a fixed point of the blend.
* **Linearity** (`displace_add`): the blend is additive in the weights, so a
  half-smile plus a half-frown is exactly their sum (no surprises when AUs mix).
* **Capstone** (`rest_face_is_neutral`): tracker ∘ blend at rest = the formalized
  neutral.

Reuses `Gnosis.Body.FacialActionCoding` (`ActionUnit` / `Emotion` / `emotionAUs`).
Rustic Church: `Init` only; proofs by `rfl` / `decide` / `simp` / `omega`.
-/

namespace Gnosis.Body.FacialExpressionPipeline

open Gnosis.Body.FacialActionCoding
open ActionUnit Emotion

/-- An AU weight: fixed-point intensity, clamped to `[0,100]`. -/
abbrev Weight := Int

/-- Clamp an intensity into `[0,100]`. -/
def clamp (w : Int) : Int :=
  if w < 0 then 0 else if 100 < w then 100 else w

/-- The sovereign tracker: an AU weight from a scalar facial **measurement**
    against its calibrated **baseline**, scaled by **gain** and clamped. -/
def track (measure baseline gain : Int) : Weight :=
  clamp (gain * (measure - baseline))

/-- **Neutral faithfulness.** At the baseline the tracker emits zero — a face at
    rest produces no Action-Unit activation. -/
theorem track_neutral (baseline gain : Int) :
    track baseline baseline gain = 0 := by
  simp [track, clamp]

/-- A live AU reading: mouth aperture 70 against a rest baseline of 30, gain 2,
    activates AU26 at intensity 80. -/
example : track 70 30 2 = 80 := by decide

/-- The blend: the net displacement of one face coordinate is the dot product of
    the AU **weights** with their per-AU unit **deltas**, over the active AUs. -/
def displace (w : ActionUnit → Weight) (δ : ActionUnit → Int) :
    List ActionUnit → Int
  | [] => 0
  | a :: rest => w a * δ a + displace w δ rest

/-- **Neutral identity.** Zero AU weights deform nothing, for any active set. -/
theorem displace_zero (δ : ActionUnit → Int) (aus : List ActionUnit) :
    displace (fun _ => 0) δ aus = 0 := by
  induction aus with
  | nil => rfl
  | cons _ _ ih => simp [displace, ih]

/-- **Linearity.** The blend is additive in the weights. -/
theorem displace_add (w₁ w₂ : ActionUnit → Weight) (δ : ActionUnit → Int)
    (aus : List ActionUnit) :
    displace (fun a => w₁ a + w₂ a) δ aus
      = displace w₁ δ aus + displace w₂ δ aus := by
  induction aus with
  | nil => rfl
  | cons a rest ih =>
    simp only [displace, ih, Int.add_mul]
    omega

/-- The active Action Units of an emotion (reuses the formalized Ekman atlas);
    these are the AUs the blend drives for that emotion. -/
theorem happiness_smiles : au12 ∈ emotionAUs happiness := by decide
theorem surprise_drops_jaw : au26 ∈ emotionAUs surprise := by decide

/-- **Capstone.** A face at rest — every AU measured at its own baseline — yields
    zero facial deformation: the avatar's neutral *is* the formalized neutral. -/
theorem rest_face_is_neutral
    (baseline gain δ : ActionUnit → Int) (aus : List ActionUnit) :
    displace (fun a => track (baseline a) (baseline a) (gain a)) δ aus = 0 := by
  have h : (fun a => track (baseline a) (baseline a) (gain a)) = (fun _ => 0) := by
    funext a; exact track_neutral (baseline a) (gain a)
  rw [h]; exact displace_zero δ aus

end Gnosis.Body.FacialExpressionPipeline
