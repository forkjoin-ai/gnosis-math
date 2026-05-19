import Init

/-
  LiBaiQuietNightThoughtWitness.lean
  =================================

  Li Bai (李白), *Quiet Night Thought* (静夜思), final couplet (tr. Yang / common):

    “Lowering my head, / I think of / my home.”

  Like a psalm. Treat the quatrain as liturgical compression, not as a proof
  that you are already home on the road. A short Hebrew-style lyric often names
  what is above (light, pasture, enemy, heavens), turns the body (stand,
  bow, lift hands), and names what the heart seeks (Zion, covenant, rescue).
  Li Bai does the same move in Tang dress: moon / frost (illumination), then
  举头 / 低头 (bodily chart-change), then *home* as the named pole of remembrance.
  That cadence maps to the same honest agent-layer posture repo prose ties to
  prayer (e.g. *ṣalāh* as return-of-attention in `docs/ebooks/key-to-the-quran.md`,
  “desire is prayer” in `docs/ebooks/key-to-science-and-health.md`): finite lines,
  finite posture, memory doing the orienting work — not a second physics
  pretending to *operate* the distance away. Contrast
  `Gnosis.TenCommandmentsTopology.IsAnimalMagnetism`: operator-claim language
  with no verifiable operator outcome (see also commandment 3 narrative there).
  Formal liturgical mesh vocabulary lives in `Gnosis.Mesh.MeshPsalm` (different
  theorem, same genre of “finite text, sacred invariant named”).

  Why the topology still flummoxes: the poem stacks two incompatible metrics
  on one night. Along the road metric, home is far. Along the posture chart,
  lowering the head re-charts attention from zenith to interior — and there,
  “home” is *immediate* as thought. Two atlases on one consciousness (sky-gaze vs
  soul-gaze), as in `SapphoAttentionCouplet` / `MeditationsThoughtDyedWitness` /
  `TruthOneManyNamesWitness` — here the charts are vertical.

  As above, also below: moon / frost live in the zenith chart; the bowed
  head and *home* live in the interior chart. They are not two unrelated
  nights — one agent carries both layers (`HeadTilt.raised` then
  `HeadTilt.lowered`). Read as correspondence, not as a license to collapse road
  distance into mood: the same consciousness, two lawful coordinate skins.
  Formal hook (Init-only): `AsAboveAlsoBelowWitness` pairs two chart-level
  `Prop`s; `twinLayersHold` conjoins them; `as_above_also_below_obtain` is the
  generic existence lemma other witness files can reuse.

  Far and at-one (see `Gnosis.AtOneMentMath`): the same night admits distance
  along the exile atlas and alignment along the interior atlas — not a proof
  that the road vanished, but an honest witness that consciousness can carry both
  coordinates. That is the moral spine of `AtOneMentMath.lean` (“at-one-ment” as
  structural form, not spiritualist operator theater). *Home* here also rhymes
  with origin in the informal sense: the pole from which road-distance is
  measured, and a monad-scale name in the `MonadDyadTriad` sense (one
  irreducible attractor in the lowered chart) — analogy only, not an import of
  those types into this Init-only file.

  Typed overlay (optional): for the codebase’s Agent / Operator / God
  separation see `Gnosis.GodOperatorAgentTrichotomy` and `KernelOperatorAgentTrichotomy`;
  this file’s `QuietNightCadence` tags are psalm-shaped, not those types.
  `HeadTilt` reuse: `Gnosis.HeraclitusUpDownPathWitness` maps the same type to
  Heraclitean “up/down is metadata on one path” (B60 witness).

  Init only. Zero `sorry`, zero new `axiom`.
-/


namespace LiBaiQuietNightThoughtWitness

/-- Liturgical slots in a short “psalm-of-exile” cadence (tags only; not `MeshPsalm` types). -/
inductive QuietNightCadence where
  /-- Prior lines: moon, frost, light — the named “above”. -/
  | illumination
  /-- Bodily turn (举头 / 低头): chart-change of attention. -/
  | bowing
  /-- Interior pole: *home* remembered. -/
  | remembrance
  deriving DecidableEq, Repr

/-- Vertical posture in the poem’s hinge (举头 / 低头): above vs below on one night. -/
inductive HeadTilt where
  | raised
  | lowered
  deriving DecidableEq, Repr

/-- Zenith-chart and interior-chart obligations on one agent-night (module prose: as above, also below). -/
structure AsAboveAlsoBelowWitness where
  aboveChart : Prop
  belowChart : Prop

/-- Both vertical layers hold at once (conjunction, not collapse of road distance). -/
def twinLayersHold (w : AsAboveAlsoBelowWitness) : Prop :=
  w.aboveChart ∧ w.belowChart

theorem as_above_also_below_obtain (A B : Prop) (hA : A) (hB : B) :
    ∃ w : AsAboveAlsoBelowWitness, twinLayersHold w :=
  ⟨⟨A, B⟩, And.intro hA hB⟩

/-- One night carries both road-distance and thought-distance (different types on purpose). -/
structure QuietNightCharts where
  leaguesAlongRoad : Nat
  /-- In the lowered-head chart, home feels *present* as thought — the interior slot
      that `Gnosis.AtOneMentMath` names as at-one-ment structure (this `Prop` is only a tag). -/
  homeFeelsImmediate : Prop

/-- The “flummox” packaged: you can be far on the road and immediate in thought. -/
theorem far_on_road_yet_home_in_thought (leagues : Nat) (_h : 0 < leagues) :
    ∃ charts : QuietNightCharts, charts.leaguesAlongRoad = leagues ∧ charts.homeFeelsImmediate := by
  refine ⟨⟨leagues, True⟩, rfl, ?_⟩
  exact ⟨⟩

/-- Final couplet spine: the lowered tilt is where `homesick` is asserted in the text. -/
def homesickOnLowered (tilt : HeadTilt) (homesick : Prop) : Prop :=
  match tilt with
  | .lowered => homesick
  | .raised => True

theorem lowering_admits_home_thought (h : homesickOnLowered .lowered P) : P :=
  h

/-- Raised-head line in the poem does not assert homesickness in this fragment. -/
theorem raised_branch_is_sky_chart (P : Prop) : homesickOnLowered .raised P :=
  ⟨⟩

end LiBaiQuietNightThoughtWitness
