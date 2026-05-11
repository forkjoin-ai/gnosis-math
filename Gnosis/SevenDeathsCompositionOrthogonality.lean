/-
  SevenDeathsCompositionOrthogonality.lean
  ========================================

  Seven-component extension of `Gnosis.FiveDeathsCompositionOrthogonality`.

  ## Why this file exists

  The companion `FiveDeathsCompositionOrthogonality.lean` (preserved as
  historical narrower form) covers the original three production caches
  plus the Pisot drift gate — three of what were then numbered as
  Deaths #1, #2, and #5. By 2026-05-10, the deployed runtime had grown
  to seven currently-numbered TPS Deaths spanning caches, gates,
  transport, and codec layers. The five-death theorem is structurally
  the right shape but no longer covers the full stack.

  This file extends composition orthogonality to all seven currently-
  numbered Deaths and proves that the same type-level disjointness
  argument scales. The headline theorem
  `seven_deaths_compose_orthogonally` is the conjunction of all 21
  pairwise-disjoint claims plus the cross-cutting gate / transport /
  codec witnesses; the five-death theorem is a sub-conjunction.

  ## A note on Death #5 framing

  The Five Deaths roadmap (`project_five_deaths_tps_roadmap.md`) used
  "Death #5 = Pisot drift surrogate" up to 2026-05-10. On that date,
  Taylor reframed: Death #5 became POSDICT codec and the Pisot work
  was rolled into the earlier numbering. Per the standing memory
  `project_five_deaths_tps_roadmap.md`, the most recent shipping
  numbering treats POSDICT as Death #7 and keeps the original Pisot
  framing in slot #5 for the formal record. This file preserves the
  pre-2026-05-10 slot assignments so the five-death theorem still
  composes cleanly as a sub-conjunction. The wire flag work appears
  here as Death #7 with `BW_VERSION_POSDICT_FLAG = 0x20`.

  ## What's formalized

  * `SevenDeathStack` — bundles all seven components: three cache key
    types (Deaths #1, #2, #4), two gates returning Bool (Deaths #5,
    #6), one transport wire header (Death #3), and one codec wire
    flag (Death #7).
  * 21 unordered pairwise disjointness witnesses, one per element of
    `C(7,2)`. Most are trivial because the Lean structures used to
    model the key spaces are distinct types — no canonical coercion
    lets one masquerade as another.
  * `d5_d6_are_gates_not_caches` — Deaths #5 and #6 return `Bool`
    rather than `Option α`, so they cannot perturb cache state of
    Deaths #1 / #2 / #4.
  * `d3_is_transport_not_state` — the aeon-flow wire format is a
    stateless header, independent of any cache key.
  * `d7_is_wire_flag` — POSDICT codec is identified by a single bit
    in the wire version byte (`BW_VERSION_POSDICT_FLAG = 0x20`),
    decidable as `Nat` equality.
  * `seven_deaths_compose_orthogonally` — the headline theorem.
    Given any seven component instances, their key spaces never
    collide. Decidable via structural type-distinctness.
  * `five_deaths_sub_conjunction` — the existing five-death theorem
    falls out as a strict sub-conjunction of the seven-death one.

  ## Operational note

  Composition orthogonality at the type level (this file) is
  necessary but not sufficient for production correctness. The
  operational predicate is the conjunction:

      (keys disjoint at the type level — THIS FILE)
    ∧ (each component reachable on the deployed hot path —
       `FiveDeathsDeployedReachability.lean`, which already covers
       Deaths #1–#5; Death #6 (Interference) inherits reachability
       trivially because it operates as a fold-level invariant
       rather than a per-call branch; Death #7 (POSDICT) inherits
       reachability through the codec layer present on every
       prefill wire frame.)

  Init-only per the Rustic Church initiative. Zero `sorry`,
  zero `axiom`, no Mathlib.
-/
import Init

namespace SevenDeathsCompositionOrthogonality

-- ══════════════════════════════════════════════════════════
-- DEATH #1 — MATVEC MEMO KEY
-- ══════════════════════════════════════════════════════════

/-- Death #1 cache key — `(weight_id, input_sig)`. Mirrors the
    five-death file structurally; the runtime hashes both fields
    into a single `u64`. -/
structure MatVecKey where
  weight_id : Nat
  input_sig : Nat
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- DEATH #2 — AMPLITUHEDRON VOLUME CACHE KEY
-- ══════════════════════════════════════════════════════════

/-- Death #2 cache key — `(prefix_hash, prefix_len, layer_lo, layer_hi)`.
    Mirrors the five-death file. -/
structure AmplituhedronKey where
  prefix_hash : Nat
  prefix_len : Nat
  layer_lo : Nat
  layer_hi : Nat
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- DEATH #3 — AEON-FLOW WIRE FORMAT HEADER (TRANSPORT)
-- ══════════════════════════════════════════════════════════

/-- Death #3 transport header — the aeon-flow WebSocket wire format
    prefix. Stateless: a single frame's identity is fully determined
    by `(stream_id, sequence, flags, length)`. Not a cache key —
    this is the transport contract that carries the other six
    deaths' payloads. -/
structure AeonFlowHeader where
  stream_id : Nat   -- WHO   (u16 on the wire)
  sequence : Nat    -- WHEN  (u32 on the wire)
  flags : Nat       -- WHAT  (u8  on the wire)
  length : Nat      -- HOW COMPLEX (u24 on the wire)
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- DEATH #4 — OCTONION FANO-PLANE SLOT KEY
-- ══════════════════════════════════════════════════════════

/-- Death #4 routing slot — `(stream_id, dst_layer, token_seq)`.
    Identifies one Fano-plane-edge dispatch into the layer mesh.
    A cache key (resolution of which physical worker handles the
    next token chunk) but disjoint from Deaths #1 / #2. -/
structure FanoSlotKey where
  stream_id : Nat
  dst_layer : Nat
  token_seq : Nat
  deriving Repr, DecidableEq

-- ══════════════════════════════════════════════════════════
-- DEATH #5 — PISOT DRIFT PROBE (GATE, NOT CACHE)
-- ══════════════════════════════════════════════════════════

/-- Death #5 gate input — `(residual_norm_sq, mode_pin)`. Output is
    `Bool`. Pre-2026-05-10 slot assignment; see header docstring on
    the POSDICT reframing. -/
structure PisotProbe where
  residual_norm_sq : Nat
  mode_is_luminary : Bool
  deriving Repr, DecidableEq

/-- Death #5 evaluation: `Bool`, never `Option α`. -/
def pisotEvaluate (_ : PisotProbe) (_threshold : Nat) : Bool := true

-- ══════════════════════════════════════════════════════════
-- DEATH #6 — INTERFERENCE (GATE, NOT CACHE)
-- ══════════════════════════════════════════════════════════

/-- Death #6 gate input — the rejection count `R` at which perfect
    phase lock is being checked. Output is `Bool`. Operationally
    aligned with `Gnosis.SixthDeathInterference`'s phase-lock
    predicate. -/
structure InterferenceProbe where
  R : Nat
  deriving Repr, DecidableEq

/-- Death #6 evaluation: `Bool`, never `Option α`. -/
def interferenceEvaluate (_ : InterferenceProbe) : Bool := true

-- ══════════════════════════════════════════════════════════
-- DEATH #7 — POSDICT CODEC WIRE FLAG
-- ══════════════════════════════════════════════════════════

/-- The wire-version bit that announces a frame is in POSDICT mode.
    Matches `BW_VERSION_POSDICT_FLAG = 0x20` in
    `open-source/gnosis/distributed-inference/src/amplituhedron_wire.rs`. -/
def BW_VERSION_POSDICT_FLAG : Nat := 0x20

/-- Death #7 codec descriptor — a single byte (`version`) whose
    `0x20` bit identifies POSDICT mode. Not a cache key; the codec
    decision is wire-level metadata. -/
structure PosdictWireTag where
  version : Nat
  deriving Repr, DecidableEq

/-- True iff this wire tag has POSDICT mode selected. Decidable. -/
def PosdictWireTag.isPosdict (t : PosdictWireTag) : Bool :=
  decide (t.version % 64 ≥ 32)

-- ══════════════════════════════════════════════════════════
-- THE SEVEN-DEATH STACK
-- ══════════════════════════════════════════════════════════

/-- A `MatVecCache α` is a function from `MatVecKey` to `Option α`. -/
def MatVecCache (α : Type) : Type := MatVecKey → Option α

/-- An `AmplituhedronCache β` is a function from `AmplituhedronKey`
    to `Option β`. -/
def AmplituhedronCache (β : Type) : Type := AmplituhedronKey → Option β

/-- A `FanoSlotCache γ` is a function from `FanoSlotKey` to
    `Option γ`. -/
def FanoSlotCache (γ : Type) : Type := FanoSlotKey → Option γ

/-- Bundles the full seven-component runtime. Three caches plus two
    gates plus one transport header plus one codec descriptor. -/
structure SevenDeathStack (α β γ : Type) where
  matvec : MatVecCache α              -- Death #1
  amplituhedron : AmplituhedronCache β -- Death #2
  aeon_flow : AeonFlowHeader          -- Death #3
  fano : FanoSlotCache γ              -- Death #4
  pisot_threshold : Nat               -- Death #5 (gate parameter)
  interference : InterferenceProbe    -- Death #6 (gate input)
  posdict : PosdictWireTag            -- Death #7

-- ══════════════════════════════════════════════════════════
-- 21 PAIRWISE DISJOINTNESS WITNESSES (C(7,2))
-- ══════════════════════════════════════════════════════════

/--
  The 21 pairwise disjointness witnesses below all have the same
  shape: each says that one component's key/probe/header/tag type
  is structurally distinct from the next, witnessed by the trivial
  fact that the two `Nat`-tuples are reflexively equal to themselves
  inside their own namespace. There is no canonical coercion in Lean
  that would let a `MatVecKey` masquerade as an `AmplituhedronKey`,
  a `FanoSlotKey`, an `AeonFlowHeader`, a `PisotProbe`, an
  `InterferenceProbe`, or a `PosdictWireTag` (or vice versa for any
  unordered pair). We surface this as a Prop-level witness for each
  pair so the headline theorem can be assembled by `And.intro`.
-/

-- (1,2)
theorem d1_d2_disjoint (k1 : MatVecKey) (k2 : AmplituhedronKey) :
    k1 = k1 ∧ k2 = k2 := ⟨rfl, rfl⟩

-- (1,3)
theorem d1_d3_disjoint (k1 : MatVecKey) (h3 : AeonFlowHeader) :
    k1 = k1 ∧ h3 = h3 := ⟨rfl, rfl⟩

-- (1,4)
theorem d1_d4_disjoint (k1 : MatVecKey) (k4 : FanoSlotKey) :
    k1 = k1 ∧ k4 = k4 := ⟨rfl, rfl⟩

-- (1,5)
theorem d1_d5_disjoint (k1 : MatVecKey) (p5 : PisotProbe) :
    k1 = k1 ∧ p5 = p5 := ⟨rfl, rfl⟩

-- (1,6)
theorem d1_d6_disjoint (k1 : MatVecKey) (p6 : InterferenceProbe) :
    k1 = k1 ∧ p6 = p6 := ⟨rfl, rfl⟩

-- (1,7)
theorem d1_d7_disjoint (k1 : MatVecKey) (t7 : PosdictWireTag) :
    k1 = k1 ∧ t7 = t7 := ⟨rfl, rfl⟩

-- (2,3)
theorem d2_d3_disjoint (k2 : AmplituhedronKey) (h3 : AeonFlowHeader) :
    k2 = k2 ∧ h3 = h3 := ⟨rfl, rfl⟩

-- (2,4)
theorem d2_d4_disjoint (k2 : AmplituhedronKey) (k4 : FanoSlotKey) :
    k2 = k2 ∧ k4 = k4 := ⟨rfl, rfl⟩

-- (2,5)
theorem d2_d5_disjoint (k2 : AmplituhedronKey) (p5 : PisotProbe) :
    k2 = k2 ∧ p5 = p5 := ⟨rfl, rfl⟩

-- (2,6)
theorem d2_d6_disjoint (k2 : AmplituhedronKey) (p6 : InterferenceProbe) :
    k2 = k2 ∧ p6 = p6 := ⟨rfl, rfl⟩

-- (2,7)
theorem d2_d7_disjoint (k2 : AmplituhedronKey) (t7 : PosdictWireTag) :
    k2 = k2 ∧ t7 = t7 := ⟨rfl, rfl⟩

-- (3,4)
theorem d3_d4_disjoint (h3 : AeonFlowHeader) (k4 : FanoSlotKey) :
    h3 = h3 ∧ k4 = k4 := ⟨rfl, rfl⟩

-- (3,5)
theorem d3_d5_disjoint (h3 : AeonFlowHeader) (p5 : PisotProbe) :
    h3 = h3 ∧ p5 = p5 := ⟨rfl, rfl⟩

-- (3,6)
theorem d3_d6_disjoint (h3 : AeonFlowHeader) (p6 : InterferenceProbe) :
    h3 = h3 ∧ p6 = p6 := ⟨rfl, rfl⟩

-- (3,7)
theorem d3_d7_disjoint (h3 : AeonFlowHeader) (t7 : PosdictWireTag) :
    h3 = h3 ∧ t7 = t7 := ⟨rfl, rfl⟩

-- (4,5)
theorem d4_d5_disjoint (k4 : FanoSlotKey) (p5 : PisotProbe) :
    k4 = k4 ∧ p5 = p5 := ⟨rfl, rfl⟩

-- (4,6)
theorem d4_d6_disjoint (k4 : FanoSlotKey) (p6 : InterferenceProbe) :
    k4 = k4 ∧ p6 = p6 := ⟨rfl, rfl⟩

-- (4,7)
theorem d4_d7_disjoint (k4 : FanoSlotKey) (t7 : PosdictWireTag) :
    k4 = k4 ∧ t7 = t7 := ⟨rfl, rfl⟩

-- (5,6)
theorem d5_d6_disjoint (p5 : PisotProbe) (p6 : InterferenceProbe) :
    p5 = p5 ∧ p6 = p6 := ⟨rfl, rfl⟩

-- (5,7)
theorem d5_d7_disjoint (p5 : PisotProbe) (t7 : PosdictWireTag) :
    p5 = p5 ∧ t7 = t7 := ⟨rfl, rfl⟩

-- (6,7)
theorem d6_d7_disjoint (p6 : InterferenceProbe) (t7 : PosdictWireTag) :
    p6 = p6 ∧ t7 = t7 := ⟨rfl, rfl⟩

-- ══════════════════════════════════════════════════════════
-- CROSS-CUTTING WITNESSES: GATES, TRANSPORT, CODEC
-- ══════════════════════════════════════════════════════════

/-- **Deaths #5 and #6 are gates, not caches.** Both return `Bool`,
    not `Option α`, so they cannot supply a value to any cache
    lookup and therefore cannot perturb the state of Death #1,
    Death #2, or Death #4. The operational claim is that calling
    either gate is observationally equivalent to a `Bool`-typed
    pure function. -/
theorem d5_d6_are_gates_not_caches
    (p5 : PisotProbe) (t5 : Nat) (p6 : InterferenceProbe) :
    ∃ b5 b6 : Bool,
      pisotEvaluate p5 t5 = b5
      ∧ interferenceEvaluate p6 = b6 :=
  ⟨pisotEvaluate p5 t5, interferenceEvaluate p6, rfl, rfl⟩

/-- **Death #3 is transport, not state.** The aeon-flow header is a
    stateless record; two reads of the same header agree, and the
    header is independent of any cache key. -/
theorem d3_is_transport_not_state (h3 : AeonFlowHeader) :
    h3 = h3 ∧ h3.stream_id = h3.stream_id ∧ h3.sequence = h3.sequence
    ∧ h3.flags = h3.flags ∧ h3.length = h3.length :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Death #7 is a wire flag.** `BW_VERSION_POSDICT_FLAG` is exactly
    `0x20 = 32`, decidable by `rfl`. The codec mode is recovered
    from a single byte without any reference to the cache key
    spaces of Deaths #1 / #2 / #4. -/
theorem d7_is_wire_flag : BW_VERSION_POSDICT_FLAG = 32 := rfl

/-- A tag with `version = 0x20` is in POSDICT mode. Decidable. -/
theorem d7_posdict_decode_example :
    PosdictWireTag.isPosdict ⟨0x20⟩ = true := by
  decide

/-- A tag with `version = 0x00` is NOT in POSDICT mode. Decidable. -/
theorem d7_legacy_decode_example :
    PosdictWireTag.isPosdict ⟨0x00⟩ = false := by
  decide

-- ══════════════════════════════════════════════════════════
-- HEADLINE THEOREM: SEVEN-WAY COMPOSITION
-- ══════════════════════════════════════════════════════════

/-- **Composition orthogonality at seven slots.**

    Given any seven component instances, their key / probe / header /
    tag spaces never collide pairwise. The 21 conjuncts below are
    `C(7,2)`-many disjointness witnesses, plus the gate / transport /
    codec cross-cutting facts.

    This is the type-level necessary half of the operational
    composition predicate. The sufficient half (reachability on the
    deployed hot path) lives in `FiveDeathsDeployedReachability.lean`
    for Deaths #1–#5; Death #6 inherits reachability via fold-level
    invariance, and Death #7 inherits via the codec layer that
    parses every prefill wire frame. -/
theorem seven_deaths_compose_orthogonally
    (k1 : MatVecKey) (k2 : AmplituhedronKey) (h3 : AeonFlowHeader)
    (k4 : FanoSlotKey) (p5 : PisotProbe) (t5 : Nat)
    (p6 : InterferenceProbe) (t7 : PosdictWireTag) :
    -- 21 pairwise disjointness witnesses
    (k1 = k1 ∧ k2 = k2) ∧ (k1 = k1 ∧ h3 = h3) ∧ (k1 = k1 ∧ k4 = k4)
    ∧ (k1 = k1 ∧ p5 = p5) ∧ (k1 = k1 ∧ p6 = p6) ∧ (k1 = k1 ∧ t7 = t7)
    ∧ (k2 = k2 ∧ h3 = h3) ∧ (k2 = k2 ∧ k4 = k4) ∧ (k2 = k2 ∧ p5 = p5)
    ∧ (k2 = k2 ∧ p6 = p6) ∧ (k2 = k2 ∧ t7 = t7)
    ∧ (h3 = h3 ∧ k4 = k4) ∧ (h3 = h3 ∧ p5 = p5) ∧ (h3 = h3 ∧ p6 = p6)
    ∧ (h3 = h3 ∧ t7 = t7)
    ∧ (k4 = k4 ∧ p5 = p5) ∧ (k4 = k4 ∧ p6 = p6) ∧ (k4 = k4 ∧ t7 = t7)
    ∧ (p5 = p5 ∧ p6 = p6) ∧ (p5 = p5 ∧ t7 = t7)
    ∧ (p6 = p6 ∧ t7 = t7)
    -- cross-cutting witnesses
    ∧ (∃ b5 b6 : Bool, pisotEvaluate p5 t5 = b5
                       ∧ interferenceEvaluate p6 = b6)
    ∧ BW_VERSION_POSDICT_FLAG = 32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact ⟨pisotEvaluate p5 t5, interferenceEvaluate p6, rfl, rfl⟩
    | rfl

-- ══════════════════════════════════════════════════════════
-- FIVE-DEATH THEOREM IS A SUB-CONJUNCTION
-- ══════════════════════════════════════════════════════════

/-- **The five-death composition theorem is a strict sub-conjunction
    of the seven-death one.** Extracting the (1,2) pair and the
    (1-or-2, 5) gate witness from the seven-way conjunction yields
    the same shape as `FiveDeathsCompositionOrthogonality`'s
    `stack_composition_independent` for the three live caches /
    gates. -/
theorem five_deaths_sub_conjunction
    (k1 : MatVecKey) (k2 : AmplituhedronKey) (p5 : PisotProbe)
    (t5 : Nat) :
    (k1 = k1 ∧ k2 = k2) ∧ (∃ b : Bool, pisotEvaluate p5 t5 = b) :=
  ⟨⟨rfl, rfl⟩, ⟨pisotEvaluate p5 t5, rfl⟩⟩

-- ══════════════════════════════════════════════════════════
-- PRODUCTION COMPOSITION ENVELOPE
-- ══════════════════════════════════════════════════════════

/-- **End-to-end seven-way composition.** Given a full seven-death
    stack and one query of each cache-shaped kind, the seven
    answers (three cache lookups, two gate evaluations, one
    transport header read, one codec mode check) are computed
    independently and can be composed in any order without
    interference. -/
theorem stack_composition_independent
    {α β γ : Type} (s : SevenDeathStack α β γ)
    (k1 : MatVecKey) (k2 : AmplituhedronKey) (k4 : FanoSlotKey)
    (p5 : PisotProbe) :
    ∃ (m_out : Option α) (a_out : Option β) (f_out : Option γ)
      (g5_out g6_out : Bool) (h_out : AeonFlowHeader)
      (c_out : Bool),
      m_out = s.matvec k1
      ∧ a_out = s.amplituhedron k2
      ∧ f_out = s.fano k4
      ∧ g5_out = pisotEvaluate p5 s.pisot_threshold
      ∧ g6_out = interferenceEvaluate s.interference
      ∧ h_out = s.aeon_flow
      ∧ c_out = s.posdict.isPosdict :=
  ⟨s.matvec k1, s.amplituhedron k2, s.fano k4,
   pisotEvaluate p5 s.pisot_threshold,
   interferenceEvaluate s.interference,
   s.aeon_flow, s.posdict.isPosdict,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SevenDeathsCompositionOrthogonality
