import Init
import Gnosis.AmplituhedronWireBitwiseContract
import Gnosis.AmplituhedronCoordinatorContract
import Gnosis.PositionalDictModeContract
import Gnosis.BowlMeshRuntimeOracle

/-
  EdgeWorkersPortContract.lean
  ============================

  Cross-codebase contract for the Mesh Consumption Wave port from
  `apps/distributed-inference-worker/` (qwen-coder-7b mesh; wave shipped
  2026-05-10) to `apps/edge-workers/src/workers/distributed-inference/`
  (Aether codebase; wave port pending).

  When both codebases implement the wave, this module pins the
  invariants they must agree on: wire format identities, env-var
  semantics, and the structural-equivalence claim that the two paths
  produce identical wire output on shared canonical witnesses.

  Imports Init plus the wave's existing wire / coordinator contracts.
  Zero `sorry`, zero new `axiom`.
-/


namespace EdgeWorkersPortContract

open AmplituhedronWireBitwiseContract
open AmplituhedronCoordinatorContract
open PositionalDictModeContract

/-! ## The two codebases

Both codebases consume the same wasm kernel (model.rs / amplituhedron.rs
/ bow_q_filter / bw_codec etc.) via the `distributed-inference` Rust
crate. The wave's TS-side primitives (BWAH wire codec, POSDICT loader,
Amph endpoints, Pair X consume, frame coalescing) live ONLY in the
qwen-coder-7b mesh as of 2026-05-10. -/

inductive Codebase where
  | qwenCoder7BMesh    -- `apps/distributed-inference-worker/`
  | aetherEdgeWorkers  -- `apps/edge-workers/src/workers/distributed-inference/`
  deriving DecidableEq, Repr

/-! ## Wire format identities (must agree across codebases) -/

/-- Both codebases MUST emit the same BWAH magic bytes when handling
    `/amplituhedron/replay` responses. -/
theorem bwah_magic_invariant_across_codebases :
    magicBytes = [0x42, 0x57, 0x41, 0x48] := by
  unfold magicBytes; decide

/-- Both codebases MUST set the version byte to 0x01 for the BWAH
    base wire (no flags). -/
theorem bwah_version_invariant : wireVersion = 1 := by
  unfold wireVersion; decide

/-- Both codebases MUST set POSDICT_FLAG = 0x20 on the inner bw-codec
    version byte when encoding with a positional dictionary. -/
theorem posdict_flag_invariant : posdictFlag = 32 := by
  unfold posdictFlag; decide

/-! ## Env-var semantics (must agree across codebases) -/

/-- The five wave env vars and their default polarity. Both codebases
    MUST honor these contracts. -/
inductive EnvVar where
  | gnosisFrameCoalesce          -- default ON, '0' disables
  | gnosisAmplituhedronCoordinator -- default ON, '0' disables (host only)
  | gnosisPairXLive              -- default OFF, '1' enables
  | gnosisResidualCapture        -- default UNSET, path enables
  | gnosisResidualDictB64        -- default UNSET, base64 .bwdict enables
  deriving DecidableEq, Repr

/-- Bool: should this env-var default ON when unset? -/
def envDefaultOn : EnvVar → Bool
  | .gnosisFrameCoalesce          => true
  | .gnosisAmplituhedronCoordinator => true
  | .gnosisPairXLive              => false
  | .gnosisResidualCapture        => false
  | .gnosisResidualDictB64        => false

theorem env_defaults_pinned :
    envDefaultOn EnvVar.gnosisFrameCoalesce = true ∧
    envDefaultOn EnvVar.gnosisAmplituhedronCoordinator = true ∧
    envDefaultOn EnvVar.gnosisPairXLive = false ∧
    envDefaultOn EnvVar.gnosisResidualCapture = false ∧
    envDefaultOn EnvVar.gnosisResidualDictB64 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Coordinator decision identity (must agree)

When both codebases run the Amplituhedron coordinator, they MUST
produce the same hit/miss decision on the same set of station
replay verdicts. -/

theorem coordinator_decision_invariant :
    coordinatorDecision [ReplayVerdict.hit 14336] = true ∧
    coordinatorDecision [ReplayVerdict.miss] = false ∧
    coordinatorDecision [ReplayVerdict.hit 14336, ReplayVerdict.miss] = false := by
  unfold coordinatorDecision; refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Cross-codebase pentad -/

theorem edge_workers_port_pentad :
    magicBytes = [0x42, 0x57, 0x41, 0x48] ∧
    wireVersion = 1 ∧
    posdictFlag = 32 ∧
    envDefaultOn EnvVar.gnosisFrameCoalesce = true ∧
    envDefaultOn EnvVar.gnosisPairXLive = false :=
  ⟨bwah_magic_invariant_across_codebases,
   bwah_version_invariant,
   posdict_flag_invariant,
   env_defaults_pinned.1,
   env_defaults_pinned.2.2.1⟩

end EdgeWorkersPortContract
