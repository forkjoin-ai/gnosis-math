import Init
import Gnosis.KhovanovCategorifiesJones
import Gnosis.PeriodicElementLinkAtlas

/-!
# IUPAC row ↔ Khovanov diagram codec (bridge + computable Jones discrimination)

`PeriodicElementLinkAtlas.diagramCodecRow` assigns **118 distinct** `Diagram`
terms to `Fin 118` (0-based atomic number index). This module **names** that map
for IUPAC consumers and records **computable** inequivalence of the Khovanov–Jones
polynomial on row pairs that share the coarse `elementDiagram` (4-periodic) atlas.

These are **kernel-checked** numeric distinctions (`native_decide`), not claims
about ambient isotopy in `ℝ³`.  For resolution-cube bookkeeping (catalog vs codec),
see `Gnosis.KhovanovDiagramWellFormed`. For the dyadic capacity bound
`2^6 < 118 ≤ 2^7`, see `Gnosis.IupacResolutionCubeBound`, and for a cube-shaped
`Diagram` shell with `128` rows, see `Gnosis.SevenCrossingIupacShell`.
Bracket **fold split** at an index (`bracketResolutions_split`); shell **Jones** peel with
explicit middle **Laurent** term: `SevenCrossingIupacShell.jonesPoly_sevenCrossingTaggedDiagram_rowSlotFin128_closedSummand`.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace IupacKhovanovCodec

open KhovanovCategorifiesJones
open PeriodicElementLinkAtlas (diagramCodecRow)

/-- Canonical Khovanov `Diagram` carrier for each IUPAC row index (0-based `Z−1`). -/
abbrev iupacRowDiagram (row : Fin 118) : Diagram :=
  diagramCodecRow row

theorem iupacRowDiagram_injective : Function.Injective iupacRowDiagram :=
  PeriodicElementLinkAtlas.diagramCodecRow_injective

/-! ## Jones polynomial separates rows that the 4-palette only sees mod 4 -/

/-- Codec-backed diagrams carry distinct resolution tags. These inequalities witness
that `jonesPoly ∘ diagramCodecRow` **separates** cohorts that `elementDiagram`
identifies (same residue mod 4). Compare `PeriodicElementLinkAtlas.element_diagram_idx_zero_four`. -/
theorem jones_codec_distinct_rows_0_4 :
    jonesPoly (diagramCodecRow ⟨0, by decide⟩) ≠
      jonesPoly (diagramCodecRow ⟨4, by decide⟩) := by native_decide

theorem jones_codec_distinct_rows_1_5 :
    jonesPoly (diagramCodecRow ⟨1, by decide⟩) ≠
      jonesPoly (diagramCodecRow ⟨5, by decide⟩) := by native_decide

theorem jones_codec_distinct_rows_117_113 :
    jonesPoly (diagramCodecRow ⟨117, by decide⟩) ≠
      jonesPoly (diagramCodecRow ⟨113, by decide⟩) := by native_decide

end IupacKhovanovCodec
end Gnosis
