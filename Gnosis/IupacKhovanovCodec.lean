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
about ambient isotopy in `ℝ³`.

Zero `sorry`, zero new `axiom`.
-/

namespace Gnosis
namespace IupacKhovanovCodec

open KhovanovCategorifiesJones
open PeriodicElementLinkAtlas (diagramCodecRow elementDiagram)

/-- Canonical Khovanov `Diagram` carrier for each IUPAC row index (0-based `Z−1`). -/
abbrev iupacRowDiagram (row : Fin 118) : Diagram :=
  diagramCodecRow row

theorem iupacRowDiagram_injective : Function.Injective iupacRowDiagram :=
  PeriodicElementLinkAtlas.diagramCodecRow_injective

/-! ## Jones polynomial separates rows that the 4-palette only sees mod 4 -/

/-- The periodic **element** atlas identifies rows `0` and `4` (both `unknot` stage). -/
example :
    elementDiagram ⟨0, by decide⟩ = elementDiagram ⟨4, by decide⟩ :=
  PeriodicElementLinkAtlas.element_diagram_idx_zero_four

/-- Codec-backed diagrams still carry distinct resolution tags, hence (here) distinct Jones. -/
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
