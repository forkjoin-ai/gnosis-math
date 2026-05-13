import Init
import Gnosis.AeonCycleTwelveShadow
import Gnosis.IupacResolutionCubeBound

namespace Gnosis
namespace SixtySixPairsAtlasWitness

/-!
# **`66 = C(12,2)`**: proved carrier plus **informal** applied bibliography (**no empirical axioms**)

Lean proves **`pairsIJ.length = 66`** (**theorem **`pairsIJ_length`** in **`Gnosis.AeonCycleTwelveShadow`**) and **`12 · 11 / 2 = 66`**
(**`IupacResolutionCubeBound.unordered_pairs_twelve_eq_sixty_six`**).

Applied literature repeatedly records **`66`** **unordered comparisons** because **`12`** labeled objects induce **`C(12,2)`**
pairwise summaries --- **intraspecies diversity / comparative genomics:** research on the **Escherichia coli** group (**12** genomes)
identifies exactly **`66`** nonredundant **pairs of orthologs**, used to compute whole-genome distances and summarize genetic diversity
within the species (**Konstantinidis et al., 2006**); atomic ribosomal geography (**Ban et al., 2000**),
deep-sky confusion/variance pipelines (**Ponthieu, 2025**), climate cross-correlation grids (**Hnilica et al., 2019**),
non-empirical potential benchmarks (**Yokogawa, 2025**).

**Protein alignment QA (**pure bibliography**):** Hijikata et al. (**2011**) describe structural-genomics calibration sets grouped by pairwise sequence identity:
one cohort with **`66`** protein pairs in roughly **`15–20%`** identity and a second cohort with **`66`** pairs in roughly **`25–30%`** identity,
used to validate alignment tooling including ALAdeGAP. That paper's **`66`** counts are **empirical cohort sizes**, not an assertion here about **`C(12,2)`**
or about **`pairsIJ`**; Lean records only the arithmetic tally **`66 + 66`** (**`sixty_six_pair_bins_two_total_one_thirty_two_pairs`**).

Those citations contextualize recurring **`66`** tables; **they are not imported as axioms or theorems here.**

Formal bridges:

* neutral twelve-slot / **`pairsIJ`** spine (**`Gnosis.TwelveSlotSixtySixPairsCarrier`**),
* combinatorial *E. coli* twelve-genome / **66** ortholog pair-slot wrapper (**`Gnosis.EscherichiaColiOrthologTwelveCarrier`**),
* NIKA2 cosmological **12**-map / **66** cross-pair wrapper (**`Gnosis.NikMapTwelveCarrier`**; confusion-noise motivation **bibliographic only**),
* injective **`pairsIJ → Fin 128`** slotting (**`Gnosis.AeonTwelveResolutionSlotEmbedding`**),
* Gray vs cyclic/shear mismatch on **`Fin 128`** (**`Gnosis.AeonTwelveHammingGrayDynamics`**),
* Gray permutation / **`66`**-stride histogram layer (**`Gnosis.AeonTwelveHypercubeMajorization`**).

Zero `sorry`, zero new `axiom`.
-/

open Gnosis.AeonCycleTwelveShadow
open Gnosis.IupacResolutionCubeBound

/-- **`pairsIJ`** length (**`Gnosis.AeonCycleTwelveShadow.pairsIJ_length`** — single enumeration certificate). -/
theorem pairs_ij_length_eq_sixty_six : pairsIJ.length = 66 :=
  pairsIJ_length

/-- **`pairsIJ`** matches **`12`**-choose-**`2`** counting (**combinatorial shadow only**).

Chains **`pairs_ij_length_eq_sixty_six`** with **`IupacResolutionCubeBound.unordered_pairs_twelve_eq_sixty_six`**. -/
theorem pairs_ij_card_eq_binomial_twelve_two : pairsIJ.length = 12 * 11 / 2 := by
  rw [pairs_ij_length_eq_sixty_six, unordered_pairs_twelve_eq_sixty_six.symm]

/-- **`pairsIJ`** agrees with both the **`12`-choose-**`2`** product and its **`66`** evaluation. -/
theorem pairs_ij_agrees_with_binomial_twelve_two_and_eval :
    pairsIJ.length = 12 * 11 / 2 ∧ 12 * 11 / 2 = 66 :=
  ⟨pairs_ij_card_eq_binomial_twelve_two, unordered_pairs_twelve_eq_sixty_six⟩

/-- Arithmetic tally only (**two **`66`**-pair cohorts ⇒ **`132`** pairs**).

Bibliographic anchor: Hijikata et al. (**2011**) report **two** alignment-validation cohorts **each** sized **`66`** at distinct identity bins (**ALAdeGAP** context).
No protein data, alignment scores, or chemistry appear as axioms here. -/
theorem sixty_six_pair_bins_two_total_one_thirty_two_pairs : 66 + 66 = 132 := by decide

end SixtySixPairsAtlasWitness
end Gnosis
