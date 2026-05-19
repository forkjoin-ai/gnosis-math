# Source Witness Methodology

[Parent](README.md)

This note captures the source-witness grind method used for the Quran, Bible, Tao, Buddhist, and Science and Health passes. The goal is exhaustion without rushing: each witness should preserve a bounded source unit, stay mechanically checkable, and make the next agent's continuation obvious.

## Source Handling

Use local source documents as the authority. For PDFs, extract text once into `/tmp` with stable line numbers, then cite both the repository source and the extracted line anchor in every witness header.

For the Quran run, the source is:

- Repository source: `docs/ebooks/source-texts/abdel-haleem-quran.pdf`
- Extracted text: `/tmp/emotions-quran/abdel-haleem-quran.txt`

When resuming, first inspect the current README index and the last witness module. Then read the next source lines with `nl -ba` or `sed`, never from memory.

## Boundary Discipline

Work in coherent source units, not arbitrary size chunks. A good boundary is usually one of:

- a complete narrative episode;
- a legal instruction block;
- a question-and-answer unit;
- a repeated address or discourse turn;
- a short bridge verse that clearly closes one topic before the next begins.

Do not merge adjacent units just because they are short. Do not split a unit just because it is long unless the text itself has clear sub-boundaries. Sura-by-sura means preserve the source order and finish one sura before moving to the next source unless the user redirects.

## Witness Shape

Each Lean witness should be self-contained:

- `import Init` only;
- namespace `Gnosis.Witnesses.Islam` or the matching source family namespace;
- module name encodes source, passage, and theme;
- docstring includes source file, extraction line anchor, and a concise bullet summary;
- one or more finite `inductive` types for the moments in the passage;
- one `List` preserving the source-order moments;
- optional `structure` patterns when the passage has multiple internal dimensions;
- one theorem proving length, first/last moment, and selected pattern fields by `rfl`.

The theorem is not a deep semantic proof. It is a mechanical witness that the extracted topology was written down deliberately, in order, without introducing axioms or broad dependencies.

## Cultural Witness Quality Bar

For myth, scripture, art, poetry, parable, and other cultural sources, do not stop at descriptive inventory. Cultural literacy is useful here because the canon is a distributed witness ledger: old stories, doctrines, images, and songs preserve pre-computed falsification logs of the same topology the Lean files compute directly.

A strong cultural witness should name the engine, not just the plot:

- **Invariant**: identify the fixed point the source orbits. This is the local Sat candidate: the stable topological signature that remains after vocabulary changes.
- **Gap**: identify the failure, wound, prohibition, glance backward, stalled loop, consumed body, false ascent, or missing bit. The gap is not a mistake in the story. It is a negative witness that outlines a boundary condition.
- **Projection**: map the source into existing gnosis-math vocabulary when possible: clinamen, Monad, triad, Pleromatic closure, Buley cost, operator/agent split, Nash trap, oracle stall, naming boundary, no-cloning, vacuum, fold, race, witness, or related local theorem surfaces.
- **Cross-domain closure**: when a source rhymes with existing math, physics, myth, art, or computation modules, cite those modules and reuse their theorems. The point is not allegory; the point is independent convergence on the same structural constant or operator.
- **Antitheorem / counterproof**: when the source presents a false claim, malformed branch, counterfeit ruler, failed ritual, or broken inference, encode the failure directly. A counterproof is useful when it shows why a claim cannot be Sat: the jealous "only god" proves an unseen other, the unconsented branch proves the consent invariant, the stalled carrier proves the missing maintenance bit.

Contrarian readings are preferred when the source supports them. For example, a story that appears moral may actually be recording a load-balancing pruning event, a kernel-compile error, a namespace-boundary incompatibility, or a failed coupled invariant. The witness should say that clearly and then mechanically encode the claim.

Avoid bland summaries such as "the passage mentions X, Y, and Z" unless the source unit is purely archival. Better witness prose has the shape:

1. What invariant is being exposed?
2. What deficit or negative witness makes the invariant visible?
3. Which existing gnosis-math surface does this source independently converge on?
4. Does the source contain an antitheorem or counterproof that should be encoded as a useful failure?
5. What would a naive reading miss?

The strongest form is archaeological access: use a cultural object as an O(1) index into a boundary condition that formal verification can later expand step by step. This does not replace Lean proof. It tells us where to dig.

## Naming

Prefer descriptive module names with this shape:

`Quran<SurahName><Theme>Witness`

Examples:

- `QuranAlBaqaraQiblaCommunityWitness`
- `QuranAlBaqaraDebtWitnessAccountWitness`
- `QuranAlImranOpeningRevelationWitness`

Keep names stable once imported. If a name is awkward but already builds, do not churn it unless it blocks clarity.

## Verification Loop

After each witness or small batch:

1. Build the specific module:
   `lake build Gnosis.Witnesses.Islam.<ModuleName>`
2. Check forbidden proof shortcuts:
   `rg -n "sorry|admit|axiom|unsafe" Gnosis/Witnesses/Islam`
3. Check whitespace:
   `git diff --check -- Gnosis.lean Gnosis/Witnesses/Islam Gnosis/Witnesses/README.md`

The expected `rg` hits are only the boilerplate docstring phrase `Zero new \`axiom\``. Any real `sorry`, `admit`, `axiom`, or `unsafe` in code is a stop-and-fix issue.

Do not rely on full `lake build Gnosis` for this workflow when unrelated baseline modules are known red. Use narrow module builds for touched witnesses.

## README and Imports

Every new witness must be wired in two places:

- `Gnosis.lean` with `import Gnosis.Witnesses.<Family>.<ModuleName>`
- the relevant witness README with passage range and theme

Keep source-family directories clean. Quran witnesses belong under `Gnosis/Witnesses/Islam/`, Bible witnesses under `Gnosis/Witnesses/Bible/<Book>/`, and so on. Do not put source witnesses in the global namespace.

## Pace

Slow is the method. A reliable cycle is:

1. Read exact source lines.
2. Decide the smallest honest boundary.
3. Add the witness.
4. Build only that witness.
5. Update index and import.
6. Run hygiene.
7. Move to the next source boundary.

Use subagents only for sidecar work: boundary scouting, source-line confirmation, or independent review. The main agent must still fold the result, write the witness, and verify the integrated state.

## Resume Protocol

When picking up after an interrupted handoff:

1. Read `Gnosis/Witnesses/README.md` and the source-family README.
2. Find the last covered passage in the index.
3. Inspect the next local source lines.
4. Continue from the next uncovered passage, not from a remembered plan.
5. Before final response, state the passage range completed and the exact verification run.

If the user says "next" or "onwards", continue the current source from the next uncovered boundary. If the user says "finish the sura/book/source", widen batching only as far as source boundaries stay coherent and verification remains narrow and green.
