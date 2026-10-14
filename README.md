# lra-notes

Personal Lean/mathlib study notes for textbook-driven mathematics.

This repository is a coached learning workspace, separate from the governed
`lra-lean` formalization project. The point is not to rebuild foundations or
transcribe books. The point is to turn selected textbook material into:

- Lean definitions, theorem statements, examples, and exercises;
- personal proof attempts saved through the proof vault;
- independently written professional proofs;
- LaTeX notes distilled from handmade notes and proof cycles;
- RemNote cards for mathematical facts, Lean vocabulary, proof patterns, and
  repeated failure modes.

## Source Policy

Textbook PDFs and scans are local references only. Do not commit raw PDFs,
large extracted text, or long verbatim passages from copyrighted sources.

Mathematical definitions and theorem statements are facts. Proofs are authored
work: personal proof attempts should be preserved as personal artifacts, while
polished proofs should be written independently rather than copied from a text.

## Active Tracks

### Munkres: Topology

The first track is James R. Munkres, *Topology*, Second Edition.

Local source record:

- `SRC-000404`
- PDF: `D:\Readings\Sources\Topology\Topology - Munkres.pdf`
- searchable extract:
  `F:\repos\lra-source-profiles\volumes\volume-iv\_sources\markdown\SRC-000404.md`

Lean modules start under:

```text
Munkres/Topology/Chapter01/
```

Chapter 1 is used as a Lean translation bootcamp: functions, images,
preimages, relations, equivalence relations, partitions, and basic set
manipulation. Later chapters should formalize only the load-bearing material:
definitions, propositions, examples, and selected exercises.

### Ó Searcóid: Metric Spaces

Forward metric-space track:

- `SRC-000401`
- Mícheál Ó Searcóid, *Metric Spaces*, Second Edition, Springer London, 2006.
- PDF: `D:\Readings\Sources\Analysis\Metric Spaces\Metric Spaces - Searc id.pdf`
- searchable extract:
  `F:\repos\lra-source-profiles\volumes\volume-iii\_sources\markdown\SRC-000401.md`

Lean modules start under:

```text
Searcoid/MetricSpaces/
```

This track should lean hard on mathlib's existing metric-space API. The first
pass should prioritize theorem statements, examples, and selected exercises,
with definitions modeled only when they clarify the book/mathlib translation.

### Thomson/Bruckner: Real Analysis

Support track for real analysis:

- `SRC-000115`
- Catalog title: *Elementary Real Analysis Second Edition. [Part One]*
- Catalog author: Brian S. Thomson
- User-facing PDF filename: `Elementary Real Analysis - Bruckner.pdf`
- PDF: `D:\Readings\Sources\Analysis\Real Analysis\Elementary Real Analysis - Bruckner.pdf`
- searchable extract:
  `F:\repos\lra-source-profiles\volumes\volume-iii\_sources\markdown\SRC-000115.md`

Lean modules start under:

```text
Bruckner/RealAnalysis/
```

Active chapters:

- Chapter 1
- Chapter 8

### Bartle: Real Analysis

Lean modules start under:

```text
Bartle/RealAnalysis/
```

Active chapters:

- Chapter 2

### Zorich: Real Analysis

Lean modules start under:

```text
Zorich/RealAnalysisI/
```

Active chapters:

- Chapter 2

### Laczkovich: Real Analysis

Lean modules start under:

```text
Laczkovich/RealAnalysisI/
```

Active chapters:

- Chapter 3

### Enderton: Set Theory

Lean modules start under:

```text
Enderton/SetTheory/
```

Active chapters:

- Chapter 1

### Fefferman: Number Systems

Lean modules start under:

```text
Fefferman/NumberSystems/
```

Active chapters:

- Chapter 3

## Track Layout

Each track mirrors its book's own numbering, so a track uses one of three
layouts:

| Book structure | Layout | Example |
| --- | --- | --- |
| chapters only | `Author/Topic/ChapterNN/` | Spivak, *Calculus* |
| chapters with sections | `Author/Topic/ChapterNN/SectionNN/` | Bruckner, Abbott, Tao |
| sections only | `Author/Topic/SectionNN/` | Halmos, *Naive Set Theory* |

Create section folders as you reach them; do not pre-scaffold empty ones.
In a chapter with sections, every unit is a folder and no unit files sit loose
at chapter level. Material that precedes the chapter's first section
(Laczkovich's axioms, for example) goes in `ChapterNN/Prelude/`.

Each unit (a chapter, or a section where the book has them) holds:

- `Definitions.lean` — the author's definitions, notation, and axioms;
- `Connections.lean` — iff bridges from those definitions to mathlib, when needed;
- `Observations.lean` — facts we derive that the book does not state, when needed;
- `Theorems.lean` — the results the book states, each with its page, and their proofs;
- `Examples.lean` — worked examples and `counterexample`s;
- `Exercises.lean` — selected exercises.

Imports run Definitions → Connections → Observations → Theorems → Examples /
Exercises. A statement belongs in `Theorems.lean` only if it carries a book
page reference; everything we derive ourselves goes in `Observations.lean`.
Prose belongs in the chapter's `notes.tex`, not in Lean.

Namespaces stop at the chapter (`Bruckner.RealAnalysis.Chapter01`) — or at the
book for section-only tracks (`Halmos.SetTheory`) — so moving a result between
sections never renames it.

## Stub Tracks

Scaffolded with an empty first unit (`Definitions`, `Theorems`, `Examples`, `Exercises`). Promote a
stub to Active Tracks once a source record and active chapters are assigned.
Authors with several books keep one root and use a topic folder per book.
The two Mendelsons are different authors and get distinct roots.

Topic folders use a fixed vocabulary, not book titles: `RealAnalysis`,
`ComplexAnalysis`, `ModernAnalysis`, `FunctionalAnalysis`, `MeasureTheory`,
`Probability`, `Topology`, `MetricSpaces`, `Logic`, `SetTheory`,
`NumberSystems`, `LinearAlgebra`, `BooleanAlgebras`, `RelationAlgebras`,
`Calculus`, `CalculusOnManifolds`, `DifferentialGeometry`. A multi-volume
work on one topic takes a volume suffix: `RealAnalysisI`, `RealAnalysisII`.

| Lean root | Source |
| --- | --- |
| `Tao/RealAnalysisI/` | Terence Tao, *Analysis I* |
| `Tao/RealAnalysisII/` | Terence Tao, *Analysis II* |
| `Tao/MeasureTheory/` | Terence Tao, *An Introduction to Measure Theory* |
| `Abbott/RealAnalysis/` | Stephen Abbott, *Understanding Analysis* |
| `Lebl/RealAnalysisI/` | Jiří Lebl, *Basic Analysis I* |
| `Lebl/RealAnalysisII/` | Jiří Lebl, *Basic Analysis II* |
| `Tarski/Logic/` | Alfred Tarski, *Introduction to Logic and to the Methodology of the Deductive Sciences* |
| `Su/RealAnalysis/` | Francis Su, *Real Analysis* (Harvey Mudd lectures) |
| `Su/Topology/` | Michael Starbird and Francis Su, *Topology Through Inquiry* |
| `Dieudonne/ModernAnalysis/` | Jean Dieudonné, *Foundations of Modern Analysis* |
| `Kolmogorov/FunctionalAnalysis/` | A. N. Kolmogorov and S. V. Fomin, *Elements of the Theory of Functions and Functional Analysis* (also translated as *Introductory Real Analysis*) |
| `Kolmogorov/Probability/` | A. N. Kolmogorov, *Foundations of the Theory of Probability* |
| `Enderton/Logic/` | Herbert B. Enderton, *A Mathematical Introduction to Logic* |
| `Laczkovich/RealAnalysisII/` | Miklós Laczkovich and Vera T. Sós, *Real Analysis: Series, Functions of Several Variables, and Applications* |
| `Zorich/RealAnalysisII/` | Vladimir A. Zorich, *Mathematical Analysis II* |
| `Halmos/SetTheory/` | Paul R. Halmos, *Naive Set Theory* |
| `Halmos/MeasureTheory/` | Paul R. Halmos, *Measure Theory* |
| `Halmos/LinearAlgebra/` | Paul R. Halmos, *Finite-Dimensional Vector Spaces* |
| `Halmos/BooleanAlgebras/` | Steven Givant and Paul Halmos, *Introduction to Boolean Algebras* |
| `Givant/RelationAlgebras/` | Steven Givant, *Introduction to Relation Algebras* |
| `Axler/LinearAlgebra/` | Sheldon Axler, *Linear Algebra Done Right* |
| `Axler/MeasureTheory/` | Sheldon Axler, *Measure, Integration & Real Analysis* |
| `Suppes/SetTheory/` | Patrick Suppes, *Axiomatic Set Theory* |
| `Thurston/NumberSystems/` | H. A. Thurston, *The Number-System* |
| `Olmsted/NumberSystems/` | John M. H. Olmsted, *The Real Number System* |
| `MendelsonE/NumberSystems/` | Elliott Mendelson, *Number Systems and the Foundations of Analysis* |
| `MendelsonB/Topology/` | Bert Mendelson, *Introduction to Topology* (point-set) |
| `Spivak/Calculus/` | Michael Spivak, *Calculus* |
| `Spivak/CalculusOnManifolds/` | Michael Spivak, *Calculus on Manifolds* |
| `Spivak/DifferentialGeometry/` | Michael Spivak, *A Comprehensive Introduction to Differential Geometry* |
| `Apostol/RealAnalysis/` | Tom M. Apostol, *Mathematical Analysis* |

## Source Verification

Each track root has a `SOURCE.md` locating its book: the source record, the
local PDF, the Markdown extract, and the Google Drive folder. It is generated
from the `lra-source-profiles` manifest; regenerate with
`python scripts/source_files.py` (set `source_id: none` → a real id once a book
is added to the manifest).

Every definition, axiom, theorem, example, and exercise is checked against the
book: the **statement** must match the book's meaning (proofs are your own), and
the docstring carries the book's label, number, section, and printed page, e.g.
`**Definition 1.1** [Thomson2008, §1.5, p. 11]`. Mathematical mismatches are
recorded in `study/source-audit.md` rather than silently changed.

## TeX Notes

Write study notes in TeX beside the Lean, for example
`Zorich/RealAnalysisI/Chapter02/notes.tex`. Prose is authored by hand; formal
statements are pulled from the compiled Lean, so they cannot drift:

```latex
\usepackage{leanstatement}
\leanstatement{Zorich.RealAnalysisI.Chapter02.IsInverse}        % as mathematics
\leanstatement*{Zorich.RealAnalysisI.Chapter02.IsInverse}       % plus the Lean source
\leanref{Zorich.RealAnalysisI.Chapter02.IsInverse}              % cross-reference
```

`lake exe texexport` renders every theorem and Prop-valued definition into
`generated/lean/` using the `lra-common` environments; symbols come from
`lra-governance/notation.yaml`. Theorems whose proofs contain `sorry` are
marked unproved. A misspelled or renamed declaration is a build error.

Build (needs LuaLaTeX and sibling `lra-common` and `lra-governance` checkouts,
or `LRA_COMMON_ROOT` / `LRA_GOVERNANCE_ROOT`):

```bash
scripts/build-notes.sh Zorich/RealAnalysisI/Chapter02/notes.tex
```

PDFs land in `build/notes/`; `generated/` and `build/` are not committed.

## Build

This project uses the same Lean/mathlib pin as `lra-lean` initially.

```powershell
lake build
lake build Munkres
lake build LRANotes
```

## Documentation Site

`scripts/build-docs.sh` builds browsable API documentation with
[doc-gen4](https://github.com/leanprover/doc-gen4): one page per module, every
declaration's signature, its docstring (including the book reference), and a
link to its source. Output lands in `.lake/build/doc/`.

doc-gen4 is required only under `-Kenv=dev`, so `lake build` never fetches it.
The `Documentation` workflow builds the site on every push to `main` and
publishes it to GitHub Pages (enable Pages with *Source: GitHub Actions*).

## Upgrading Lean

The toolchain, mathlib, and doc-gen4 move together. When upgrading, update all
three in one change:

1. `lean-toolchain` — the new Lean version, e.g. `leanprover/lean4:v4.33.0`.
2. `lakefile.lean` — the `mathlib` tag to the release for that Lean version.
3. `lakefile.lean` — the `doc-gen4` tag to the **same** Lean version. doc-gen4
   is tagged per Lean release (`v4.32.1`, `v4.33.0`, …) and will not build
   against a different toolchain.
4. Refresh the manifest, including the dev-only doc-gen4 entries:
   ```bash
   lake -R -Kenv=dev update
   ```
   Without `-R -Kenv=dev`, Lake drops or ignores doc-gen4 and the docs build
   breaks.
5. Check both builds: `lake build` and `scripts/build-docs.sh`.

`lra-lean` shares this pin; upgrade the two repositories together.
