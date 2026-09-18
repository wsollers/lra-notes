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
Zorich/RealAnalysis/
```

Active chapters:

- Chapter 2

### Laczkovich: Real Analysis

Lean modules start under:

```text
Laczkovich/RealAnalysis/
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

## Build

This project uses the same Lean/mathlib pin as `lra-lean` initially.

```powershell
lake build
lake build Munkres
lake build LRANotes
```
