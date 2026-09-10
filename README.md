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

## First Track

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

## Build

This project uses the same Lean/mathlib pin as `lra-lean` initially.

```powershell
lake build Munkres
```

