# Combinatorial Designs Formalization

Formalization of basic results from combinatorial design theory in Lean 4 using Mathlib.

## Versions

| Tool | Version |
|------|---------|
| Lean 4 | `v4.27.0` |
| Mathlib | `v4.27.0` |

## Building

1. Clone the repository as usual.

2. Download the Mathlib cache (significantly reduces build time):

```bash
lake exe cache get
```

3. Build the project:

```bash
lake build
```

## Library Structure

| File | Description |
|------|-------------|
| `Defs.lean` | Core definitions: `Design`, `BlockDesign`, `TDesign`, `BIBD`, `RPBD` |
| `Basic.lean` | Fundamental parameter relations for BIBDs (e.g. `r(k-1) = λ(v-1)`) |
| `IncidenceMatrix.lean` | Incidence matrices, dual designs, and algebraic characterizations |
| `MatrixLemmas.lean` | Matrix lemmas used in the proof of Fisher's inequality |
| `FisherInequality.lean` | Fisher's inequality: `b ≥ v` for nontrivial RPBDs |
| `SymmetricBIBD.lean` | Symmetric BIBD properties and the Bruck-Ryser-Chowla theorem |
| `HadamardMatrix.lean` | Hadamard matrices and divisibility of order by 4 |
| `MatrixCongruence.lean` | Matrix congruence and connections to quadratic forms |
| `Diagonalizable.lean` | Diagonalizability of bilinear forms |
| `WittCancellation.lean` | Witt cancellation theorem |
| `Construction.lean` | Design constructions: sum, complement, derived, residual, difference sets |
| `Isomorphism.lean` | Design isomorphisms and the automorphism group |
| `KramerMesner.lean` | Kramer-Mesner theorem for constructing t-designs via group actions |
| `Examples.lean` | Concrete examples: the Fano plane as a 2-(7, 3, 1) BIBD |
