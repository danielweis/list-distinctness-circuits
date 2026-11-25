# The list-distinctness theorem behind ω = 9/4 implies superlinear Boolean circuit lower bounds

Daniel Weis · November 25, 2026 · [PDF](paper.pdf)

OpenAI's preprint *The matrix multiplication exponent is nine fourths* (November 24, 2026) claims ω = 9/4, deriving its lower bound ω ≥ 9/4 by contradiction with a lower bound on tensor networks that test list distinctness (its Theorem 2.2). This note observes that Boolean circuits translate into such networks with constant-factor overhead. Theorem 2.2 therefore implies that fan-in-two Boolean circuits deciding element distinctness on N input bits need Ω(N (log N)^σ) gates for some (non-explicit) constant σ > 0. As far as we know, no superlinear lower bound against general Boolean circuits was previously known for any function in NP; element distinctness is even in uniform AC⁰. The note also derives bounds for sorting, distinct-element counting, graph acyclicity, the AND of many independent instances, and circuits that count witnesses modulo p, including unambiguous ones.

**Status.** Theorem 2.2 has not been refereed, but its formal version (`ManyList`) is proved in the Lean development accompanying the OpenAI preprint, as part of the formal proof of ω = 9/4. We built that development at commit `3344da5` with Lean 4.34.1 and confirmed that `square_exponent`, `manyList` and `manyList_full` depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

On top of it, `CircuitLowerBound.lean` formalizes the main theorem of this note (with weaker constants), stated with the circuit and element-distinctness definitions of two independent, unpatched libraries that the OpenAI development already pins: [CSLib](https://github.com/leanprover/cslib) (`Cslib.Circuits.Circuit`, `Computes`, natural-number `complexity` over complete bases, the full binary and De Morgan bases) and [Complexitylib](https://github.com/cslib-community/complexitylib) (`elementDistinctness`). For example, `full_basis_complexity` and `deMorgan_complexity` prove that for every constant c and all large w, the natural-number circuit complexity of `elementDistinctness (2^w) (2w)` exceeds c·N, where N = 2w·2^w (with non-vacuity machine-checked via CSLib's basis completeness). None of OpenAI's own definitions appear in these statements, so the formal circuit bound survives any later flaw in OpenAI's definitions of networks or of ω. All seven theorems whose axioms the file prints (the five CSLib-form theorems and the two internal ones they build on) depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and `lake env leanchecker --fresh CircuitLowerBound` replayed the full transitive closure (including Mathlib, CSLib, Complexitylib, and OpenAI's modules) into a fresh kernel environment without errors. Section 5 of the note gives details.

## Reproducing the Lean check

```sh
bash verify-lean.sh   # works in ~/lean-work (or set LEAN_WORK); also checks CircuitLowerBound.lean
```

## Build the PDF

```sh
latexmk -pdf main.tex
cp main.pdf paper.pdf
```
