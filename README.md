# The list-distinctness theorem behind ω = 9/4 implies superlinear Boolean circuit lower bounds

Daniel Weis · November 25, 2026 · [PDF](paper.pdf)

OpenAI's preprint *The matrix multiplication exponent is nine fourths* (November 24, 2026) proves ω = 9/4. Its lower bound, ω ≥ 9/4, is proved by contradiction with a lower bound on tensor networks that test list distinctness (its Theorem 2.2). This note observes that Boolean circuits translate into such networks with constant-factor overhead. Theorem 2.2 therefore implies that fan-in-two Boolean circuits deciding element distinctness on N input bits need Ω(N (log N)^σ) gates for a constant σ > 0. As far as we know, no superlinear lower bound against general Boolean circuits was previously known for any function in NP; element distinctness is even in uniform AC⁰. The note also derives bounds for the AND of many independent instances and for circuits that count witnesses modulo p, including unambiguous ones.

**Status.** Theorem 2.2 has not been refereed, but its formal version (`ManyList`) is proved in the Lean development accompanying the OpenAI preprint, as part of the formal proof of ω = 9/4. We built that development at commit `3344da5` with Lean 4.34.1 and confirmed that `square_exponent`, `manyList` and `manyList_full` depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

On top of it, `CircuitLowerBound.lean` formalizes the main theorem of this note (with weaker constants), stated with the circuit and element-distinctness definitions of two independent libraries that the OpenAI development already pins: [CSLib](https://github.com/leanprover/cslib) (`Cslib.Circuits.Circuit`, `Computes`, `ecomplexity`, the full binary and De Morgan bases) and [Complexitylib](https://github.com/cslib-community/complexitylib) (`elementDistinctness`). For example, `full_basis_complexity` proves that for every constant c and all large w, the circuit complexity of `elementDistinctness (2^w) (2w)` over the full binary basis exceeds c·N, where N = 2w·2^w. All five main theorems depend only on the standard axioms. What remains unchecked by machine is that those library definitions mean what they appear to mean. Section 5 of the note gives details.

## Reproducing the Lean check

```sh
bash verify-lean.sh   # works in ~/lean-work (or set LEAN_WORK); also checks CircuitLowerBound.lean
```

## Build the PDF

```sh
latexmk -pdf main.tex
cp main.pdf paper.pdf
```
