# QLean

QLean is a Lean 4 framework for formal verification of fixed-register quantum programs.
It provides:

- computational-basis-indexed matrices for finite quantum registers;
- reusable full-register gates and single-qubit gate embeddings;
- the `QLean.QProg σ n α` deep embedding for fixed-register quantum programs;
- expectation-style weakest preconditions and Hoare triples; and
- Bell-state demos, an exact four-element Grover proof, and a general Grover WP proof with
  explicit success verification conditions.

All library declarations live under the `QLean` namespace.  For example, use `QLean.QProg`,
`QLean.QMat`, `QLean.QProg.QHoare`, and `QLean.Gate` after importing the relevant modules.

```lean
import QLean

open QLean
```

Build the library with:

```bash
lake exe cache get
lake build QLean
```

The library currently targets Lean/mathlib `v4.30.0`.
