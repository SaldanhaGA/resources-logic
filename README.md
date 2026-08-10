# A Mechanized Resource-Aware Hoare Logic with Asymptotic Assertions

A [Lean 4](https://lean-lang.org/) (+
[Mathlib](https://github.com/leanprover-community/mathlib4)) mechanization of
the resource-aware Hoare logic of Ana Carolina Ferreira da Silva, _Formal
Verification of Resource Usage_ (MSc dissertation, University of Porto, 2022).

The dissertation defines an annotated imperative `while`-language, a
cost-instrumented operational semantics, and Hoare logics over cost-annotated
triples `{P} S {Q | t}` (worst-case upper bound, amortized, and exact cost),
each with a verification condition generator (VCG). This project mechanizes
those definitions and reconstructs their pen-and-paper proofs. Doing so
uncovered two genuine errors in the source text and led to a
**relative-completeness** result that the dissertation leaves open. The
development is further extended with elementary **asymptotic cost assertions**
(`O`, `Ω`, `Θ`) lifted to the level of triples.

## Requirements

- [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager. The
  exact compiler version is pinned in [`lean-toolchain`](lean-toolchain)
  (`leanprover/lean4:v4.32.0`) and is installed automatically by `elan` on the
  first `lake` invocation.
- The build pulls in Mathlib `v4.32.0` as a dependency (declared in
  `lakefile.toml`).

No system-wide Lean installation is needed; `elan` selects the pinned toolchain
inside this directory.

## Building

From the repository root:

```sh
# 1. Download the prebuilt Mathlib artifacts (avoids compiling Mathlib from
#    source, which would take hours). This also resolves the dependency.
lake exe cache get

# 2. Build the whole development.
lake build
```

A successful run ends with `Build completed successfully`. The first build is
dominated by downloading and unpacking the Mathlib cache; afterwards,
`lake build` is incremental.

## Checking the proofs are complete

The development contains no `sorry`, and every result rests only on the three
standard Lean axioms. To confirm this for a few representative theorems, create
a file with the following contents and run it with `lake env lean <file>`:

```lean
import ResourcesLogic
open ResourcesLogic
#print axioms Hoare.sound       -- [propext, Quot.sound]
#print axioms Hoare.complete    -- [propext, Classical.choice, Quot.sound]
#print axioms vcg_sound         -- [propext, Classical.choice, Quot.sound]
```
