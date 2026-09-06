# Lean formalization of Erdős #1075

[`Erdos1075.erdos1075_counterexamples`](Erdos1075/Main.lean) formalizes
Theorem 1 and its extension to every `r ≥ 8` in the
[current manuscript](PROOF.tex).

## Exact statement

For every natural number `r ≥ 8` and real `γ > 1 / r^r`, there is `ε > 0`
such that, for every `N₀`, there are `N ≥ N₀` and a finite `r`-uniform
hypergraph `H` on `Fin N` satisfying

```text
(1 + ε) * (N / r)^r ≤ |E(H)|
∀ S ≠ ∅, |E(H[S])| < γ * |S|^r.
```

Density expressions are real-valued, and `ε` is fixed before `N₀`.
`UniformHypergraph` represents edges as finite sets; `inducedEdges H S`
selects those contained in `S`. Any subgraph on `S` has at most this many
edges, so the induced-subgraph bound implies the bound in the original problem.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run:

```sh
lake exe cache get
lake build
lake env lean Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1075
```

The toolchain is Lean `v4.33.0-rc2`; `lake-manifest.json` pins mathlib to
`51e6992efd06126df61a496bebf8f49482a4e129`.

## Proof correspondence

| Manuscript component | Lean implementation |
| --- | --- |
| Finite threshold crossing and quantitative cubic path loss | [`Cubic.lean`](Erdos1075/Cubic.lean), `path_cubic_bound` |
| Finite AM–GM and the final scalar estimate | [`Scalar.lean`](Erdos1075/Scalar.lean), `path_scalar_bound` |
| Complete degree-8 open-path upper bound, with homogeneous normalization | [`Path.lean`](Erdos1075/Path.lean), `path_bound` |
| Explicit vertex and edge families, simplicity, uniformity, polynomial identity | [`Construction.lean`](Erdos1075/Construction.lean), `cycleGraph_polynomial` |
| Elementary symmetric bound and the `1 / 7!` deletion estimate | [`Derivative.lean`](Erdos1075/Derivative.lean), `polynomial_zeroAt_bound` |
| Cycle upper bound `8^(-8) + 1 / (7! n)` | [`CycleBound.lean`](Erdos1075/CycleBound.lean), `cycle_upper_bound` |
| Prescribed integer class sizes and positive excess | [`Witness.lean`](Erdos1075/Witness.lean), `classSize_polynomial_density` |
| Blowup polynomial and edge counts | [`Blowup.lean`](Erdos1075/Blowup.lean), `blowup_polynomial`, `blowup_card_edges` |
| Lifting to higher uniformities | [`Suspension.lean`](Erdos1075/Suspension.lean), `suspension_bound` |
| Integer witnesses after lifting | [`LiftedWitness.lean`](Erdos1075/LiftedWitness.lean) |
| Induced-subgraph bounds and arbitrarily large labelled counterexamples | [`Counterexamples.lean`](Erdos1075/Counterexamples.lean), `arbitrarily_large_blowups` |
| All parameters and quantifiers combined | [`Main.lean`](Erdos1075/Main.lean), `erdos1075_counterexamples` |

The implementation works with universal polynomial bounds rather than
defining the Lagrangian as a supremum. The scalar estimate uses a polynomial
certificate equivalent to the manuscript's AM–GM argument. Setting one
`A_i` weight to zero opens the cycle and gives the same `1 / (7! n)` error bound.
