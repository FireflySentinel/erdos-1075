# Erdős Problem #1075: counterexamples for every $r\ge 5$

Preprint giving **counterexamples** to
[Erdős Problem #1075](https://www.erdosproblems.com/1075) for every $r\ge 5$, so the
problem as stated for all $r\ge 3$ has a negative answer. The endpoint question remains
open for $3\le r\le 4$.

[Preprint PDF](paper/PROOF.pdf)

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean checks/Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1075
```

## Exact statement

[`Erdos1075.erdos1075_counterexamples`](Erdos1075/Main.lean) formalizes
Theorem 1 and its extension to every `r ≥ 5` in the
[current manuscript](paper/PROOF.tex).

For every natural number `r ≥ 5` and real `γ > 1 / r^r`, there is `ε > 0`
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

## Proof correspondence

| Manuscript component | Lean implementation |
| --- | --- |
| Quadratic potential and accumulated path energy | [`Potential.lean`](Erdos1075/Potential.lean), `potential_le_path_cost`; [`Cubic.lean`](Erdos1075/Cubic.lean), `path_square_energy` |
| Quantitative cubic path loss with coefficient `1 / 10` | [`Cubic.lean`](Erdos1075/Cubic.lean), `path_cubic_bound` |
| Finite AM–GM and the final scalar estimate | [`Scalar.lean`](Erdos1075/Scalar.lean), `path_scalar_bound` |
| Complete degree-5 open-path upper bound, with homogeneous normalization | [`Path.lean`](Erdos1075/Path.lean), `path_bound` |
| Explicit vertex and edge families, simplicity, uniformity, polynomial identity | [`Construction.lean`](Erdos1075/Construction.lean), `cycleGraph_polynomial` |
| Elementary symmetric bound and the `1 / 4!` deletion estimate | [`Derivative.lean`](Erdos1075/Derivative.lean), `polynomial_zeroAt_bound` |
| Cycle upper bound `5^(-5) + 1 / (4! n)` | [`CycleBound.lean`](Erdos1075/CycleBound.lean), `cycle_upper_bound` |
| Prescribed integer class sizes and positive excess | [`Witness.lean`](Erdos1075/Witness.lean), `classSize_polynomial_density` |
| Blowup polynomial and edge counts | [`Blowup.lean`](Erdos1075/Blowup.lean), `blowup_polynomial`, `blowup_card_edges` |
| Lifting to higher uniformities | [`Suspension.lean`](Erdos1075/Suspension.lean), `suspension_bound` |
| Integer witnesses after lifting | [`LiftedWitness.lean`](Erdos1075/LiftedWitness.lean) |
| Induced-subgraph bounds and arbitrarily large labelled counterexamples | [`Counterexamples.lean`](Erdos1075/Counterexamples.lean), `arbitrarily_large_blowups` |
| All parameters and quantifiers combined | [`Main.lean`](Erdos1075/Main.lean), `erdos1075_counterexamples` |

The implementation works with universal polynomial bounds rather than
defining the Lagrangian as a supremum. The scalar estimate uses the same binomial
expansion as the manuscript. Setting one
`A_i` weight to zero opens the cycle and gives the same `1 / (4! n)` error bound.

## AI use disclosure

GPT-6 Astra was used to generate the mathematical proofs, draft the manuscript,
and perform the lean formalization. GPT-5.6 Sol and Claude Opus 5 were used only
for editorial review of the exposition. GPT-6 Astra was run in a research
environment containing earlier results produced by GPT-5.6 Sol and Claude Opus 5,
but those earlier results did not contribute to the final mathematical arguments.
The author reviewed the final manuscript and takes full responsibility for its
content.
