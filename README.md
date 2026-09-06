# Erdős Problem #1075: counterexamples for every $r\ge 5$

Preprint giving **counterexamples** to
[Erdős Problem #1075](https://www.erdosproblems.com/1075) for every $r\ge 5$, so the
problem as stated for all $r\ge 3$ has a negative answer. The endpoint question remains
open for $3\le r\le 4$.

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
Theorem 1 and its extension to every `r ≥ 5`.

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

| Manuscript component | Lean source |
|---|---|
| Quantitative cubic path loss | [Cubic.lean](Erdos1075/Cubic.lean), `path_cubic_bound` |
| Complete degree-5 open-path upper bound | [Path.lean](Erdos1075/Path.lean), `path_bound` |
| Cycle upper bound `5^(-5) + 1 / (4! n)` | [CycleBound.lean](Erdos1075/CycleBound.lean), `cycle_upper_bound` |
| Lifting to higher uniformities | [Suspension.lean](Erdos1075/Suspension.lean), `suspension_bound` |
| Theorem 1 and all quantifiers combined | [Main.lean](Erdos1075/Main.lean), `erdos1075_counterexamples` |

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs, draft the manuscript,
and perform the lean formalization. GPT-5.6 Sol and Claude Opus 5 were used only
for editorial review of the exposition. GPT-6 Astra was run in a research
environment containing earlier results produced by GPT-5.6 Sol and Claude Opus 5,
but those earlier results did not contribute to the final mathematical arguments.
The author reviewed the final manuscript and takes full responsibility for its
content.
