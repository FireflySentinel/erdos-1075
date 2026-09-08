# Erdős Problem #1075: counterexamples for every $r\ge 5$

[Preprint](paper/PROOF.pdf) giving **counterexamples** to
[Erdős Problem #1075](https://www.erdosproblems.com/1075) for every $r\ge 5$.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1075
```

## Proof correspondence

| Manuscript component | Lean source |
|---|---|
| Quantitative cubic path loss | [Cubic.lean](Erdos1075/Cubic.lean), `path_cubic_bound` |
| Complete degree-5 open-path upper bound | [Path.lean](Erdos1075/Path.lean), `path_bound` |
| Cycle upper bound `5^(-5) + 1 / (4! n)` | [CycleBound.lean](Erdos1075/CycleBound.lean), `cycle_upper_bound` |
| Lifting to higher uniformities | [Suspension.lean](Erdos1075/Suspension.lean), `suspension_bound` |
| Theorem 1 and all quantifiers combined | [Main.lean](Erdos1075/Main.lean), `erdos1075_counterexamples` |

The [proof bridge](checks/FormalConjecturesBridge.lean) derives the corresponding
problem statements and is included in `lake test`.

## Use of generative AI

GPT-6 Astra proposed the argument and generated the Lean formalization.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review.
The author completed the manuscript and is responsible for the content.
