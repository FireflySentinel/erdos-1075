# Erdős Problem #1075: counterexamples for every $r\ge 5$

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22367904.svg)](https://doi.org/10.5281/zenodo.22367904)
[![Lean](https://github.com/FireflySentinel/erdos-1075/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/FireflySentinel/erdos-1075/actions/workflows/lean.yml)

Preprint giving **counterexamples** to
[Erdős Problem #1075](https://www.erdosproblems.com/1075) for every $r\ge 5$, so the
problem as stated for all $r\ge 3$ has a negative answer. The endpoint question remains
open for $3\le r\le 4$.

**Qiyuan Gu**, University of Chicago, <phoenix1203@uchicago.edu>

[Preprint PDF](PROOF.pdf)

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1075
```

See [FORMALIZATION.md](FORMALIZATION.md) for the exact statement and proof correspondence.

## AI use disclosure

GPT-6 Astra was used to generate the mathematical proofs, draft the manuscript,
and perform the lean formalization. GPT-5.6 Sol and Claude Opus 5 were used only
for editorial review of the exposition. GPT-6 Astra was run in a research
environment containing earlier results produced by GPT-5.6 Sol and Claude Opus 5,
but those earlier results did not contribute to the final mathematical arguments.
The author reviewed the final manuscript and takes full responsibility for its
content.
