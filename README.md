# Erdős Problem #1075: counterexamples for every $r\ge 16$

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22367904.svg)](https://doi.org/10.5281/zenodo.22367904)

Preprint giving **counterexamples** to
[Erdős Problem #1075](https://www.erdosproblems.com/1075) for every $r\ge 16$, so the
problem as stated for all $r\ge 3$ has a negative answer. The endpoint question remains
open for $3\le r\le 15$.

**Qiyuan Gu**, University of Chicago, <phoenix1203@uchicago.edu>

[Preprint PDF](PROOF.pdf) · [LaTeX source](PROOF.tex) ·
[Lean formalization](Erdos1075/Main.lean) · [Build instructions](FORMALIZATION.md)

Published version: [v2](https://doi.org/10.5281/zenodo.22380117), 5 September 2026.

Comments and corrections: [email](mailto:phoenix1203@uchicago.edu) or
[issue](https://github.com/FireflySentinel/erdos-1075/issues).

## The problem

Let $r\ge 3$. Is there a constant $c_r>r^{-r}$ such that, for any $\epsilon>0$ and all
sufficiently large $n$, every $r$-uniform hypergraph on $n$ vertices with at least
$(1+\epsilon)(n/r)^r$ edges contains a subgraph on $m$ vertices with at least $c_rm^r$
edges, where $m=m(n)\to\infty$?

Erdős proved the statement with $c_r=r^{-r}$ under the stronger hypothesis of at least
$\epsilon n^r$ edges (*On extremal problems of graphs and generalized graphs*,
Israel J. Math. **2** (1964), 183–190). Problem 1075 asks whether the constant can be
pushed strictly above $r^{-r}$ at the smaller edge density.

## Main theorem

**Theorem 1.** For every $\gamma>16^{-16}$ there is an $\varepsilon>0$ and there are
arbitrarily large $16$-uniform hypergraphs $H$ such that

$$e(H)\ge(1+\varepsilon)\left(\frac{v(H)}{16}\right)^{16},
\qquad e(H[S])<\gamma|S|^{16}\ \text{ for every nonempty } S\subseteq V(H).$$

So no $c_{16}>16^{-16}$ can work. **Corollary 2** lifts this to every $r\ge 16$ by
adjoining $r-16$ common vertices to every edge (Peng's lifting step), so Problem 1075, as a
statement for all $r\ge 3$, has a negative answer.

The proof constructs explicit finite hypergraphs $G_n$ whose unnormalized Lagrangians
satisfy

$$16^{-16}\left(1+\frac{1}{4(14n)^{14}}\right)\le\lambda(G_n)\le 16^{-16}+\frac{1}{15!\,n},$$

and takes blow-ups. The construction uses two families of bipartite links arranged around
a cycle; a quantitative inequality for the corresponding open paths gives the upper bound.

## Relation to earlier work

In the usual density normalization, the result makes the endpoint
$r!/r^r$ a non-jump for every $r\ge16$. Earlier non-jump constructions and
Peng's lifting theorem are discussed in §1 of the preprint. The cyclic
construction falls outside Shaw's finite-pattern criterion; see §1 for
the comparison.

## Declaration of generative AI and AI-assisted technologies

OpenAI Codex (GPT-6 Astra) was used to generate the mathematical proofs,
draft the manuscript, and write the Lean formalization. GPT-5.6 Sol and
Claude Opus 5 were used only for editorial review of the exposition. The
author reviewed the final manuscript and takes full responsibility for
its content.

## Citation

```bibtex
@misc{gu2026erdos1075,
  author       = {Qiyuan Gu},
  title        = {A counterexample to Erd\H{o}s Problem 1075},
  year         = {2026},
  doi          = {10.5281/zenodo.22367904},
  howpublished = {Preprint, Zenodo},
  note         = {Erd\H{o}s Problem 1075}
}
```

Problem statement quoted from T. F. Bloom, *Erdős Problem #1075*,
<https://www.erdosproblems.com/1075>.
