# Erdős Problem #1075: counterexamples for every $r\ge 6$

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22367904.svg)](https://doi.org/10.5281/zenodo.22367904)

Preprint giving **counterexamples** to
[Erdős Problem #1075](https://www.erdosproblems.com/1075) for every $r\ge 6$, so the
problem as stated for all $r\ge 3$ has a negative answer. The endpoint question remains
open for $3\le r\le 5$.

**Qiyuan Gu**, University of Chicago, <phoenix1203@uchicago.edu>

[Preprint PDF](PROOF.pdf) · [LaTeX source](PROOF.tex) ·
[Lean formalization](Erdos1075/Main.lean) · [Build instructions](FORMALIZATION.md)

This revision lowers the base uniformity to $r=6$.
The published [v2](https://doi.org/10.5281/zenodo.22380117), 5 September 2026,
established counterexamples for $r\ge16$.

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

**Theorem 1.** For every $\gamma>6^{-6}$ there is an $\varepsilon>0$ and there are
arbitrarily large $6$-uniform hypergraphs $H$ such that

$$e(H)\ge(1+\varepsilon)\left(\frac{v(H)}{6}\right)^{6},
\qquad e(H[S])<\gamma|S|^{6}\ \text{ for every nonempty } S\subseteq V(H).$$

So no $c_{6}>6^{-6}$ can work. **Corollary 6** lifts this to every $r\ge 6$ by
adjoining $r-6$ common vertices to every edge (Peng's lifting step), so Problem 1075, as a
statement for all $r\ge 3$, has a negative answer.

The proof constructs explicit finite hypergraphs $G_n$ whose unnormalized Lagrangians
satisfy

$$6^{-6}\left(1+\frac{1}{4(4n)^{4}}\right)\le\lambda(G_n)\le 6^{-6}+\frac{1}{5!\,n},$$

and takes blow-ups. The construction uses two families of bipartite links arranged around
a cycle; a quantitative inequality for the corresponding open paths gives the upper bound.

## Relation to earlier work

In the usual density normalization, the result makes the endpoint
$r!/r^r$ a non-jump for every $r\ge6$. Earlier non-jump constructions and
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
