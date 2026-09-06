# Erdős Problem #1075: counterexamples for every $r\ge 5$

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22367904.svg)](https://doi.org/10.5281/zenodo.22367904)
[![Lean](https://github.com/FireflySentinel/erdos-1075/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/FireflySentinel/erdos-1075/actions/workflows/lean.yml)

Preprint giving **counterexamples** to
[Erdős Problem #1075](https://www.erdosproblems.com/1075) for every $r\ge 5$, so the
problem as stated for all $r\ge 3$ has a negative answer. The endpoint question remains
open for $3\le r\le 4$.

**Qiyuan Gu**, University of Chicago, <phoenix1203@uchicago.edu>

[Preprint PDF](PROOF.pdf) · [LaTeX source](PROOF.tex) ·
[Lean formalization](Erdos1075/Main.lean) · [Build instructions](FORMALIZATION.md)

## The problem

Let $r\ge 3$. Is there a constant $c_r>r^{-r}$ such that, for any $\epsilon>0$ and all
sufficiently large $n$, every $r$-uniform hypergraph on $n$ vertices with at least
$(1+\epsilon)(n/r)^r$ edges contains a subgraph on $m$ vertices with at least $c_rm^r$
edges, where $m=m(n)\to\infty$?

Erdős proved the statement with $c_r=r^{-r}$ assuming only at least
$\epsilon n^r$ edges for any fixed $\epsilon>0$ (*On extremal problems of graphs and
generalized graphs*, Israel J. Math. **2** (1964), 183–190). Problem 1075 asks whether
the stronger assumption of at least $(1+\epsilon)(n/r)^r$ edges allows a constant
strictly greater than $r^{-r}$.

## Main theorem

**Theorem 1.** For every $\gamma>5^{-5}$ there is an $\varepsilon>0$ and there are
arbitrarily large $5$-uniform hypergraphs $H$ such that

$$e(H)\ge(1+\varepsilon)\left(\frac{v(H)}{5}\right)^{5},
\qquad e(H[S])<\gamma|S|^{5}\ \text{ for every nonempty } S\subseteq V(H).$$

So no $c_{5}>5^{-5}$ can work. **Corollary 7** lifts this to every $r\ge 5$ by
adjoining $r-5$ common vertices to every edge (Peng's lifting step), so Problem 1075, as a
statement for all $r\ge 3$, has a negative answer.

The proof constructs explicit finite hypergraphs $G_n$ whose unnormalized Lagrangians
satisfy

$$5^{-5}\left(1+\frac{1}{4(3n)^{3}}\right)\le\lambda(G_n)\le 5^{-5}+\frac{1}{4!\,n},$$

and takes blow-ups. The construction uses two families of bipartite links arranged around
a cycle; a quantitative inequality for the corresponding open paths gives the upper bound.

## Relation to earlier work

In the usual density normalization, the result makes the endpoint
$r!/r^r$ a non-jump for every $r\ge5$. Earlier non-jump constructions and
Peng's lifting theorem are discussed in §1 of the preprint. The cyclic
construction falls outside Shaw's finite-pattern criterion; see §1 for
the comparison.

## AI use disclosure

GPT-6 Astra was used to generate the mathematical proofs, draft the manuscript,
and perform the lean formalization. GPT-5.6 Sol and Claude Opus 5 were used only
for editorial review of the exposition. GPT-6 Astra was run in a research
environment containing earlier results produced by GPT-5.6 Sol and Claude Opus 5,
but those earlier results did not contribute to the final mathematical arguments.
The author reviewed the final manuscript and takes full responsibility for its
content.
