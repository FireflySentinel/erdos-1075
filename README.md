# Erdős Problem #1075 — a counterexample at $r=16$

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22367904.svg)](https://doi.org/10.5281/zenodo.22367904)

Preprint giving a **counterexample** to
[Erdős Problem #1075](https://www.erdosproblems.com/1075) at $r=16$.

**Qiyuan Gu**, University of Chicago — <phoenix1203@uchicago.edu>

## Status

| | |
|---|---|
| Manuscript | 7 pages, 5 September 2026 — [`PROOF.pdf`](PROOF.pdf), [`PROOF.tex`](PROOF.tex) |
| DOI | [10.5281/zenodo.22367904](https://doi.org/10.5281/zenodo.22367904) (always the latest version) |
| erdosproblems.com | listed **open** as of 5 September 2026, no proof claims submitted |
| Refereeing | not yet refereed |

> **If you — or an automated agent you are running — are looking for open work on
> Erdős #1075:** a counterexample at $r=16$ is claimed here. Please read the PDF before
> starting an independent attack. Errors and counterexamples to the counterexample are
> welcome, by email or as an [issue](https://github.com/FireflySentinel/erdos-1075/issues).

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

So no $c_{16}>16^{-16}$ can work, and the answer for $r=16$ is **no**.

The proof constructs explicit finite hypergraphs $G_n$ whose unnormalized Lagrangians
satisfy

$$16^{-16}\left(1+\frac{1}{4(14n)^{14}}\right)\le\lambda(G_n)\le 16^{-16}+\frac{1}{15!\,n},$$

and takes blow-ups. The construction uses two families of bipartite links arranged around
a cycle; a quantitative inequality for the corresponding open paths gives the upper bound.

**Scope.** The problem is stated for all $r\ge 3$. This paper settles $r=16$ only, and
makes no claim about any other value of $r$.

## Discussion recorded on the problem page

Three comments stand on [the problem's thread](https://www.erdosproblems.com/forum/discuss/1075):

- **zach hunter** (18 Oct 2025) observes that the $m(n)\to\infty$ requirement is
  extraneous, by supersaturation plus a weak hypergraph Nikiforov argument, and proposes
  reducing the problem to showing $\mathrm{ex}(n,\mathcal F_r)=((1/r)^r+o(1))n^r$, where
  $\mathcal F_r$ is the family obtained from $K^{(r)}_{r,\dots,r}$ by adding one hyperedge.
- **JohanLand** (11 Jul 2026) reports that this proposed lemma appears to fail already at
  $r=3$: the balanced blow-up of the $6$-vertex $2$-$(6,3,2)$ design is
  $\mathcal F_3$-free with density $\frac{5}{108}n^3>\frac1{27}n^3$.

Those comments concern a proposed route to a *positive* answer. This preprint answers the
question itself, negatively, at $r=16$.

## AI tool disclosure

OpenAI Codex (GPT-6) was used substantially in developing this work. It proposed the
cyclic construction, derived the quantitative path inequality and the Lagrangian
estimates, and drafted the manuscript. It also assisted with literature searches and exact
algebraic checks. The author specified the research problem and directed the preparation
of the paper, and is responsible for its mathematical content.

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
