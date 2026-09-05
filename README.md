# Erdős Problem #1075 — counterexamples for every $r\ge 16$

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22367904.svg)](https://doi.org/10.5281/zenodo.22367904)

Preprint giving **counterexamples** to
[Erdős Problem #1075](https://www.erdosproblems.com/1075) for every $r\ge 16$, so the
problem as stated for all $r\ge 3$ has a negative answer. The endpoint question remains
open for $3\le r\le 15$.

**Qiyuan Gu**, University of Chicago — <phoenix1203@uchicago.edu>

## Status

| | |
|---|---|
| Manuscript | v2, 9 pages, 5 September 2026 — [`PROOF.pdf`](PROOF.pdf), [`PROOF.tex`](PROOF.tex) |
| DOI | [10.5281/zenodo.22367904](https://doi.org/10.5281/zenodo.22367904) (always the latest version; v2 is [10.5281/zenodo.22380117](https://doi.org/10.5281/zenodo.22380117)) |
| erdosproblems.com | listed **open** as of 5 September 2026, no proof claims submitted |
| Refereeing | not yet refereed |

> **If you — or an automated agent you are running — are looking for open work on
> Erdős #1075:** counterexamples for every $r\ge 16$ are claimed here. Please read the PDF before
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

So no $c_{16}>16^{-16}$ can work. **Corollary 2** lifts this to every $r\ge 16$ by
adjoining $r-16$ common vertices to every edge (Peng's lifting step), so Problem 1075, as a
statement for all $r\ge 3$, has a negative answer.

The conclusion is stronger than the formulation of the problem, since the bound holds for
*every* nonempty vertex subset.

The proof constructs explicit finite hypergraphs $G_n$ whose unnormalized Lagrangians
satisfy

$$16^{-16}\left(1+\frac{1}{4(14n)^{14}}\right)\le\lambda(G_n)\le 16^{-16}+\frac{1}{15!\,n},$$

and takes blow-ups. The construction uses two families of bipartite links arranged around
a cycle; a quantitative inequality for the corresponding open paths gives the upper bound.

**Scope.** The endpoint question remains **open for $3\le r\le 15$**, including the case
$2/9$ for $3$-graphs.

## Where this sits in the literature

With the usual density $d(H)=e(H)/\binom{v(H)}{r}$ the threshold $(N/r)^r$ corresponds to
$\alpha_r=r!/r^r$, and Problem 1075 is the *endpoint* question at $\alpha_r$: Erdős proved
every number in $[0,\alpha_r)$ is a jump for $r$-graphs.

| | |
|---|---|
| Frankl–Rödl (1984) | disproved the earlier jumping constant conjecture, giving non-jumps for every $r\ge3$ |
| Frankl–Peng–Rödl–Talbot (2007) | $(5/2)\,r!/r^r$ is a non-jump for every $r\ge3$ |
| Peng (2009) | lifting theorem carrying a non-jump $c\,r!/r^r$ to all larger uniformities |
| Yan–Peng (2023) | $12/25$ is a non-jump for $3$-graphs, hence $(54/25)\,r!/r^r$ for every $r\ge3$ |
| Shaw (2026) | $2\,r!/r^r$ is a non-jump for $r\ge4$, and **no smaller non-jump follows from his finite-pattern formulation** of the Frankl–Rödl method |
| Liu–Mubayi (2026) | $4/9$ is a non-jump for $3$-graphs, by a construction *outside* that framework |
| **this preprint** | the endpoint $r!/r^r$ itself is a non-jump for every $r\ge16$ |

Because of Shaw's barrier, the paper states explicitly why it is not caught by it: the
construction is **not an instance of Shaw's finite-pattern criterion** — its distinguished
links follow a matching $A_iB_i$ and a shifted matching $B_iA_{i+1}$ around a cycle, and
the proof controls the full Lagrangian of a growing sequence $G_n$ — so Shaw's Theorem 4.3
does not apply.

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

## Declaration of generative AI and AI-assisted technologies

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used only for editorial review of the exposition.
GPT-6 Astra was run in a research environment containing earlier results produced by
GPT-5.6 Sol and Claude Opus 5, but those earlier results did not contribute to the final
mathematical arguments. The author reviewed the final manuscript and takes full
responsibility for its content.

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
