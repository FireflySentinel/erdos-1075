# Lean formalization of Erdős #1075

The complete counterexample theorem for **every `r ≥ 16`** is proved in
[`Erdos1075/Main.lean`](Erdos1075/Main.lean), as
`Erdos1075.erdos1075_counterexamples`.

The source manuscript is the GitHub **v2** revision
[`a8853af27b2b35fdf0bf08c0363ab2d451632845`](https://github.com/FireflySentinel/erdos-1075/tree/a8853af27b2b35fdf0bf08c0363ab2d451632845),
including its extension from uniformity 16 to all larger uniformities.

## Exact statement

For every natural number `r ≥ 16` and real number `γ > 1 / r^r`, there is
a real `ε > 0` such that, for every natural number `N₀`, there are `N ≥ N₀`
and a finite simple `r`-uniform hypergraph `H` on `Fin N` satisfying

```text
(1 + ε) * (N / r)^r ≤ number of edges of H
```

and, for every nonempty `S : Finset (Fin N)`,

```text
number of edges of H induced on S < γ * |S|^r.
```

Here all displayed divisions and inequalities involving density are over
the real numbers. The positive `ε` is chosen **before** the arbitrary order
threshold `N₀`. The bound on induced subgraphs includes every nonempty
subset, without a lower bound on its size.

`UniformHypergraph V r` stores a `Finset (Finset V)` and a proof that every
edge has cardinality `r`. Thus edges have neither repeated vertices nor
multiplicities. `inducedEdges H S` filters precisely the edges contained in
`S`. The final theorem uses ordinary labelled vertices `Fin N`.

## Build and check

Install [Elan](https://github.com/leanprover/elan), then run from this repository:

```sh
lake exe cache get
lake build
lake env lean Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1075
```

The toolchain is pinned to `leanprover/lean4:v4.33.0-rc2`. The committed
`lake-manifest.json` pins mathlib to
`51e6992efd06126df61a496bebf8f49482a4e129` and pins all transitive dependencies.
Keep the manifest when reproducing the verification.

`Check.lean` checks the actual transitive axiom dependencies of the main
theorem, the cubic path inequality, and the cycle bound. Each has exactly
the standard Lean dependencies

```text
[propext, Classical.choice, Quot.sound]
```

There are no `sorry` placeholders, additional axioms, assumed versions of
the manuscript's new lemmas, or `native_decide` certificates. `leanchecker`
replays the compiled project declarations through Lean's kernel. It is an
additional kernel replay, not a separate implementation of Lean's logic.

The [GitHub workflow](.github/workflows/lean.yml) runs the build, axiom
checks, and kernel replay. The local commands above also work without GitHub.

Local verification on 5 September 2026 passed: `lake build` completed without
warnings, the guarded axiom checks passed, and `leanchecker` successfully
replayed all 14 project modules. The workflow is configured; these results
refer to the local verification run.

## Proof correspondence

| Manuscript component | Lean implementation |
| --- | --- |
| Finite threshold crossing and quantitative cubic path loss | [`Cubic.lean`](Erdos1075/Cubic.lean), `path_cubic_bound` |
| Finite AM–GM and the final scalar estimate | [`Scalar.lean`](Erdos1075/Scalar.lean), `path_scalar_bound` |
| Complete degree-16 open-path upper bound, including zero masses | [`Path.lean`](Erdos1075/Path.lean), `path_bound` |
| Explicit vertex and edge families, simplicity, uniformity, polynomial identity | [`Construction.lean`](Erdos1075/Construction.lean), `cycleGraph_polynomial` |
| Elementary symmetric bound and the `1 / 15!` deletion estimate | [`Derivative.lean`](Erdos1075/Derivative.lean), `polynomial_zeroAt_bound` |
| Cycle upper bound `16^(-16) + 1 / (15! n)` | [`CycleBound.lean`](Erdos1075/CycleBound.lean), `cycle_upper_bound` |
| Prescribed integer class sizes and positive excess | [`Witness.lean`](Erdos1075/Witness.lean), `classSize_polynomial_density` |
| Simple blowups and all induced-subgraph counts | [`Blowup.lean`](Erdos1075/Blowup.lean), `blowup_polynomial`, `blowup_induced_bound` |
| Lifting to higher uniformities | [`Suspension.lean`](Erdos1075/Suspension.lean), `suspension_bound` |
| Integer witnesses after lifting | [`LiftedWitness.lean`](Erdos1075/LiftedWitness.lean) |
| Arbitrarily large labelled counterexamples | [`Counterexamples.lean`](Erdos1075/Counterexamples.lean), `arbitrarily_large_blowups` |
| All parameters and quantifiers combined | [`Main.lean`](Erdos1075/Main.lean), `erdos1075_counterexamples` |

The implementation proves universal polynomial bounds directly, so it
does not need to introduce a supremum defining the Lagrangian. All the
new mathematical estimates used by the counterexample theorem are proved
inside the project.

Two elementary presentation changes simplify the Lean proof. First,
for `0 ≤ h ≤ 1/2`, the inequality `F(h) ≤ h` follows algebraically from
`h(1-h) ≤ 1/4` and `h^7 ≤ (1/2)^7`, without differentiation. Second,
setting one `A_i` weight to zero already opens the cycle. Rotation then
identifies its polynomial with a finite path whose terminal `A` weight is
zero. This gives the same `1 / (15! n)` error term as the manuscript's
deletion of an `A_i, B_i` pair.

The factorial estimate counts the orderings of each edge by an injection
into all tuples. This is a proof of a finite combinatorial identity, not
a search for counterexamples. The counterexamples and integer weights
are the explicit family specified in the manuscript.
