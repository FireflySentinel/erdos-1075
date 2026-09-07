/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 1075

*References:*
- [erdosproblems.com/1075](https://www.erdosproblems.com/1075)
- [Er64f] Erdős, P., On extremal problems of graphs and generalized graphs.
  Israel J. Math. (1964), 183–190.
- [Gu26] Gu, Q., Counterexamples to Erdős Problem 1075.
  https://github.com/FireflySentinel/erdos-1075
-/

open Filter

namespace Erdos1075

/-- The density-increment assertion at uniformity $r$. Requiring arbitrarily
large prescribed lower bounds on the subgraph order expresses $m(n)\to\infty$.
The finite family $E$ represents a simple hypergraph on $\operatorname{Fin} n$. -/
def HasDensityIncrement (r : ℕ) : Prop :=
  ∃ c : ℝ, 1 / (r : ℝ) ^ r < c ∧ ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
    ∀ᶠ n : ℕ in atTop, ∀ E : Finset (Finset (Fin n)),
      (∀ e ∈ E, e.card = r) →
      (1 + ε) * ((n : ℝ) / (r : ℝ)) ^ r ≤ (E.card : ℝ) →
      ∃ S : Finset (Fin n), m ≤ S.card ∧
        c * (S.card : ℝ) ^ r ≤ ((E.filter (fun e => e ⊆ S)).card : ℝ)

/--
Let $r\geq 3$. There exists $c_r>r^{-r}$ such that, for any $\epsilon>0$,
if $n$ is sufficiently large, the following holds.
Any $r$-uniform hypergraph on $n$ vertices with at least $(1+\epsilon)(n/r)^r$ many
edges contains a subgraph on $m$ vertices with at least $c_rm^r$ edges, where
$m=m(n)\to \infty$ as $n\to \infty$.

Gu [Gu26] gives counterexamples for every $r\geq5$. An induced subgraph has at
least as many edges as any subgraph on the same vertex set.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/FireflySentinel/erdos-1075/blob/25a8630842853b70873e4c0a72b85d403413972b/checks/FormalConjecturesBridge.lean#L49"]
theorem erdos_1075 :
    ¬∀ r : ℕ, 3 ≤ r → HasDensityIncrement r := by
  sorry

/--
The density-increment assertion is false for every $r\geq5$ [Gu26].
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/FireflySentinel/erdos-1075/blob/25a8630842853b70873e4c0a72b85d403413972b/checks/FormalConjecturesBridge.lean#L33"]
theorem erdos_1075.variants.r_ge_five :
    ∀ r : ℕ, 5 ≤ r → ¬HasDensityIncrement r := by
  sorry

/--
Does the density-increment assertion hold for $r=3$?
-/
@[category research open, AMS 5]
theorem erdos_1075.variants.r_three :
    answer(sorry) ↔ HasDensityIncrement 3 := by
  sorry

/--
Does the density-increment assertion hold for $r=4$?
-/
@[category research open, AMS 5]
theorem erdos_1075.variants.r_four :
    answer(sorry) ↔ HasDensityIncrement 4 := by
  sorry

end Erdos1075
