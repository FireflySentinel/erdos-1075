import Erdos1075

/-! # Explicit statements for Erdős Problem 1075

The hypergraph counterexamples refute the density-increment assertion for every
$r\geq5$, and hence its universal form.
-/

noncomputable section

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


/-- The density-increment assertion fails for every uniformity $r\geq5$. -/
theorem erdos_1075.variants.r_ge_five :
    ∀ r : ℕ, 5 ≤ r → ¬HasDensityIncrement r := by
  intro r hr h
  obtain ⟨c, hc, h⟩ := h
  obtain ⟨ε, hε, hcounter⟩ := erdos1075_counterexamples r hr c hc
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h ε hε 1)
  obtain ⟨N, hN, H, hlarge, hsmall⟩ := hcounter N₀
  obtain ⟨S, hS, hden⟩ := hN₀ N hN H.edges H.uniform hlarge
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  exact (not_le_of_gt (hsmall S hne)) hden

/-- info: 'Erdos1075.erdos_1075.variants.r_ge_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1075.erdos_1075.variants.r_ge_five

/-- The density-increment assertion does not hold for all $r\geq3$. -/
theorem erdos_1075 :
    ¬∀ r : ℕ, 3 ≤ r → HasDensityIncrement r := by
  intro h
  exact erdos_1075.variants.r_ge_five 5 (by norm_num) (h 5 (by norm_num))

/-- info: 'Erdos1075.erdos_1075' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1075.erdos_1075

end Erdos1075
