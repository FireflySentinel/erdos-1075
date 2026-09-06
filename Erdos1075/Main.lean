import Erdos1075.CycleBound
import Erdos1075.LiftedWitness
import Erdos1075.Counterexamples

namespace Erdos1075

open Finset CycleVertex

private lemma exists_cycle_bound_below (β : ℝ) (hβ : baseDensity < β) :
    ∃ n : ℕ, 2 ≤ n ∧ baseDensity + 1 / ((7 : ℕ).factorial * (n : ℝ)) < β := by
  have hδ : 0 < β - baseDensity := sub_pos.mpr hβ
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) ((1 / (7 : ℕ).factorial) / (β - baseDensity)))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn2 : 2 ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hlarge : (1 / (7 : ℕ).factorial) / (β - baseDensity) < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hmul := (div_lt_iff₀ hδ).mp hlarge
  have hsmall : (1 / (7 : ℕ).factorial) / (n : ℝ) < β - baseDensity :=
    (div_lt_iff₀ hn0).mpr (by nlinarith only [hmul])
  have heq : (1 / (7 : ℕ).factorial) / (n : ℝ) = 1 / ((7 : ℕ).factorial * (n : ℝ)) := by ring
  rw [heq] at hsmall
  exact ⟨n, hn2, by linarith⟩

/-- The complete counterexample theorem in uniformity `8 + q`. -/
theorem counterexamples_eight_add (q : ℕ) (γ : ℝ)
    (hγ : 1 / ((8 + q : ℕ) : ℝ) ^ (8 + q) < γ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ,
      ∃ N ≥ N₀, ∃ H : UniformHypergraph (Fin N) (8 + q),
        (1 + ε) * ((N : ℝ) / ((8 + q : ℕ) : ℝ)) ^ (8 + q) ≤ (H.edges.card : ℝ) ∧
        ∀ S : Finset (Fin N), S.Nonempty → ((H.inducedEdges S).card : ℝ) < γ * (S.card : ℝ) ^ (8 + q) := by
  have hr : (0 : ℝ) < (8 + q : ℕ) := by positivity
  have hrpow : (0 : ℝ) < ((8 + q : ℕ) : ℝ) ^ (8 + q) := pow_pos hr _
  have h8pow : (0 : ℝ) < (8 : ℝ) ^ 8 := by norm_num
  let β := γ * ((8 + q : ℕ) : ℝ) ^ (8 + q) / (8 : ℝ) ^ 8
  have hβ : baseDensity < β := by
    have hmul := (div_lt_iff₀ hrpow).mp hγ
    exact (div_lt_div_iff_of_pos_right h8pow).mpr hmul
  obtain ⟨n, hn, hnβ⟩ := exists_cycle_bound_below β hβ
  have : NeZero n := ⟨by omega⟩
  let c := baseDensity + 1 / ((7 : ℕ).factorial * (n : ℝ))
  let α := c * (8 : ℝ) ^ 8 / ((8 + q : ℕ) : ℝ) ^ (8 + q)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact add_nonneg baseDensity_pos.le (by positivity)
  have hαγ : α < γ := by
    have hmul := mul_lt_mul_of_pos_right hnβ h8pow
    have hdiv := div_lt_div_of_pos_right hmul hrpow
    convert hdiv using 1 <;> first | rfl | (dsimp [α, c, β]; field_simp)
  refine ⟨witnessExcess n, witnessExcess_pos n (by omega), ?_⟩
  intro N₀
  apply ((cycleGraph (finRotate n)).suspension q).arbitrarily_large_blowups
    (by omega) (liftedClassSize n q) (by rw [liftedClassSize_sum n q (by omega)]; positivity)
    (witnessExcess n) α γ hαγ (liftedClassSize_density n q (by omega) (finRotate n))
    (N₀ := N₀)
  intro x hx hmass
  exact (cycleGraph (finRotate n)).suspension_bound (by norm_num) q c hc
    (fun x hx hmass => cycle_upper_bound x hx hmass) x hx hmass

/-- Counterexamples to Erdős Problem 1075 for every r ≥ 8. -/
theorem erdos1075_counterexamples (r : ℕ) (hr : 8 ≤ r) (γ : ℝ)
    (hγ : 1 / (r : ℝ) ^ r < γ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ,
      ∃ N ≥ N₀, ∃ H : UniformHypergraph (Fin N) r,
        (1 + ε) * ((N : ℝ) / (r : ℝ)) ^ r ≤ (H.edges.card : ℝ) ∧
        ∀ S : Finset (Fin N), S.Nonempty → ((H.inducedEdges S).card : ℝ) < γ * (S.card : ℝ) ^ r := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
  exact counterexamples_eight_add q γ hγ

end Erdos1075
