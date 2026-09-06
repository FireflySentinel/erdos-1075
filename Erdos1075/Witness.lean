import Erdos1075.Construction

namespace Erdos1075

open Finset CycleVertex

/-- The integer class sizes of the rational witness in the manuscript. -/
def classSize (n : ℕ) : CycleVertex n → ℕ
  | Sum.inl _ => 6
  | Sum.inr (Sum.inl _) => 6
  | Sum.inr (Sum.inr (Sum.inl _)) => 6 * (n - 1)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 3 * n
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => 3 * n
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))))) => 6 * n
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _))))) => 2

lemma classSize_sum (n : ℕ) (hn : 1 ≤ n) : (∑ v, classSize n v) = 30 * n := by
  simp [CycleVertex, Fintype.sum_sum_type, classSize]
  omega

lemma classSize_polynomial (n : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) :
    (cycleGraph σ).polynomial (fun v => (classSize n v : ℝ)) = (6 * (n : ℝ)) ^ 5 + 72 * (n : ℝ) ^ 2 := by
  rw [cycleGraph_polynomial]
  simp only [A, B, C, U, V, W, D, classSize, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub hn,
    sum_const, prod_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

noncomputable def witnessExcess (n : ℕ) : ℝ := 1 / (4 * (3 * (n : ℝ)) ^ 3)

lemma witnessExcess_pos (n : ℕ) (hn : 1 ≤ n) : 0 < witnessExcess n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  unfold witnessExcess
  positivity

lemma classSize_polynomial_density (n : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) :
    (cycleGraph σ).polynomial (fun v => (classSize n v : ℝ)) =
      (1 + witnessExcess n) * ((30 * (n : ℝ)) / 5) ^ 5 := by
  rw [classSize_polynomial n hn σ]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold witnessExcess
  field_simp
  ring

end Erdos1075
