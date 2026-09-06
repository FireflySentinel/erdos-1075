import Erdos1075.Witness
import Erdos1075.Suspension

namespace Erdos1075

open Finset CycleVertex

def liftedClassSize (n q : ℕ) : CycleVertex n ⊕ Fin q → ℕ :=
  Sum.elim (fun v => 16 * classSize n v) (fun _ => 224 * n)

lemma liftedClassSize_sum (n q : ℕ) (hn : 1 ≤ n) :
    (∑ v, liftedClassSize n q v) = (16 + q) * (224 * n) := by
  simp only [liftedClassSize, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, ← mul_sum,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, classSize_sum n hn]
  ring

lemma liftedClassSize_polynomial (n q : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) :
    ((cycleGraph σ).suspension q).polynomial (fun v => (liftedClassSize n q v : ℝ)) =
      (1 + witnessExcess n) * (224 * (n : ℝ)) ^ (16 + q) := by
  rw [UniformHypergraph.suspension_polynomial]
  simp only [liftedClassSize, Sum.elim_inl, Sum.elim_inr, Nat.cast_mul, Nat.cast_ofNat]
  rw [UniformHypergraph.polynomial_scale, classSize_polynomial_density n hn σ]
  simp only [prod_const, card_univ, Fintype.card_fin, pow_add]
  ring

lemma liftedClassSize_density (n q : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n)) :
    ((cycleGraph σ).suspension q).polynomial (fun v => (liftedClassSize n q v : ℝ)) =
      (1 + witnessExcess n) * (((∑ v, liftedClassSize n q v : ℕ) : ℝ) / (16 + q : ℕ)) ^ (16 + q) := by
  rw [liftedClassSize_sum n q hn, liftedClassSize_polynomial n q hn σ]
  congr 2
  push_cast
  field_simp

end Erdos1075
