import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace Erdos1075

open Finset

/-- AM–GM in a form with natural exponents only. -/
lemma pow_mul_pow_le_weighted_mean (x y : ℝ) (m n : ℕ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hmn : 0 < m + n) :
    x ^ m * y ^ n ≤ (((m : ℝ) * x + (n : ℝ) * y) / (m + n)) ^ (m + n) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmn' : (0 : ℝ) < (m : ℝ) + n := by exact_mod_cast hmn
  have h := Real.geom_mean_le_arith_mean (univ : Finset (Fin 2))
    ![(m : ℝ), (n : ℝ)] ![x, y]
    (by intro i hi; fin_cases i <;> simp [hm, hn])
    (by simpa using hmn')
    (by intro i hi; fin_cases i <;> simp [hx, hy])
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.rpow_natCast] at h
  have h' := (Real.rpow_inv_le_iff_of_pos (show 0 ≤ x ^ m * y ^ n by positivity)
    (show 0 ≤ ((m : ℝ) * x + (n : ℝ) * y) / ((m : ℝ) + n) by positivity) hmn').mp h
  simpa only [← Nat.cast_add, Real.rpow_natCast] using h'

/-- The usual finite AM–GM inequality, including zero entries. -/
lemma prod_le_mean_pow {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hs : s.Nonempty) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∏ i ∈ s, x i) ≤ ((∑ i ∈ s, x i) / s.card) ^ s.card := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := Real.geom_mean_le_arith_mean s (fun _ => 1) x
    (by intro i hi; norm_num) (by simpa using hcard) hx
  simp only [Real.rpow_one, one_mul, sum_const, nsmul_eq_mul, mul_one] at h
  have h' := (Real.rpow_inv_le_iff_of_pos (prod_nonneg hx)
    (div_nonneg (sum_nonneg hx) hcard.le) hcard).mp h
  simpa only [Real.rpow_natCast] using h'

noncomputable def pathShape (h : ℝ) : ℝ := (5 * h) * (5 * (1 - h) / 4) ^ 4

lemma pathShape_nonneg {h : ℝ} (h0 : 0 ≤ h) : 0 ≤ pathShape h := by
  unfold pathShape
  positivity

lemma pathShape_le_one {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) : pathShape h ≤ 1 := by
  have hmean := pow_mul_pow_le_weighted_mean (5 * h) (5 * (1 - h) / 4) 1 4
    (by positivity) (by positivity) (by norm_num)
  norm_num only [Nat.cast_ofNat, Nat.cast_one, Nat.reduceAdd, pow_one] at hmean
  have heq : ((1 : ℝ) * (5 * h) + 4 * (5 * (1 - h) / 4)) / 5 = 1 := by ring
  rw [heq, one_pow] at hmean
  exact hmean

/-- The binomial expansion controls the scalar estimate at uniformity five. -/
lemma scalar_polynomial_nonneg (h t : ℝ) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    0 ≤ (h + t) ^ 5 - t ^ 5 - 8125 / 2048 * h * t ^ 4 := by
  calc
    0 ≤ h ^ 5 + 5 * h ^ 4 * t + 10 * h ^ 3 * t ^ 2 + 10 * h ^ 2 * t ^ 3 +
        2115 / 2048 * h * t ^ 4 := by positivity
    _ = (h + t) ^ 5 - t ^ 5 - 8125 / 2048 * h * t ^ 4 := by ring

lemma path_endpoint_bound {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    pathShape h * (1 - 27 / 40) + (1 - h) ^ 5 ≤ 1 := by
  have hp := scalar_polynomial_nonneg h (1 - h) h0 (sub_nonneg.mpr h1)
  have hsum : h + (1 - h) = 1 := by ring
  rw [hsum, one_pow] at hp
  unfold pathShape
  nlinarith only [hp]

/-- The final scalar inequality in the open-path Lagrangian argument. -/
theorem path_scalar_bound {h z : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 4) :
    pathShape h + z * (4 * (1 - h) ^ 5 - 27 / 10 * pathShape h) ≤ 1 := by
  have hfirst := mul_le_mul_of_nonneg_left (pathShape_le_one h0 h1)
    (show 0 ≤ 1 - 4 * z by linarith)
  have hsecond := mul_le_mul_of_nonneg_left (path_endpoint_bound h0 h1)
    (show 0 ≤ 4 * z by positivity)
  nlinarith only [hfirst, hsecond]

end Erdos1075
