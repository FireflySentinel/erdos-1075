import Erdos1075.Cubic

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

noncomputable def pathShape (h : ℝ) : ℝ := (4 * h / 3) ^ 12 * (4 * (1 - h)) ^ 4

lemma pathShape_nonneg (h : ℝ) : 0 ≤ pathShape h := by
  unfold pathShape
  positivity

lemma pathShape_le_one {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) : pathShape h ≤ 1 := by
  have hmean := pow_mul_pow_le_weighted_mean (4 * h / 3) (4 * (1 - h)) 12 4
    (by positivity) (by positivity) (by norm_num)
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hmean
  have heq : ((12 : ℝ) * (4 * h / 3) + 4 * (4 * (1 - h))) / 16 = 1 := by ring
  rw [heq, one_pow] at hmean
  exact hmean

lemma pathShape_le_self {h : ℝ} (h0 : 0 ≤ h) (hhalf : h ≤ 1 / 2) :
    pathShape h ≤ h := by
  have h1 : h ≤ 1 := by linarith
  have hprod0 : 0 ≤ h * (1 - h) := mul_nonneg h0 (sub_nonneg.mpr h1)
  have hprod : h * (1 - h) ≤ 1 / 4 := by nlinarith [sq_nonneg (h - 1 / 2)]
  have h7 : h ^ 7 ≤ (1 / 2 : ℝ) ^ 7 := by gcongr
  have h4 : (h * (1 - h)) ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := by gcongr
  have hmul : h ^ 7 * (h * (1 - h)) ^ 4 ≤ (1 / 2 : ℝ) ^ 7 * (1 / 4 : ℝ) ^ 4 := by
    exact mul_le_mul h7 h4 (by positivity) (by positivity)
  calc
    pathShape h = h * ((4 / 3 : ℝ) ^ 12 * 4 ^ 4 *
        (h ^ 7 * (h * (1 - h)) ^ 4)) := by unfold pathShape; ring
    _ ≤ h * ((4 / 3 : ℝ) ^ 12 * 4 ^ 4 * ((1 / 2 : ℝ) ^ 7 * (1 / 4 : ℝ) ^ 4)) := by
      gcongr
    _ ≤ h * 1 := by gcongr; norm_num
    _ = h := mul_one h

lemma pathShape_large_h {h : ℝ} (hhalf : 1 / 2 ≤ h) (h1 : h ≤ 1) :
    4 * (1 - h) ^ 16 ≤ 9 / 400 * pathShape h := by
  have h0 : 0 ≤ h := by linarith
  have hy : 0 ≤ 1 - h := sub_nonneg.mpr h1
  have hyh : 1 - h ≤ h := by linarith
  have hp : (1 - h) ^ 12 ≤ h ^ 12 := by gcongr
  calc
    4 * (1 - h) ^ 16 = 4 * (1 - h) ^ 12 * (1 - h) ^ 4 := by ring
    _ ≤ 4 * h ^ 12 * (1 - h) ^ 4 := by gcongr
    _ ≤ ((9 / 400 : ℝ) * (4 / 3) ^ 12 * 4 ^ 4) * h ^ 12 * (1 - h) ^ 4 := by
      gcongr
      norm_num
    _ = 9 / 400 * pathShape h := by unfold pathShape; ring

/-- The final scalar inequality in the open-path Lagrangian argument. -/
theorem path_scalar_bound {h z : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 4) :
    pathShape h + z * (4 * (1 - h) ^ 16 - 9 / 400 * pathShape h) ≤ 1 := by
  by_cases hh : 1 / 2 ≤ h
  · have hbr := pathShape_large_h hh h1
    have hmul := mul_nonpos_of_nonneg_of_nonpos hz0 (sub_nonpos.mpr hbr)
    linarith only [hmul, pathShape_le_one h0 h1]
  · have hf := pathShape_le_self h0 (le_of_lt (lt_of_not_ge hh))
    have hy : 0 ≤ 1 - h := sub_nonneg.mpr h1
    have hypow : (1 - h) ^ 16 ≤ 1 - h := by
      calc
        (1 - h) ^ 16 = (1 - h) * (1 - h) ^ 15 := by ring
        _ ≤ (1 - h) * 1 ^ 15 := by gcongr; linarith
        _ = 1 - h := by ring
    have hm := mul_le_mul_of_nonneg_right hz1 (show 0 ≤ 4 * (1 - h) ^ 16 by positivity)
    have hn : 0 ≤ z * (9 / 400 * pathShape h) := by
      exact mul_nonneg hz0 (mul_nonneg (by norm_num) (pathShape_nonneg h))
    nlinarith only [hf, hypow, hm, hn]

end Erdos1075
