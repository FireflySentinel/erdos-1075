import Mathlib.Tactic

namespace Erdos1075

open Finset

noncomputable def pathPotential (x : ℝ) : ℝ :=
  if x ≤ 1 then x - x ^ 2 / 2 else 1 / 2

@[simp] lemma pathPotential_zero : pathPotential 0 = 0 := by
  norm_num [pathPotential]

lemma pathPotential_step {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pathPotential x - pathPotential y ≤ x * (1 - y) ^ 2 := by
  by_cases hy1 : y ≤ 1
  · by_cases hx1 : x ≤ 1
    · simp only [pathPotential, if_pos hx1, if_pos hy1]
      have h := add_nonneg (sq_nonneg (x - 2 * y + y ^ 2))
        (mul_nonneg (mul_nonneg hy (sq_nonneg (1 - y))) (show 0 ≤ 2 - y by linarith))
      nlinarith only [h]
    · simp only [pathPotential, if_neg hx1, if_pos hy1]
      have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ x by linarith) (sq_nonneg (1 - y))
      nlinarith only [h, sq_nonneg (1 - y)]
  · have hp : pathPotential x ≤ 1 / 2 := by
      unfold pathPotential
      split_ifs <;> nlinarith [sq_nonneg (1 - x)]
    rw [show pathPotential y = 1 / 2 by simp [pathPotential, hy1]]
    have h := mul_nonneg hx (sq_nonneg (1 - y))
    linarith

lemma pathPotential_large {x : ℝ} (hx : 1 / 3 ≤ x) :
    2 / 9 ≤ pathPotential x := by
  unfold pathPotential
  split_ifs with hx1
  · nlinarith [mul_nonneg (show 0 ≤ x - 1 / 3 by linarith)
      (show 0 ≤ 5 / 3 - x by linarith)]
  · norm_num

lemma scaled_potential_step {a b α β c M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 < α) (hβ : 0 < β)
    (hM : 0 ≤ M) (hMc : M ≤ c * α * β ^ 2) :
    M * (pathPotential (a / α) - pathPotential (b / β)) ≤ c * a * (b - β) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (pathPotential_step (div_nonneg ha hα.le) (div_nonneg hb hβ.le)) hM
  have hcost : 0 ≤ (a / α) * (1 - b / β) ^ 2 := by positivity
  have h' := mul_le_mul_of_nonneg_right hMc hcost
  have hid : c * α * β ^ 2 * ((a / α) * (1 - b / β) ^ 2) = c * a * (b - β) ^ 2 := by
    field_simp
    ring
  rw [hid] at h'
  exact h.trans h'

/-- Summing nonnegative step costs controls the potential at every point of a path. -/
lemma potential_le_path_cost (L : ℕ) (p q e f : ℕ → ℝ)
    (he : ∀ i < L, 0 ≤ e i) (hf : ∀ i < L, 0 ≤ f i)
    (hp : ∀ i < L, p i - q i ≤ e i)
    (hq : ∀ i < L, q i - p (i + 1) ≤ f i) :
    ∀ i < L,
      p i - p L ≤ ∑ j ∈ range L, (e j + f j) ∧
      q i - p L ≤ ∑ j ∈ range L, (e j + f j) := by
  induction L with
  | zero => intro i hi; omega
  | succ L ih =>
    have heL := he L (by omega)
    have hfL := hf L (by omega)
    have hpL := hp L (by omega)
    have hqL := hq L (by omega)
    have hsum : 0 ≤ ∑ j ∈ range L, (e j + f j) :=
      sum_nonneg fun j hj => add_nonneg (he j (by have := mem_range.mp hj; omega))
        (hf j (by have := mem_range.mp hj; omega))
    intro i hi
    rw [sum_range_succ]
    by_cases hiL : i < L
    · have h := ih (fun j hj => he j (by omega)) (fun j hj => hf j (by omega))
        (fun j hj => hp j (by omega)) (fun j hj => hq j (by omega)) i hiL
      constructor <;> linarith [h.1, h.2]
    · have hi' : i = L := by omega
      subst i
      constructor <;> linarith

lemma cubic_absorption (S m : ℝ) (hS : 0 ≤ S) (hm : 0 ≤ m) :
    (S + m) ^ 3 / 10 ≤ (S + m) * S ^ 2 / 3 + 2 / 9 * m ^ 3 := by
  have h : 0 ≤ 21 * (S - 3 * m / 5) ^ 2 * (S + 6 * m / 5) +
      3 * m * (S - 18 * m / 25) ^ 2 + 233 / 625 * m ^ 3 := by positivity
  nlinarith only [h]

end Erdos1075
