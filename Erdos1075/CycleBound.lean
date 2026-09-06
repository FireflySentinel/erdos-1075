import Erdos1075.Construction
import Erdos1075.Derivative
import Mathlib.Logic.Equiv.Fin.Rotate

namespace Erdos1075

open Finset CycleVertex Fin.NatCast

lemma sum_update_real {V : Type*} [DecidableEq V] [Fintype V] (x : V → ℝ) (v : V) (c : ℝ) :
    (∑ w, Function.update x v c w) = (∑ w, x w) - x v + c := by
  rw [sum_update_of_mem (mem_univ v), sdiff_singleton_eq_erase, sum_erase_eq_sub (mem_univ v)]
  ring

lemma sum_range_rotate {n : ℕ} [NeZero n] (k : Fin n) (f : Fin n → ℝ) :
    (∑ i ∈ range n, f ((i : Fin n) + k)) = ∑ i, f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  simpa using Equiv.sum_comp (finCycle k) f

/-- A zero `A`-weight opens the cycle; rotation identifies it with a finite path. -/
lemma cycle_zero_bound {n : ℕ} [NeZero n] (x : CycleVertex n → ℝ) (k : Fin n)
    (hx : ∀ v, 0 ≤ x v) (hmass : (∑ v, x v) = 1) (hk : x (A k) = 0) :
    (cycleGraph (finRotate n)).polynomial x ≤ baseDensity := by
  let a : ℕ → ℝ := fun i => x (A ((i : Fin n) + k))
  let b : ℕ → ℝ := fun i => x (B ((i : Fin n) + k))
  have hasum : (∑ i ∈ range n, a i) = ∑ i, x (A i) := sum_range_rotate k (fun i => x (A i))
  have hbsum : (∑ i ∈ range n, b i) = ∑ i, x (B i) := sum_range_rotate k (fun i => x (B i))
  have hnext (i : ℕ) : ((i + 1 : ℕ) : Fin n) + k = finRotate n ((i : Fin n) + k) := by
    simp [finRotate_apply, Nat.cast_add, add_assoc, add_comm]
  have hp1 : cubicForm n a b (x C) (∑ i, x (D i)) =
      ∑ i, x (A i) * (x (B i) + x C) * ((∑ j, x (B j)) - x (B i) + (∑ j, x (D j))) := by
    unfold cubicForm
    rw [hbsum]
    exact sum_range_rotate k (fun i => x (A i) * (x (B i) + x C) * ((∑ j, x (B j)) - x (B i) + (∑ j, x (D j))))
  have hp2 : shiftedCubic n a b (x C) (∑ i, x (D i)) =
      ∑ i, x (B i) * (x (A (finRotate n i)) + x C) *
        ((∑ j, x (A j)) - x (A (finRotate n i)) + (∑ j, x (D j))) := by
    unfold shiftedCubic
    rw [hasum]
    dsimp only [a, b]
    simp only [hnext]
    exact sum_range_rotate k (fun i => x (B i) * (x (A (finRotate n i)) + x C) *
      ((∑ j, x (A j)) - x (A (finRotate n i)) + (∑ j, x (D j))))
  have hpath := path_bound n a b (x C) (x U) (x V) (fun i => x (W i)) (fun i => x (D i))
    (fun i hi => hx _) (fun i hi => hx _) (hx _) (hx _) (hx _)
    (fun i => hx _) (fun i => hx _) (by simpa [a] using hk)
    (by rw [hasum, hbsum, ← sum_weights]; exact hmass)
  rw [hp1, hp2] at hpath
  simpa only [cycleGraph_polynomial] using hpath

lemma cycle_zero_bound_mass_le {n : ℕ} [NeZero n] (x : CycleVertex n → ℝ) (k : Fin n)
    (hx : ∀ v, 0 ≤ x v) (hmass : (∑ v, x v) ≤ 1) (hk : x (A k) = 0) :
    (cycleGraph (finRotate n)).polynomial x ≤ baseDensity := by
  let y := Function.update x C (x C + (1-∑ v, x v))
  have hyx : ∀ v, x v ≤ y v := by
    intro v
    by_cases hv : v = C
    · subst v
      simp only [y, Function.update_self]
      linarith
    · simp [y, Function.update_of_ne hv]
  have hy : ∀ v, 0 ≤ y v := fun v => (hx v).trans (hyx v)
  have hymass : (∑ v, y v) = 1 := by
    rw [show (∑ v, y v) = (∑ v, x v) - x C + (x C + (1-∑ v, x v)) by
      exact sum_update_real x C _]
    ring
  have hyk : y (A k) = 0 := by simpa [y, A, C] using hk
  exact ((cycleGraph (finRotate n)).polynomial_mono hx hyx).trans (cycle_zero_bound y k hy hymass hyk)

/-- The manuscript's uniform upper bound for the cyclic templates. -/
theorem cycle_upper_bound {n : ℕ} [NeZero n] (x : CycleVertex n → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hmass : (∑ v, x v) = 1) :
    (cycleGraph (finRotate n)).polynomial x ≤ baseDensity + 1 / ((5 : ℕ).factorial * (n : ℝ)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hAsum : (∑ i, x (A i)) ≤ 1 := by
    rw [← hmass]
    calc
      (∑ i, x (A i)) = ∑ v ∈ univ.image A, x v := by
        rw [sum_image (fun i hi j hj h => by simpa [A] using h)]
      _ ≤ ∑ v, x v := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v hv hnot => hx v)
  have hex : ∃ k : Fin n, x (A k) ≤ 1 / n := by
    by_contra! h
    have hsum := sum_lt_sum_of_nonempty (s := (univ : Finset (Fin n))) univ_nonempty
      (fun i hi => h i)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hn1 : (n : ℝ) * (1 / n) = 1 := by field_simp
    rw [hn1] at hsum
    linarith
  obtain ⟨k, hk⟩ := hex
  let y := Function.update x (A k) 0
  have hy : ∀ v, 0 ≤ y v := by
    intro v
    simp only [y, Function.update_apply]
    split_ifs
    · norm_num
    · exact hx v
  have hymass : (∑ v, y v) ≤ 1 := by
    rw [show (∑ v, y v) = (∑ v, x v) - x (A k) + 0 by exact sum_update_real x (A k) 0]
    linarith [hx (A k)]
  have hybound := cycle_zero_bound_mass_le y k hy hymass (by simp [y])
  have hdel := (cycleGraph (finRotate n)).polynomial_zeroAt_bound (r := 5) (A k) x hx hmass.le
  have hlast : x (A k) / (5 : ℕ).factorial ≤ 1 / ((5 : ℕ).factorial * (n : ℝ)) := by
    calc
      x (A k) / (5 : ℕ).factorial ≤ (1 / n) / (5 : ℕ).factorial := div_le_div_of_nonneg_right hk (by positivity)
      _ = _ := by ring
  exact hdel.trans (add_le_add hybound hlast)

end Erdos1075
