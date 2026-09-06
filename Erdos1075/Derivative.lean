import Erdos1075.Hypergraph
import Mathlib.Data.Fintype.Perm

namespace Erdos1075.UniformHypergraph

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ}

/-- Count all orderings of each edge, giving the factorial in the derivative bound. -/
lemma factorial_mul_polynomial_le_mass_pow (H : UniformHypergraph V r) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) : (r.factorial : ℝ) * H.polynomial x ≤ (∑ v, x v) ^ r := by
  classical
  let F : H.edges × Equiv.Perm (Fin r) → (Fin r → V) := fun p i => H.edgeEnum p.1 (p.2 i)
  have hFimage (e : H.edges) (σ : Equiv.Perm (Fin r)) : univ.image (F (e, σ)) = e.val := by
    change univ.image ((H.edgeEnum e) ∘ σ) = e.val
    rw [← image_image, image_univ_of_surjective σ.surjective, H.edgeEnum_image]
  have hFinj : Function.Injective F := by
    rintro ⟨e, σ⟩ ⟨f, τ⟩ h
    have hef : e = f := Subtype.ext (by rw [← hFimage e σ, ← hFimage f τ, h])
    subst f
    have hστ : σ = τ := by
      apply Equiv.ext
      intro i
      exact H.edgeEnum_injective e (congrFun h i)
    subst τ
    rfl
  have hprod (e : H.edges) (σ : Equiv.Perm (Fin r)) :
      (∏ i, x (F (e, σ) i)) = ∏ v ∈ e.val, x v := by
    change (∏ i, x (H.edgeEnum e (σ i))) = _
    exact (Equiv.prod_comp σ (fun i => x (H.edgeEnum e i))).trans (H.prod_edgeEnum e x)
  calc
    (r.factorial : ℝ) * H.polynomial x = ∑ p : H.edges × Equiv.Perm (Fin r), ∏ i, x (F p i) := by
      rw [Fintype.sum_prod_type]
      simp only [hprod, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul, ← mul_sum]
      congr 1
      exact (sum_attach H.edges (fun e => ∏ v ∈ e, x v)).symm
    _ ≤ ∑ f : Fin r → V, ∏ i, x (f i) := by
      rw [← sum_image (s := univ) (g := F) (f := fun f : Fin r → V => ∏ i, x (f i))
        (fun p hp q hq h => hFinj h)]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun f hf hnot => prod_nonneg fun i hi => hx (f i))
    _ = (∑ v, x v) ^ r := (Fintype.sum_pow x r).symm

lemma polynomial_le_mass_pow_div_factorial (H : UniformHypergraph V r) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) : H.polynomial x ≤ (∑ v, x v) ^ r / r.factorial := by
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  apply (le_div_iff₀ hf).mpr
  simpa only [mul_comm] using H.factorial_mul_polynomial_le_mass_pow x hx

def link (H : UniformHypergraph V (r + 1)) (v : V) : UniformHypergraph V r where
  edges := (H.edges.filter (fun e => v ∈ e)).image (fun e => e.erase v)
  uniform := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    obtain ⟨heH, hev⟩ := mem_filter.mp he'
    rw [card_erase_of_mem hev, H.uniform e' heH]
    omega

omit [Fintype V] in
lemma link_polynomial (H : UniformHypergraph V (r + 1)) (v : V) (x : V → ℝ) :
    (H.link v).polynomial x = ∑ e ∈ H.edges, if v ∈ e then ∏ w ∈ e.erase v, x w else 0 := by
  unfold polynomial link
  rw [sum_image]
  · rw [sum_filter]
  · intro e he f hf h
    have he' := (mem_filter.mp he).2
    have hf' := (mem_filter.mp hf).2
    rw [← insert_erase he', ← insert_erase hf']
    exact congrArg (insert v) h

omit [Fintype V] in
lemma polynomial_zeroAt (H : UniformHypergraph V (r + 1)) (v : V) (x : V → ℝ) :
    H.polynomial x = H.polynomial (Function.update x v 0) + x v * (H.link v).polynomial x := by
  rw [link_polynomial]
  unfold polynomial
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro e he
  by_cases hv : v ∈ e
  · rw [if_pos hv, prod_update_of_mem hv]
    simp only [zero_mul, zero_add]
    exact (mul_prod_erase e x hv).symm
  · rw [if_neg hv, prod_update_of_notMem hv]
    ring

/-- Removing one vertex loses at most its weight divided by `(r-1)!` at mass at most one. -/
lemma polynomial_zeroAt_bound (H : UniformHypergraph V (r + 1)) (v : V) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hmass : (∑ v, x v) ≤ 1) :
    H.polynomial x ≤ H.polynomial (Function.update x v 0) + x v / r.factorial := by
  rw [H.polynomial_zeroAt v x]
  apply add_le_add le_rfl
  have hlink := (H.link v).polynomial_le_mass_pow_div_factorial x hx
  have hpow : (∑ v, x v) ^ r ≤ 1 := by
    calc
      (∑ v, x v) ^ r ≤ (1 : ℝ) ^ r := by gcongr; exact sum_nonneg fun v hv => hx v
      _ = 1 := one_pow _
  have hlink' : (H.link v).polynomial x ≤ 1 / r.factorial :=
    hlink.trans (div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _))
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlink' (hx v)

end Erdos1075.UniformHypergraph
