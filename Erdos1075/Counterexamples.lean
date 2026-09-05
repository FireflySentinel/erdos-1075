import Erdos1075.Blowup
import Erdos1075.Suspension

namespace Erdos1075.UniformHypergraph

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ}

lemma blowup_bound (H : UniformHypergraph V r) (m : V → ℕ) (α : ℝ)
    (hbound : ∀ x : V → ℝ,(∀ v,0 ≤ x v) → (∑ v,x v) = 1 → H.polynomial x ≤ α)
    (x : BlowupVertex m → ℝ) (hx : ∀ v,0 ≤ x v) (hmass : (∑ v,x v) = 1) :
    (H.blowup m).polynomial x ≤ α := by
  rw [blowup_polynomial]
  apply hbound
  · intro v
    exact sum_nonneg fun i hi => hx _
  · rw [← Fintype.sum_sigma (f := x)]
    exact hmass

lemma map_equiv_bound {W : Type*} [DecidableEq W] [Fintype W]
    (H : UniformHypergraph V r) (e : V ≃ W) (α : ℝ)
    (hbound : ∀ x : V → ℝ,(∀ v,0 ≤ x v) → (∑ v,x v) = 1 → H.polynomial x ≤ α)
    (x : W → ℝ) (hx : ∀ v,0 ≤ x v) (hmass : (∑ v,x v) = 1) :
    (H.map e.toEmbedding).polynomial x ≤ α := by
  rw [map_polynomial]
  apply hbound
  · intro v
    exact hx _
  · simpa only [Equiv.coe_toEmbedding,Equiv.sum_comp] using hmass

lemma weighted_induced_bound (H : UniformHypergraph V r) (hr : 0 < r) (α : ℝ)
    (hbound : ∀ x : V → ℝ,(∀ v,0 ≤ x v) → (∑ v,x v) = 1 → H.polynomial x ≤ α)
    (S : Finset V) : ((H.inducedEdges S).card : ℝ) ≤ α*(S.card:ℝ)^r := by
  have h := H.bound_homogeneous hr α hbound (fun v => if v ∈ S then 1 else 0)
    (fun v => by split_ifs <;> norm_num)
  simpa only [polynomial_indicator,Finset.sum_boole,filter_mem_eq_inter,univ_inter] using h

/-- Rational template weights give arbitrarily large simple uniform counterexamples. -/
theorem arbitrarily_large_blowups (H : UniformHypergraph V r) (hr : 0 < r)
    (m : V → ℕ) (hm : 0 < ∑ v,m v) (ε α γ : ℝ) (hαγ : α < γ)
    (hcount : H.polynomial (fun v => (m v:ℝ)) = (1+ε)*(((∑ v,m v:ℕ):ℝ)/(r:ℝ))^r)
    (hbound : ∀ x : V → ℝ,(∀ v,0 ≤ x v) → (∑ v,x v) = 1 → H.polynomial x ≤ α)
    (N₀ : ℕ) :
    ∃ N ≥ N₀, ∃ K : UniformHypergraph (Fin N) r,
      (1+ε)*((N:ℝ)/(r:ℝ))^r ≤ (K.edges.card:ℝ) ∧
      ∀ S : Finset (Fin N), S.Nonempty → ((K.inducedEdges S).card:ℝ) < γ*(S.card:ℝ)^r := by
  classical
  let sizes : V → ℕ := fun v => (N₀+1)*m v
  let N := (N₀+1)*(∑ v,m v)
  let e : BlowupVertex sizes ≃ Fin N := Fintype.equivFinOfCardEq (by
    rw [blowup_card_vertices]
    simp only [sizes,← mul_sum]
    rfl)
  let K := (H.blowup sizes).map e.toEmbedding
  have hN : N₀ ≤ N := by
    dsimp [N]
    nlinarith
  refine ⟨N,hN,K,?_,?_⟩
  · have hKcard : (K.edges.card:ℝ) = ((N₀+1:ℕ):ℝ)^r*H.polynomial (fun v => (m v:ℝ)) := by
      calc
        (K.edges.card:ℝ) = ((H.blowup sizes).edges.card:ℝ) := by
          congr 1
          exact card_image_of_injective _ (image_injective e.injective)
        _ = H.polynomial (fun v => (sizes v:ℝ)) := blowup_card_edges H sizes
        _ = _ := by
          simp only [sizes,Nat.cast_mul]
          rw [polynomial_scale]
    rw [hKcard,hcount]
    have hNr : (N:ℝ)/(r:ℝ) = ((N₀+1:ℕ):ℝ)*(((∑ v,m v:ℕ):ℝ)/(r:ℝ)) := by
      dsimp [N]
      push_cast
      ring
    rw [hNr,mul_pow]
    exact le_of_eq (by ring)
  · have hKbound : ∀ x : Fin N → ℝ,(∀ v,0 ≤ x v) → (∑ v,x v) = 1 → K.polynomial x ≤ α :=
      (H.blowup sizes).map_equiv_bound e α (H.blowup_bound sizes α hbound)
    intro S hS
    have hSpow : (0:ℝ) < (S.card:ℝ)^r := pow_pos (by exact_mod_cast hS.card_pos) _
    exact (K.weighted_induced_bound hr α hKbound S).trans_lt (mul_lt_mul_of_pos_right hαγ hSpow)

end Erdos1075.UniformHypergraph
