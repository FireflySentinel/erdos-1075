import Erdos1075.Hypergraph

namespace Erdos1075.UniformHypergraph

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V] {r : ℕ}

omit [Fintype V] in
lemma polynomial_zero (H : UniformHypergraph V r) (hr : 0 < r) : H.polynomial (fun _ => 0) = 0 := by
  unfold polynomial
  apply sum_eq_zero
  intro e he
  rw [prod_const,H.uniform e he,zero_pow (ne_of_gt hr)]

lemma bound_homogeneous (H : UniformHypergraph V r) (hr : 0 < r) (α : ℝ)
    (hbound : ∀ x : V → ℝ,(∀ v,0 ≤ x v) → (∑ v,x v) = 1 → H.polynomial x ≤ α)
    (x : V → ℝ) (hx : ∀ v,0 ≤ x v) : H.polynomial x ≤ α*(∑ v,x v)^r := by
  let t := ∑ v,x v
  have ht : 0 ≤ t := sum_nonneg fun v hv => hx v
  rcases ht.eq_or_lt with ht0 | htpos
  · have hz : x = fun _ => 0 := by
      funext v
      have h := (sum_eq_zero_iff_of_nonneg (fun v hv => hx v)).mp ht0.symm
      exact h v (mem_univ v)
    rw [hz,H.polynomial_zero hr]
    simp [zero_pow (ne_of_gt hr)]
  · have htne : t ≠ 0 := ne_of_gt htpos
    have h := hbound (fun v => (1/t)*x v) (fun v => mul_nonneg (by positivity) (hx v))
      (by rw [← mul_sum]; change (1/t)*t = 1; field_simp)
    rw [H.polynomial_scale] at h
    have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg ht r)
    have hcancel : t^r*((1/t)^r*H.polynomial x) = H.polynomial x := by
      rw [← mul_assoc,← mul_pow]
      field_simp
      simp
    rw [hcancel] at hmul
    simpa only [mul_comm] using hmul

def suspensionEdge (q : ℕ) (e : Finset V) : Finset (V ⊕ Fin q) :=
  e.image Sum.inl ∪ univ.image Sum.inr

omit [Fintype V] in
lemma suspensionEdge_injective (q : ℕ) : Function.Injective (suspensionEdge (V := V) q) := by
  intro e f h
  ext v
  have hv := congrArg (fun s => (Sum.inl v : V ⊕ Fin q) ∈ s) h
  simpa [suspensionEdge] using hv

omit [Fintype V] in
lemma suspension_disjoint (q : ℕ) (e : Finset V) :
    Disjoint (e.image (Sum.inl : V → V ⊕ Fin q)) (univ.image Sum.inr) := by
  simp [disjoint_left]

def suspension (H : UniformHypergraph V r) (q : ℕ) : UniformHypergraph (V ⊕ Fin q) (r+q) where
  edges := H.edges.image (suspensionEdge q)
  uniform := by
    intro e he
    obtain ⟨e',he',rfl⟩ := mem_image.mp he
    rw [suspensionEdge,card_union_of_disjoint (suspension_disjoint q e')]
    rw [card_image_of_injective _ Sum.inl_injective,card_image_of_injective _ Sum.inr_injective]
    simp [H.uniform e' he']

omit [Fintype V] in
lemma suspension_polynomial (H : UniformHypergraph V r) (q : ℕ) (x : V ⊕ Fin q → ℝ) :
    (H.suspension q).polynomial x = H.polynomial (fun v => x (Sum.inl v))*(∏ i,x (Sum.inr i)) := by
  unfold polynomial suspension
  rw [sum_image (fun e he f hf h => suspensionEdge_injective q h),sum_mul]
  apply sum_congr rfl
  intro e he
  rw [suspensionEdge,prod_union (suspension_disjoint q e)]
  rw [prod_image (fun v hv w hw h => Sum.inl_injective h),prod_image (fun v hv w hw h => Sum.inr_injective h)]

/-- The lifting factor from the manuscript, proved directly by finite AM–GM. -/
theorem suspension_bound (H : UniformHypergraph V r) (hr : 0 < r) (q : ℕ) (α : ℝ)
    (hα : 0 ≤ α)
    (hbound : ∀ x : V → ℝ,(∀ v,0 ≤ x v) → (∑ v,x v) = 1 → H.polynomial x ≤ α)
    (x : V ⊕ Fin q → ℝ) (hx : ∀ v,0 ≤ x v) (hmass : (∑ v,x v) = 1) :
    (H.suspension q).polynomial x ≤ α*(r:ℝ)^r/((r+q:ℕ):ℝ)^(r+q) := by
  rw [suspension_polynomial]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmass' : (∑ v,x (Sum.inl v)) + (∑ i,x (Sum.inr i)) = 1 := by
    simpa only [Fintype.sum_sum_type] using hmass
  have hbottom := H.bound_homogeneous hr α hbound (fun v => x (Sum.inl v)) (fun v => hx _)
  have ht : 0 ≤ ∑ v,x (Sum.inl v) := sum_nonneg fun v hv => hx _
  have hu : 0 ≤ ∑ i,x (Sum.inr i) := sum_nonneg fun i hi => hx _
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [Finset.univ_eq_empty,prod_empty,sum_empty,add_zero] at *
    rw [hmass',one_pow,mul_one] at hbottom
    simpa [div_self (ne_of_gt (pow_pos hrR r))] using hbottom
  · have : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hp := prod_le_mean_pow univ (fun i => x (Sum.inr i)) univ_nonempty (fun i hi => hx _)
    simp only [card_univ,Fintype.card_fin] at hp
    have ham := pow_mul_pow_le_weighted_mean ((∑ v,x (Sum.inl v))/(r:ℝ))
      ((∑ i,x (Sum.inr i))/(q:ℝ)) r q (by positivity) (by positivity) (by omega)
    have hmean : ((r:ℝ)*((∑ v,x (Sum.inl v))/(r:ℝ)) +
      (q:ℝ)*((∑ i,x (Sum.inr i))/(q:ℝ)))/((r:ℝ)+q) = 1/((r:ℝ)+q) := by
      field_simp
      linarith
    rw [hmean] at ham
    calc
      H.polynomial (fun v => x (Sum.inl v))*(∏ i,x (Sum.inr i)) ≤
          (α*(∑ v,x (Sum.inl v))^r)*(((∑ i,x (Sum.inr i))/(q:ℝ))^q) :=
        mul_le_mul hbottom hp (prod_nonneg fun i hi => hx _) (by positivity)
      _ = α*(r:ℝ)^r * (((∑ v,x (Sum.inl v))/(r:ℝ))^r * ((∑ i,x (Sum.inr i))/(q:ℝ))^q) := by
        simp only [div_pow]
        field_simp

      _ ≤ α*(r:ℝ)^r*(1/((r:ℝ)+q))^(r+q) := mul_le_mul_of_nonneg_left ham (by positivity)
      _ = _ := by rw [Nat.cast_add,div_pow,one_pow]; ring

end Erdos1075.UniformHypergraph
