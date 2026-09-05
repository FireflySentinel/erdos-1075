import Erdos1075.Scalar
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdos1075

open Finset

/-- A finite simple uniform hypergraph: edges are sets, with no multiplicities. -/
structure UniformHypergraph (V : Type*) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

namespace UniformHypergraph

variable {V : Type*} [DecidableEq V] {r : ℕ}

noncomputable def polynomial (H : UniformHypergraph V r) (x : V → ℝ) : ℝ :=
  ∑ e ∈ H.edges, ∏ v ∈ e, x v

def inducedEdges (H : UniformHypergraph V r) (S : Finset V) : Finset (Finset V) :=
  H.edges.filter (fun e => e ⊆ S)

lemma polynomial_nonneg (H : UniformHypergraph V r) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) : 0 ≤ H.polynomial x := by
  exact sum_nonneg fun e he => prod_nonneg fun v hv => hx v

lemma polynomial_scale (H : UniformHypergraph V r) (x : V → ℝ) (c : ℝ) :
    H.polynomial (fun v => c*x v) = c^r*H.polynomial x := by
  unfold polynomial
  rw [mul_sum]
  apply sum_congr rfl
  intro e he
  rw [prod_mul_distrib, prod_const, H.uniform e he]

lemma polynomial_mono (H : UniformHypergraph V r) {x y : V → ℝ}
    (hx : ∀ v, 0 ≤ x v) (hxy : ∀ v, x v ≤ y v) :
    H.polynomial x ≤ H.polynomial y := by
  exact sum_le_sum fun e he => prod_le_prod (fun v hv => hx v) (fun v hv => hxy v)

def map {W : Type*} [DecidableEq W] (H : UniformHypergraph V r) (f : V ↪ W) :
    UniformHypergraph W r where
  edges := H.edges.image (fun e => e.image f)
  uniform := by
    intro e he
    obtain ⟨e',he',rfl⟩ := mem_image.mp he
    rw [card_image_of_injective _ f.injective]
    exact H.uniform e' he'

lemma map_polynomial {W : Type*} [DecidableEq W] (H : UniformHypergraph V r)
    (f : V ↪ W) (x : W → ℝ) :
    (H.map f).polynomial x = H.polynomial (fun v => x (f v)) := by
  unfold polynomial map
  rw [sum_image (fun e he e' he' h => image_injective f.injective h)]
  apply sum_congr rfl
  intro e he
  rw [prod_image (fun v hv w hw h => f.injective h)]

/-- An ordering of an edge, used only to inject its monomial into a power of a sum. -/
noncomputable def edgeEnum (H : UniformHypergraph V r) (e : H.edges) : Fin r → V :=
  fun i => ((Fintype.equivFinOfCardEq (α := e.val) (by simpa using H.uniform e.val e.property)).symm i).val

lemma edgeEnum_injective (H : UniformHypergraph V r) (e : H.edges) :
    Function.Injective (H.edgeEnum e) := by
  exact Subtype.val_injective.comp (Equiv.injective _)

lemma edgeEnum_image (H : UniformHypergraph V r) (e : H.edges) :
    univ.image (H.edgeEnum e) = e.val := by
  ext v
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Fintype.equivFinOfCardEq (α := e.val) (by simpa using H.uniform e.val e.property)).symm i).property
  · intro hv
    let j : e.val := ⟨v,hv⟩
    refine ⟨(Fintype.equivFinOfCardEq (α := e.val) (by simpa using H.uniform e.val e.property)) j, ?_⟩
    simp [edgeEnum, j]

lemma edgeEnum_map_injective (H : UniformHypergraph V r) :
    Function.Injective H.edgeEnum := by
  intro e f h
  apply Subtype.ext
  rw [← H.edgeEnum_image e, ← H.edgeEnum_image f, h]

lemma prod_edgeEnum (H : UniformHypergraph V r) (e : H.edges) (x : V → ℝ) :
    (∏ i, x (H.edgeEnum e i)) = ∏ v ∈ e.val, x v := by
  rw [← H.edgeEnum_image e, prod_image]
  exact fun i hi j hj hij => H.edgeEnum_injective e hij

variable [Fintype V]

/-- A uniform monomial sum is bounded by the corresponding power of total mass. -/
lemma polynomial_le_mass_pow (H : UniformHypergraph V r) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) : H.polynomial x ≤ (∑ v, x v)^r := by
  classical
  rw [Fintype.sum_pow]
  calc
    H.polynomial x = ∑ e : H.edges, ∏ i, x (H.edgeEnum e i) := by
      simp only [H.prod_edgeEnum]
      exact (sum_attach H.edges (fun e => ∏ v ∈ e, x v)).symm
    _ ≤ ∑ f : Fin r → V, ∏ i, x (f i) := by
      rw [← sum_image (s := univ) (g := H.edgeEnum) (f := fun f : Fin r → V => ∏ i, x (f i))
        (fun e he f hf h => H.edgeEnum_map_injective h)]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun f hf hnot => prod_nonneg fun i hi => hx (f i))

end UniformHypergraph

end Erdos1075
