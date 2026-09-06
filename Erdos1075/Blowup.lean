import Erdos1075.Hypergraph

namespace Erdos1075.UniformHypergraph

open Finset

variable {V : Type*} [DecidableEq V] {r : ℕ}

abbrev BlowupVertex (m : V → ℕ) := Σ v, Fin (m v)

abbrev BlowupChoice (H : UniformHypergraph V r) (m : V → ℕ) :=
  Σ e : H.edges, ∀ v : e.val, Fin (m v.val)

def choiceEdge (H : UniformHypergraph V r) (m : V → ℕ) (f : H.BlowupChoice m) :
    Finset (BlowupVertex m) := univ.image (fun v : f.1.val => ⟨v.val, f.2 v⟩)

lemma choice_vertex_injective (H : UniformHypergraph V r) (m : V → ℕ) (f : H.BlowupChoice m) :
    Function.Injective (fun v : f.1.val => (⟨v.val, f.2 v⟩ : BlowupVertex m)) := by
  intro v w h
  exact Subtype.ext (congrArg Sigma.fst h)

lemma choiceEdge_image (H : UniformHypergraph V r) (m : V → ℕ) (f : H.BlowupChoice m) :
    (H.choiceEdge m f).image Sigma.fst = f.1.val := by
  simp [choiceEdge, image_image, Function.comp_def]

lemma choiceEdge_injective (H : UniformHypergraph V r) (m : V → ℕ) :
    Function.Injective (H.choiceEdge m) := by
  rintro ⟨e, f⟩ ⟨e', g⟩ h
  have he : e = e' := Subtype.ext (by
    rw [← H.choiceEdge_image m ⟨e, f⟩, ← H.choiceEdge_image m ⟨e', g⟩, h])
  subst e'
  have hfg : f = g := by
    funext v
    have hv : (⟨v.val, f v⟩ : BlowupVertex m) ∈ H.choiceEdge m ⟨e, g⟩ := by
      rw [← h]
      exact mem_image.mpr ⟨v, mem_univ _, rfl⟩
    obtain ⟨w, hw, heq⟩ := mem_image.mp hv
    have hwv : w = v := Subtype.ext (congrArg Sigma.fst heq)
    subst w
    exact (Sigma.mk.inj heq).2.eq.symm
  subst g
  rfl

def blowup (H : UniformHypergraph V r) (m : V → ℕ) : UniformHypergraph (BlowupVertex m) r where
  edges := univ.image (H.choiceEdge m)
  uniform := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    rw [choiceEdge, card_image_of_injective _ (H.choice_vertex_injective m f), card_univ]
    simpa using H.uniform f.1.val f.1.property

lemma choiceEdge_prod (H : UniformHypergraph V r) (m : V → ℕ) (f : H.BlowupChoice m)
    (x : BlowupVertex m → ℝ) :
    (∏ v ∈ H.choiceEdge m f, x v) = ∏ v : f.1.val, x ⟨v.val, f.2 v⟩ := by
  rw [choiceEdge, prod_image]
  exact fun v hv w hw heq => H.choice_vertex_injective m f heq

/-- The polynomial identity for a blowup; all class sizes, including zero, are allowed. -/
theorem blowup_polynomial (H : UniformHypergraph V r) (m : V → ℕ)
    (x : BlowupVertex m → ℝ) :
    (H.blowup m).polynomial x = H.polynomial (fun v => ∑ i, x ⟨v, i⟩) := by
  classical
  unfold polynomial blowup
  rw [sum_image (fun f hf g hg h => H.choiceEdge_injective m h)]
  simp only [H.choiceEdge_prod, Fintype.sum_sigma]
  calc
    _ = ∑ e : H.edges, ∏ v : e.val, ∑ i, x ⟨v.val, i⟩ := by
      apply sum_congr rfl
      intro e he
      exact (Fintype.prod_sum (fun (v : e.val) (i : Fin (m v.val)) => x ⟨v.val, i⟩)).symm
    _ = ∑ e : H.edges, ∏ v ∈ e.val, ∑ i, x ⟨v, i⟩ := by
      apply sum_congr rfl
      intro e he
      exact prod_attach e.val (fun v => ∑ i, x ⟨v, i⟩)
    _ = _ := sum_attach H.edges (fun e => ∏ v ∈ e, ∑ i, x ⟨v, i⟩)

lemma polynomial_indicator (H : UniformHypergraph V r) (S : Finset V) :
    H.polynomial (fun v => if v ∈ S then 1 else 0) = (H.inducedEdges S).card := by
  classical
  unfold polynomial inducedEdges
  rw [card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, sum_filter]
  apply sum_congr rfl
  intro e he
  by_cases h : e ⊆ S
  · simp [h, prod_eq_one (fun v hv => if_pos (h hv))]
  · have hex : ∃ v ∈ e, v ∉ S := by simpa only [subset_iff, not_forall, exists_prop] using h
    obtain ⟨v, hv, hvS⟩ := hex
    rw [if_neg h]
    exact prod_eq_zero hv (by simp [hvS])

lemma polynomial_one (H : UniformHypergraph V r) : H.polynomial (fun _ => 1) = H.edges.card := by
  simp [polynomial]

lemma blowup_card_edges (H : UniformHypergraph V r) (m : V → ℕ) :
    ((H.blowup m).edges.card : ℝ) = H.polynomial (fun v => (m v : ℝ)) := by
  rw [← polynomial_one, blowup_polynomial]
  simp

variable [Fintype V]

omit [DecidableEq V] in
lemma blowup_card_vertices (m : V → ℕ) : Fintype.card (BlowupVertex m) = ∑ v, m v := by
  simp [BlowupVertex, Fintype.card_sigma]

end Erdos1075.UniformHypergraph
