import Erdos1075.Hypergraph
import Erdos1075.Path

namespace Erdos1075

open Finset

/-- The seven named types of vertices in the manuscript. -/
abbrev CycleVertex (n : ℕ) :=
  Fin n ⊕ (Fin n ⊕ (Unit ⊕ (Unit ⊕ (Unit ⊕ (Fin 12 ⊕ Fin 14)))))

instance (n : ℕ) : DecidableEq (CycleVertex n) := instDecidableEqSum

noncomputable section

namespace CycleVertex

variable {n : ℕ}

def A (i : Fin n) : CycleVertex n := Sum.inl i
def B (i : Fin n) : CycleVertex n := Sum.inr (Sum.inl i)
def C : CycleVertex n := Sum.inr (Sum.inr (Sum.inl ()))
def U : CycleVertex n := Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))
def V : CycleVertex n := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
def W (i : Fin 12) : CycleVertex n := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
def D (i : Fin 14) : CycleVertex n := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))))

lemma sum_weights (x : CycleVertex n → ℝ) :
    (∑ v, x v) = (∑ i, x (A i)) + (∑ i, x (B i)) + x C + x U + x V +
      (∑ i, x (W i)) + (∑ i, x (D i)) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  unfold A B C U V W D
  ring

def commonW : Finset (CycleVertex n) := univ.image W
def commonD : Finset (CycleVertex n) := univ.image D

@[simp] lemma mem_commonW (v : CycleVertex n) : v ∈ commonW ↔ ∃ i, W i = v := by
  simp [commonW]

@[simp] lemma mem_commonD (v : CycleVertex n) : v ∈ commonD ↔ ∃ i, D i = v := by
  simp [commonD]

lemma card_commonW : (commonW : Finset (CycleVertex n)).card = 12 := by
  rw [commonW, card_image_of_injective]
  · simp
  · intro i j h
    simpa [W] using h

lemma card_commonD : (commonD : Finset (CycleVertex n)).card = 14 := by
  rw [commonD, card_image_of_injective]
  · simp
  · intro i j h
    simpa [D] using h

def firstChoice (i : Fin n) (b : Bool) : CycleVertex n := if b then B i else C

abbrev OtherChoice (i : Fin n) := {j : Fin n // j ≠ i} ⊕ Fin 14

def otherVertex (i : Fin n) : OtherChoice i → CycleVertex n
  | Sum.inl j => B j.val
  | Sum.inr j => D j

abbrev TripleCode (n : ℕ) := Σ i : Fin n, Bool × OtherChoice i

def firstTriple (f : TripleCode n) : Finset (CycleVertex n) :=
  {A f.1, firstChoice f.1 f.2.1, otherVertex f.1 f.2.2}

lemma first_ne_A (i : Fin n) (b : Bool) (j : Fin n) : firstChoice i b ≠ A j := by
  cases b <;> simp [firstChoice, A, B, C]

lemma other_ne_A (i : Fin n) (b : OtherChoice i) (j : Fin n) : otherVertex i b ≠ A j := by
  cases b <;> simp [otherVertex, A, B, D]

lemma other_ne_C (i : Fin n) (b : OtherChoice i) : otherVertex i b ≠ C := by
  cases b <;> simp [otherVertex, B, C, D]

lemma other_ne_B (i : Fin n) (b : OtherChoice i) : otherVertex i b ≠ B i := by
  cases b with
  | inl j => simpa [otherVertex, B] using j.property
  | inr j => simp [otherVertex, B, D]

lemma first_ne_other (i : Fin n) (b : Bool) (j : OtherChoice i) : firstChoice i b ≠ otherVertex i j := by
  cases b
  · simpa [firstChoice] using (other_ne_C i j).symm
  · simpa [firstChoice] using (other_ne_B i j).symm

lemma firstTriple_card (f : TripleCode n) : (firstTriple f).card = 3 := by
  simp [firstTriple, (first_ne_A f.1 f.2.1 f.1).symm,
    (other_ne_A f.1 f.2.2 f.1).symm, first_ne_other]

lemma memC_firstTriple (f : TripleCode n) : C ∈ firstTriple f ↔ f.2.1 = false := by
  have hCA : C ≠ A f.1 := by simp [C, A]
  have hCB : C ≠ B f.1 := by simp [C, B]
  have hCY := (other_ne_C f.1 f.2.2).symm
  cases hb : f.2.1 <;> simp [firstTriple, firstChoice, hb, hCA, hCB, hCY]

lemma firstTriple_injective : Function.Injective (firstTriple (n := n)) := by
  rintro ⟨i, b, y⟩ ⟨j, b', y'⟩ h
  have hi : i = j := by
    have hm : A i ∈ firstTriple ⟨j, b', y'⟩ := by rw [← h]; simp [firstTriple]
    simp only [firstTriple, mem_insert, mem_singleton] at hm
    rcases hm with hm | hm | hm
    · simpa [A] using hm
    · exact False.elim (first_ne_A j b' i hm.symm)
    · exact False.elim (other_ne_A j y' i hm.symm)
  subst j
  have hb : b = b' := by
    have hm := congrArg (fun e => C ∈ e) h
    simp only [memC_firstTriple] at hm
    cases b <;> cases b' <;> simp_all
  subst b'
  have hy : otherVertex i y = otherVertex i y' := by
    have hm : otherVertex i y ∈ firstTriple ⟨i, b, y'⟩ := by rw [← h]; simp [firstTriple]
    simpa [firstTriple, other_ne_A, (first_ne_other i b y).symm] using hm
  have hy' : y = y' := by
    cases y <;> cases y' <;> simp_all [otherVertex, B, D, Subtype.ext_iff]
  subst y'
  rfl

lemma firstTriple_prod (f : TripleCode n) (x : CycleVertex n → ℝ) :
    (∏ v ∈ firstTriple f, x v) = x (A f.1) * x (firstChoice f.1 f.2.1) * x (otherVertex f.1 f.2.2) := by
  simp [firstTriple, (first_ne_A f.1 f.2.1 f.1).symm,
    (other_ne_A f.1 f.2.2 f.1).symm, first_ne_other, mul_assoc]

lemma sum_otherVertex (i : Fin n) (x : CycleVertex n → ℝ) :
    (∑ y : OtherChoice i, x (otherVertex i y)) = (∑ j, x (B j)) - x (B i) + (∑ j, x (D j)) := by
  rw [Fintype.sum_sum_type]
  simp only [otherVertex]
  have he : (∑ j : {j : Fin n // j ≠ i}, x (B j.val)) = ∑ j ∈ univ.erase i, x (B j) :=
    (sum_subtype (univ.erase i) (by simp) (fun j => x (B j))).symm
  rw [he, sum_erase_eq_sub (mem_univ i)]

lemma sum_firstTriple_prod (x : CycleVertex n → ℝ) :
    (∑ f : TripleCode n, ∏ v ∈ firstTriple f, x v) =
      ∑ i, x (A i) * (x (B i) + x C) * ((∑ j, x (B j)) - x (B i) + (∑ j, x (D j))) := by
  simp only [firstTriple_prod, Fintype.sum_sigma, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i hi
  simp only [← mul_sum, sum_otherVertex]
  simp [firstChoice]
  ring

def firstCommon : Finset (CycleVertex n) := insert U commonW

lemma firstTriple_disjoint_common (f : TripleCode n) :
    Disjoint firstCommon (firstTriple f) := by
  apply disjoint_left.mpr
  intro v hv ht
  simp only [firstTriple, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · simp [firstCommon, A, U, W] at hv
  · cases h : f.2.1 <;> simp [firstCommon, firstChoice, h, B, C, U, W] at hv
  · cases h : f.2.2 <;> simp [firstCommon, otherVertex, h, B, D, U, W] at hv

def firstEdge (f : TripleCode n) : Finset (CycleVertex n) := firstCommon ∪ firstTriple f

lemma firstCommon_card : (firstCommon : Finset (CycleVertex n)).card = 13 := by
  rw [firstCommon, card_insert_of_notMem]
  · rw [card_commonW]
  · simp [U, W]

lemma firstEdge_card (f : TripleCode n) : (firstEdge f).card = 16 := by
  rw [firstEdge, card_union_of_disjoint (firstTriple_disjoint_common f), firstCommon_card, firstTriple_card]

lemma firstEdge_injective : Function.Injective (firstEdge (n := n)) := by
  intro f g h
  apply firstTriple_injective
  have he := congrArg (fun e => e \ firstCommon) h
  simpa only [firstEdge, union_sdiff_cancel_left (firstTriple_disjoint_common f),
    union_sdiff_cancel_left (firstTriple_disjoint_common g)] using he

lemma firstEdge_prod (f : TripleCode n) (x : CycleVertex n → ℝ) :
    (∏ v ∈ firstEdge f, x v) = (∏ i, x (W i)) * x U * (∏ v ∈ firstTriple f, x v) := by
  rw [firstEdge, prod_union (firstTriple_disjoint_common f), firstCommon, prod_insert]
  · rw [commonW, prod_image]
    · ring
    · intro i hi j hj h
      simpa [W] using h
  · simp [U, W]

def firstFamily : UniformHypergraph (CycleVertex n) 16 where
  edges := univ.image firstEdge
  uniform := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    exact firstEdge_card f

lemma firstFamily_polynomial (x : CycleVertex n → ℝ) :
    firstFamily.polynomial x = (∏ i, x (W i)) * x U *
      (∑ i, x (A i) * (x (B i) + x C) * ((∑ j, x (B j)) - x (B i) + (∑ j, x (D j)))) := by
  unfold UniformHypergraph.polynomial firstFamily
  rw [sum_image (fun f hf g hg h => firstEdge_injective h)]
  simp only [firstEdge_prod, ← mul_sum, sum_firstTriple_prod]

def flipVertex (σ : Equiv.Perm (Fin n)) : Equiv.Perm (CycleVertex n) where
  toFun
    | Sum.inl i => B (σ.symm i)
    | Sum.inr (Sum.inl i) => A i
    | Sum.inr (Sum.inr (Sum.inl _)) => C
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => V
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => U
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) => W i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))) => D i
  invFun
    | Sum.inl i => B i
    | Sum.inr (Sum.inl i) => A (σ i)
    | Sum.inr (Sum.inr (Sum.inl _)) => C
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => V
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => U
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) => W i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))) => D i
  left_inv := by
    rintro (i | i | ⟨⟩ | ⟨⟩ | ⟨⟩ | i | i) <;> simp [A, B, C, U, V, W, D]
  right_inv := by
    rintro (i | i | ⟨⟩ | ⟨⟩ | ⟨⟩ | i | i) <;> simp [A, B, C, U, V, W, D]

@[simp] lemma flip_A (σ : Equiv.Perm (Fin n)) (i : Fin n) : flipVertex σ (A i) = B (σ.symm i) := rfl
@[simp] lemma flip_B (σ : Equiv.Perm (Fin n)) (i : Fin n) : flipVertex σ (B i) = A i := rfl
@[simp] lemma flip_C (σ : Equiv.Perm (Fin n)) : flipVertex σ C = C := rfl
@[simp] lemma flip_U (σ : Equiv.Perm (Fin n)) : flipVertex σ U = V := rfl
@[simp] lemma flip_V (σ : Equiv.Perm (Fin n)) : flipVertex σ V = U := rfl
@[simp] lemma flip_W (σ : Equiv.Perm (Fin n)) (i : Fin 12) : flipVertex σ (W i) = W i := rfl
@[simp] lemma flip_D (σ : Equiv.Perm (Fin n)) (i : Fin 14) : flipVertex σ (D i) = D i := rfl

def secondFamily (σ : Equiv.Perm (Fin n)) : UniformHypergraph (CycleVertex n) 16 :=
  firstFamily.map (flipVertex σ).toEmbedding

lemma secondFamily_polynomial (σ : Equiv.Perm (Fin n)) (x : CycleVertex n → ℝ) :
    (secondFamily σ).polynomial x = (∏ i, x (W i)) * x V *
      (∑ i, x (B i) * (x (A (σ i)) + x C) * ((∑ j, x (A j)) - x (A (σ i)) + (∑ j, x (D j)))) := by
  rw [secondFamily, UniformHypergraph.map_polynomial, firstFamily_polynomial]
  simp only [Equiv.coe_toEmbedding, flip_W, flip_U, flip_A, flip_B, flip_C, flip_D]
  congr 1
  exact (Equiv.sum_comp σ (fun i => x (B (σ.symm i)) * (x (A i) + x C) *
    ((∑ j, x (A j)) - x (A i) + (∑ j, x (D j))))).symm.trans (by simp)

lemma U_mem_firstEdge (f : TripleCode n) : U ∈ firstEdge f := by simp [firstEdge, firstCommon]

lemma V_not_mem_firstEdge (f : TripleCode n) : V ∉ firstEdge f := by
  rcases f with ⟨i, b, y⟩
  cases b <;> cases y <;> simp [firstEdge, firstCommon, firstTriple, firstChoice, otherVertex, A, B, C, U, V, W, D]

lemma W_mem_firstEdge (f : TripleCode n) (i : Fin 12) : W i ∈ firstEdge f := by
  simp [firstEdge, firstCommon]

lemma families_disjoint (σ : Equiv.Perm (Fin n)) : Disjoint firstFamily.edges (secondFamily σ).edges := by
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨f, hfuniv, rfl⟩ := mem_image.mp he
  obtain ⟨e, hemem, heq⟩ := mem_image.mp hf
  obtain ⟨g, hg, rfl⟩ := mem_image.mp hemem
  have hV : V ∈ firstEdge f := by
    rw [← heq]
    exact mem_image.mpr ⟨U, U_mem_firstEdge g, flip_U σ⟩
  exact V_not_mem_firstEdge f hV

def extraEdge : Finset (CycleVertex n) := insert U (insert V commonD)

lemma extraEdge_card : (extraEdge : Finset (CycleVertex n)).card = 16 := by
  simp [extraEdge, card_insert_of_notMem, card_commonD, U, V, D]

lemma extraEdge_prod (x : CycleVertex n → ℝ) : (∏ v ∈ extraEdge, x v) = x U * x V * (∏ i, x (D i)) := by
  simp only [extraEdge]
  rw [prod_insert (by simp [U, V, D]), prod_insert (by simp [V, D])]
  rw [commonD, prod_image (fun i hi j hj h => by simpa [D] using h)]
  ring

lemma extra_not_first : extraEdge ∉ (firstFamily (n := n)).edges := by
  intro h
  obtain ⟨f, hf, he⟩ := mem_image.mp h
  have hw := W_mem_firstEdge f 0
  rw [he] at hw
  simp [extraEdge, W, U, V, D] at hw

lemma extra_not_second (σ : Equiv.Perm (Fin n)) : extraEdge ∉ (secondFamily σ).edges := by
  intro h
  obtain ⟨e, he, heq⟩ := mem_image.mp h
  obtain ⟨f, hf, rfl⟩ := mem_image.mp he
  have hw : W 0 ∈ (firstEdge f).image (flipVertex σ).toEmbedding :=
    mem_image.mpr ⟨W 0, W_mem_firstEdge f 0, flip_W σ 0⟩
  rw [heq] at hw
  simp [extraEdge, W, U, V, D] at hw

/-- The finite, simple sixteen-uniform template, with an arbitrary linking permutation. -/
def cycleGraph (σ : Equiv.Perm (Fin n)) : UniformHypergraph (CycleVertex n) 16 where
  edges := insert extraEdge (firstFamily.edges ∪ (secondFamily σ).edges)
  uniform := by
    intro e he
    rcases mem_insert.mp he with rfl | he
    · exact extraEdge_card
    · rcases mem_union.mp he with he | he
      · exact firstFamily.uniform e he
      · exact (secondFamily σ).uniform e he

theorem cycleGraph_polynomial (σ : Equiv.Perm (Fin n)) (x : CycleVertex n → ℝ) :
    (cycleGraph σ).polynomial x = (∏ i, x (W i)) *
      (x U * (∑ i, x (A i) * (x (B i) + x C) * ((∑ j, x (B j)) - x (B i) + (∑ j, x (D j)))) +
       x V * (∑ i, x (B i) * (x (A (σ i)) + x C) * ((∑ j, x (A j)) - x (A (σ i)) + (∑ j, x (D j))))) +
      x U * x V * (∏ i, x (D i)) := by
  unfold UniformHypergraph.polynomial cycleGraph
  rw [sum_insert (by simp [extra_not_first, extra_not_second]), sum_union (families_disjoint σ)]
  change (∏ v ∈ extraEdge, x v) + (firstFamily.polynomial x + (secondFamily σ).polynomial x) = _
  rw [extraEdge_prod, firstFamily_polynomial, secondFamily_polynomial]
  ring

end CycleVertex

end

end Erdos1075
