import Erdos1075.Potential

namespace Erdos1075

open Finset

lemma square_below_third {x t : ℝ} (ht : 0 ≤ t) (hx : x ≤ t / 3) :
    4 / 9 * t ^ 2 ≤ (x - t) ^ 2 := by
  have h := mul_nonneg (show 0 ≤ t / 3 - x by linarith)
    (show 0 ≤ 5 * t / 3 - x by linarith)
  nlinarith

lemma cubic_square_identity (L : ℕ) (a b : ℕ → ℝ) (A B c D : ℝ)
    (hA : ∑ i ∈ range L, a i = A) (hmass : A + B + c + D = 1) :
    (∑ i ∈ range L, a i * (b i + c) * (B - b i + D)) =
      A * (1 - A) ^ 2 / 4 -
        ∑ i ∈ range L, a i * (b i - (B + D - c) / 2) ^ 2 := by
  have hi (i : ℕ) :
      a i * (b i + c) * (B - b i + D) +
        a i * (b i - (B + D - c) / 2) ^ 2 = a i * ((1 - A) ^ 2 / 4) := by
    rw [show c = 1 - A - B - D by linarith]
    ring
  have hsum := sum_congr (s₁ := range L) rfl (fun i _ => hi i)
  rw [sum_add_distrib, ← sum_mul, hA] at hsum
  linarith

lemma one_variable_cubic_loss (x : ℝ) :
    1 / 27 - x * (1 - x) ^ 2 / 4 = (x - 1 / 3) ^ 2 * (4 / 3 - x) / 4 := by
  ring

/-- A quadratic potential accumulates the square energy along the whole path. -/
lemma path_square_energy (L : ℕ) (a b : ℕ → ℝ) (α β s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : ∀ i < L, 0 ≤ a i) (hb : ∀ i < L, 0 ≤ b i)
    (hend : a L = 0) (hα1 : α ≤ 1 / 2) (hβ1 : β ≤ 1 / 2)
    (hmass : 1 / 4 ≤ (∑ i ∈ range L, a i) + ∑ i ∈ range L, b i) :
    2 / 9 * min (s * α * β ^ 2) ((1 - s) * β * α ^ 2) ≤
      s * (∑ i ∈ range L, a i * (b i - β) ^ 2) +
      (1 - s) * (∑ i ∈ range L, b i * (a (i + 1) - α) ^ 2) := by
  let M := min (s * α * β ^ 2) ((1 - s) * β * α ^ 2)
  let E₁ := ∑ i ∈ range L, a i * (b i - β) ^ 2
  let E₂ := ∑ i ∈ range L, b i * (a (i + 1) - α) ^ 2
  have hs' : 0 ≤ 1 - s := by linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMa : M ≤ s * α * β ^ 2 := min_le_left _ _
  have hMb : M ≤ (1 - s) * β * α ^ 2 := min_le_right _ _
  have hnext (i : ℕ) (hi : i < L) : 0 ≤ a (i + 1) := by
    by_cases hn : i + 1 < L
    · exact ha _ hn
    · have hi' : i + 1 = L := by omega
      rw [hi', hend]
  change 2 / 9 * M ≤ s * E₁ + (1 - s) * E₂
  by_cases hlarge : ∃ i < L, α / 3 ≤ a i ∨ β / 3 ≤ b i
  · have hstepa (i : ℕ) (hi : i < L) :
        M * pathPotential (a i / α) - M * pathPotential (b i / β) ≤ s * a i * (b i - β) ^ 2 := by
      have h := scaled_potential_step (ha i hi) (hb i hi) hα hβ hM hMa
      nlinarith only [h]
    have hstepb (i : ℕ) (hi : i < L) :
        M * pathPotential (b i / β) - M * pathPotential (a (i + 1) / α) ≤
          (1 - s) * b i * (a (i + 1) - α) ^ 2 := by
      have h := scaled_potential_step (hb i hi) (hnext i hi) hβ hα hM hMb
      nlinarith only [h]
    have hpath := potential_le_path_cost L
      (fun i => M * pathPotential (a i / α)) (fun i => M * pathPotential (b i / β))
      (fun i => s * a i * (b i - β) ^ 2) (fun i => (1 - s) * b i * (a (i + 1) - α) ^ 2)
      (fun i hi => by have := ha i hi; positivity)
      (fun i hi => by have := hb i hi; positivity) hstepa hstepb
    have heq : (∑ i ∈ range L, (s * a i * (b i - β) ^ 2 +
        (1 - s) * b i * (a (i + 1) - α) ^ 2)) = s * E₁ + (1 - s) * E₂ := by
      dsimp [E₁, E₂]
      rw [sum_add_distrib, mul_sum, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intro i hi <;> ring
    obtain ⟨i, hi, hbig⟩ := hlarge
    have hp := hpath i hi
    simp only [hend, zero_div, pathPotential_zero, mul_zero, sub_zero, heq] at hp
    rcases hbig with hai | hbi
    · have hx : (1 : ℝ) / 3 ≤ a i / α := (le_div_iff₀ hα).mpr (by linarith)
      have h := mul_le_mul_of_nonneg_left (pathPotential_large hx) hM
      linarith only [h, hp.1]
    · have hx : (1 : ℝ) / 3 ≤ b i / β := (le_div_iff₀ hβ).mpr (by linarith)
      have h := mul_le_mul_of_nonneg_left (pathPotential_large hx) hM
      linarith only [h, hp.2]
  · have hsmall (i : ℕ) (hi : i < L) : a i < α / 3 ∧ b i < β / 3 := by
      constructor
      · exact lt_of_not_ge (fun h => hlarge ⟨i, hi, Or.inl h⟩)
      · exact lt_of_not_ge (fun h => hlarge ⟨i, hi, Or.inr h⟩)
    have hnext' (i : ℕ) (hi : i < L) : a (i + 1) ≤ α / 3 := by
      by_cases h : i + 1 < L
      · exact (hsmall (i + 1) h).1.le
      · have : i + 1 = L := by omega
        rw [this, hend]
        positivity
    have hsum₁ : (∑ i ∈ range L, a i) * (4 / 9 * β ^ 2) ≤ E₁ := by
      rw [sum_mul]
      exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (square_below_third hβ.le (hsmall i (mem_range.mp hi)).2.le) (ha i (mem_range.mp hi))
    have hsum₂ : (∑ i ∈ range L, b i) * (4 / 9 * α ^ 2) ≤ E₂ := by
      rw [sum_mul]
      exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (square_below_third hα.le (hnext' i (mem_range.mp hi))) (hb i (mem_range.mp hi))
    have hMa' : 2 * M ≤ s * β ^ 2 := by
      nlinarith only [hMa, mul_nonneg (mul_nonneg hs (sq_nonneg β)) (show 0 ≤ 1 / 2 - α by linarith)]
    have hMb' : 2 * M ≤ (1 - s) * α ^ 2 := by
      nlinarith only [hMb, mul_nonneg (mul_nonneg hs' (sq_nonneg α)) (show 0 ≤ 1 / 2 - β by linarith)]
    have hA0 : 0 ≤ ∑ i ∈ range L, a i := sum_nonneg fun i hi => ha i (mem_range.mp hi)
    have hB0 : 0 ≤ ∑ i ∈ range L, b i := sum_nonneg fun i hi => hb i (mem_range.mp hi)
    have ha' := mul_le_mul_of_nonneg_right hMa' hA0
    have hb' := mul_le_mul_of_nonneg_right hMb' hB0
    have h₁ := mul_le_mul_of_nonneg_left hsum₁ hs
    have h₂ := mul_le_mul_of_nonneg_left hsum₂ hs'
    have htotal := mul_le_mul_of_nonneg_left hmass hM
    nlinarith only [ha', hb', h₁, h₂, htotal]

lemma near_balanced_energy {α β s m E : ℝ} (hm : 0 ≤ m)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hα : m ≤ α) (hβ : m ≤ β)
    (he : 2 / 9 * min (s * α * β ^ 2) ((1 - s) * β * α ^ 2) ≤ E) :
    2 / 9 * s * (1 - s) * m ^ 3 ≤ E := by
  have hα0 : 0 ≤ α := hm.trans hα
  have hβ0 : 0 ≤ β := hm.trans hβ
  have hs' : 0 ≤ 1 - s := by linarith
  have hp₁ : m ^ 3 ≤ α * β ^ 2 := by
    calc m ^ 3 = m * m ^ 2 := by ring
         _ ≤ α * β ^ 2 := by gcongr
  have hp₂ : m ^ 3 ≤ β * α ^ 2 := by
    calc m ^ 3 = m * m ^ 2 := by ring
         _ ≤ β * α ^ 2 := by gcongr
  have hmul₁ := mul_le_mul_of_nonneg_left hp₁ hs
  have hmul₂ := mul_le_mul_of_nonneg_left hp₂ hs'
  have ht₁ := mul_le_mul_of_nonneg_right (show s * (1 - s) ≤ s by nlinarith [sq_nonneg s]) (pow_nonneg hm 3)
  have ht₂ := mul_le_mul_of_nonneg_right (show s * (1 - s) ≤ 1 - s by nlinarith [sq_nonneg (1 - s)]) (pow_nonneg hm 3)
  have hmin : s * (1 - s) * m ^ 3 ≤ min (s * α * β ^ 2) ((1 - s) * β * α ^ 2) := by
    apply le_min <;> nlinarith only [hmul₁, hmul₂, ht₁, ht₂]
  linarith only [he, hmin]

/-- The quantitative cubic bound, uniformly in the path length. -/
theorem path_cubic_bound (L : ℕ) (a b : ℕ → ℝ) (c D s : ℝ)
    (ha : ∀ i < L, 0 ≤ a i) (hb : ∀ i < L, 0 ≤ b i)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hend : a L = 0)
    (hmass : (∑ i ∈ range L, a i) + (∑ i ∈ range L, b i) + c + D = 1) :
    s * (∑ i ∈ range L, a i * (b i + c) * ((∑ j ∈ range L, b j) - b i + D)) +
      (1 - s) * (∑ i ∈ range L, b i * (a (i + 1) + c) *
        ((∑ j ∈ range L, a j) - a (i + 1) + D)) ≤
        1 / 27 - s * (1 - s) * D ^ 3 / 10 := by
  let A := ∑ i ∈ range L, a i
  let B := ∑ i ∈ range L, b i
  let α := (A + D - c) / 2
  let β := (B + D - c) / 2
  let E₁ := ∑ i ∈ range L, a i * (b i - β) ^ 2
  let E₂ := ∑ i ∈ range L, b i * (a (i + 1) - α) ^ 2
  let E := s * E₁ + (1 - s) * E₂
  have hmass' : A + B + c + D = 1 := hmass
  have hA0 : 0 ≤ A := sum_nonneg fun i hi => ha i (mem_range.mp hi)
  have hB0 : 0 ≤ B := sum_nonneg fun i hi => hb i (mem_range.mp hi)
  have hA1 : A ≤ 1 := by linarith
  have hB1 : B ≤ 1 := by linarith
  have hD1 : D ≤ 1 := by linarith
  have hs' : 0 ≤ 1 - s := by linarith
  have he₁ : 0 ≤ E₁ := sum_nonneg fun i hi => mul_nonneg (ha i (mem_range.mp hi)) (sq_nonneg _)
  have he₂ : 0 ≤ E₂ := sum_nonneg fun i hi => mul_nonneg (hb i (mem_range.mp hi)) (sq_nonneg _)
  have he : 0 ≤ E := add_nonneg (mul_nonneg hs he₁) (mul_nonneg hs' he₂)
  rw [cubic_square_identity L a b A B c D rfl hmass',
    cubic_square_identity L b (fun i => a (i + 1)) B A c D rfl (by linarith)]
  change s * (A * (1 - A) ^ 2 / 4 - E₁) +
    (1 - s) * (B * (1 - B) ^ 2 / 4 - E₂) ≤ _
  have hid :
      1 / 27 - (s * (A * (1 - A) ^ 2 / 4 - E₁) +
        (1 - s) * (B * (1 - B) ^ 2 / 4 - E₂)) =
      s * (A - 1 / 3) ^ 2 * (4 / 3 - A) / 4 +
        (1 - s) * (B - 1 / 3) ^ 2 * (4 / 3 - B) / 4 + E := by
    dsimp [E]
    ring
  have hla : s * D * (A - 1 / 3) ^ 2 / 3 ≤
      s * (A - 1 / 3) ^ 2 * (4 / 3 - A) / 4 := by
    have hcoef : 0 ≤ 4 / 3 - A - 4 * D / 3 := by linarith
    nlinarith only [mul_nonneg (mul_nonneg hs (sq_nonneg (A - 1 / 3))) hcoef]
  have hlb : (1 - s) * D * (B - 1 / 3) ^ 2 / 3 ≤
      (1 - s) * (B - 1 / 3) ^ 2 * (4 / 3 - B) / 4 := by
    have hcoef : 0 ≤ 4 / 3 - B - 4 * D / 3 := by linarith
    nlinarith only [mul_nonneg (mul_nonneg hs' (sq_nonneg (B - 1 / 3))) hcoef]
  have hbase : s * D * (A - 1 / 3) ^ 2 / 3 + (1 - s) * D * (B - 1 / 3) ^ 2 / 3 + E ≤
      1 / 27 - (s * (A * (1 - A) ^ 2 / 4 - E₁) +
        (1 - s) * (B * (1 - B) ^ 2 / 4 - E₂)) := by
    linarith only [hid, hla, hlb]
  let S := |A - 1 / 3| + |B - 1 / 3|
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have habsa := abs_nonneg (A - 1 / 3)
  have habsb := abs_nonneg (B - 1 / 3)
  have hla' := neg_abs_le (A - 1 / 3)
  have hlb' := neg_abs_le (B - 1 / 3)
  have hAB : 2 / 3 - S ≤ A + B := by dsimp [S]; linarith
  have hss : 0 ≤ s * (1 - s) := mul_nonneg hs hs'
  have hsq : s * (1 - s) * S ^ 2 ≤ s * (A - 1 / 3) ^ 2 + (1 - s) * (B - 1 / 3) ^ 2 := by
    dsimp [S]
    rw [← sq_abs (A - 1 / 3), ← sq_abs (B - 1 / 3)]
    nlinarith only [sq_nonneg (s * |A - 1 / 3| - (1 - s) * |B - 1 / 3|)]
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ D / 3 by positivity)
  have hbase' : s * (1 - s) * D * S ^ 2 / 3 + E ≤
      1 / 27 - (s * (A * (1 - A) ^ 2 / 4 - E₁) + (1 - s) * (B * (1 - B) ^ 2 / 4 - E₂)) := by
    nlinarith only [hbase, hmul]
  by_cases hlarge : 11 * D / 20 ≤ S
  · have hsquare := mul_self_le_mul_self (show 0 ≤ 11 * D / 20 by positivity) hlarge
    have h := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hss hD)
    have hz := mul_nonneg hss (pow_nonneg hD 3)
    nlinarith only [hbase', h, hz, he]
  have hsmall : S < 11 * D / 20 := lt_of_not_ge hlarge
  have hDpos : 0 < D := by linarith
  have hDsmall : D ≤ 20 / 27 := by linarith
  have hABquarter : 1 / 4 ≤ A + B := by linarith
  have hm : 0 ≤ D - S := by linarith
  have hαl : D - S ≤ α := by dsimp [α, S]; linarith
  have hβl : D - S ≤ β := by dsimp [β, S]; linarith
  have hαpos : 0 < α := by linarith
  have hβpos : 0 < β := by linarith
  have hαu : α ≤ 1 / 2 := by dsimp [α]; linarith
  have hβu : β ≤ 1 / 2 := by dsimp [β]; linarith
  have henergy := path_square_energy L a b α β s hαpos hβpos hs hs1 ha hb hend hαu hβu hABquarter
  have he' := near_balanced_energy hm hs hs1 hαl hβl henergy
  change 2 / 9 * s * (1 - s) * (D - S) ^ 3 ≤ E at he'
  have habsorb := cubic_absorption S (D - S) hS0 hm
  rw [show S + (D - S) = D by ring] at habsorb
  have hfinal := mul_le_mul_of_nonneg_left habsorb hss
  nlinarith only [hbase', he', hfinal]

end Erdos1075
