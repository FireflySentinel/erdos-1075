import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace Erdos1075

open Finset

/-- A finite path must cross one of the two thresholds before its terminal value. -/
lemma path_threshold {L : ℕ} {a b : ℕ → ℝ} {α β : ℝ}
    (hend : a L < α)
    (hlarge : ∃ i < L, α ≤ a i ∨ β ≤ b i) :
    ∃ i < L, (α ≤ a i ∧ b i < β) ∨ (β ≤ b i ∧ a (i + 1) < α) := by
  induction L with
  | zero => obtain ⟨i, hi, _⟩ := hlarge; omega
  | succ L ih =>
    by_cases hb : β ≤ b L
    · exact ⟨L, by omega, Or.inr ⟨hb, hend⟩⟩
    have hb' : b L < β := lt_of_not_ge hb
    by_cases ha : α ≤ a L
    · exact ⟨L, by omega, Or.inl ⟨ha, hb'⟩⟩
    have ha' : a L < α := lt_of_not_ge ha
    obtain ⟨i, hi, hai⟩ := hlarge
    have hi' : i < L := by
      by_contra hn
      have : i = L := by omega
      subst i
      exact hai.elim ha hb
    obtain ⟨j, hj, h⟩ := ih ha' ⟨i, hi', hai⟩
    exact ⟨j, by omega, h⟩

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

/-- The terminal mismatch in a finite open path forces a positive square energy. -/
lemma path_square_energy (L : ℕ) (a b : ℕ → ℝ) (α β s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : ∀ i < L, 0 ≤ a i) (hb : ∀ i < L, 0 ≤ b i)
    (hend : a L = 0)
    (hA : α / 3 ≤ ∑ i ∈ range L, a i)
    (hB : β / 3 ≤ ∑ i ∈ range L, b i) :
    4 / 27 * min (s * α * β ^ 2) ((1 - s) * β * α ^ 2) ≤
      s * (∑ i ∈ range L, a i * (b i - β) ^ 2) +
      (1 - s) * (∑ i ∈ range L, b i * (a (i + 1) - α) ^ 2) := by
  let E₁ := ∑ i ∈ range L, a i * (b i - β) ^ 2
  let E₂ := ∑ i ∈ range L, b i * (a (i + 1) - α) ^ 2
  have he₁ : 0 ≤ E₁ := sum_nonneg fun i hi => mul_nonneg (ha i (mem_range.mp hi)) (sq_nonneg _)
  have he₂ : 0 ≤ E₂ := sum_nonneg fun i hi => mul_nonneg (hb i (mem_range.mp hi)) (sq_nonneg _)
  have hs' : 0 ≤ 1 - s := by linarith
  change 4 / 27 * min _ _ ≤ s * E₁ + (1 - s) * E₂
  by_cases hlarge : ∃ i < L, α / 3 ≤ a i ∨ β / 3 ≤ b i
  · have hend' : a L < α / 3 := by rw [hend]; positivity
    obtain ⟨i, hi, h⟩ := path_threshold hend' hlarge
    rcases h with ⟨hai, hbi⟩ | ⟨hbi, hai⟩
    · have hsquare := square_below_third hβ.le hbi.le
      have hterm : α / 3 * (4 / 9 * β ^ 2) ≤ a i * (b i - β) ^ 2 :=
        mul_le_mul hai hsquare (by positivity) (ha i hi)
      have hsum : a i * (b i - β) ^ 2 ≤ E₁ :=
        single_le_sum (f := fun j => a j * (b j - β) ^ 2)
          (fun j hj => mul_nonneg (ha j (mem_range.mp hj)) (sq_nonneg _))
          (mem_range.mpr hi)
      have hmul := mul_le_mul_of_nonneg_left (hterm.trans hsum) hs
      have hmin := min_le_left (s * α * β ^ 2) ((1 - s) * β * α ^ 2)
      have hpos := mul_nonneg hs' he₂
      nlinarith
    · have hsquare := square_below_third hα.le hai.le
      have hterm : β / 3 * (4 / 9 * α ^ 2) ≤ b i * (a (i + 1) - α) ^ 2 :=
        mul_le_mul hbi hsquare (by positivity) (hb i hi)
      have hsum : b i * (a (i + 1) - α) ^ 2 ≤ E₂ :=
        single_le_sum (f := fun j => b j * (a (j + 1) - α) ^ 2)
          (fun j hj => mul_nonneg (hb j (mem_range.mp hj)) (sq_nonneg _))
          (mem_range.mpr hi)
      have hmul := mul_le_mul_of_nonneg_left (hterm.trans hsum) hs'
      have hmin := min_le_right (s * α * β ^ 2) ((1 - s) * β * α ^ 2)
      have hpos := mul_nonneg hs he₁
      nlinarith
  · have hsmall (i : ℕ) (hi : i < L) : a i < α / 3 ∧ b i < β / 3 := by
      constructor
      · exact lt_of_not_ge (fun h => hlarge ⟨i, hi, Or.inl h⟩)
      · exact lt_of_not_ge (fun h => hlarge ⟨i, hi, Or.inr h⟩)
    have hnext (i : ℕ) (hi : i < L) : a (i + 1) ≤ α / 3 := by
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
        (square_below_third hα.le (hnext i (mem_range.mp hi))) (hb i (mem_range.mp hi))
    have hbound₁ := (mul_le_mul_of_nonneg_right hA (show 0 ≤ 4 / 9 * β ^ 2 by positivity)).trans hsum₁
    have hbound₂ := (mul_le_mul_of_nonneg_right hB (show 0 ≤ 4 / 9 * α ^ 2 by positivity)).trans hsum₂
    have hm₁ := mul_le_mul_of_nonneg_left hbound₁ hs
    have hm₂ := mul_le_mul_of_nonneg_left hbound₂ hs'
    have hmin := min_le_left (s * α * β ^ 2) ((1 - s) * β * α ^ 2)
    have hpos : 0 ≤ (1 - s) * β * α ^ 2 := by positivity
    nlinarith

lemma large_deviation_loss {δ D s : ℝ} (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hδ : D / 4 ≤ |δ|) :
    s * (1 - s) * D ^ 3 / 48 ≤ s * D * δ ^ 2 / 3 := by
  have hsq := mul_self_le_mul_self (show 0 ≤ D / 4 by positivity) hδ
  rw [← sq, ← sq, sq_abs] at hsq
  have hmul := mul_le_mul_of_nonneg_left hsq (mul_nonneg hs hD)
  nlinarith [mul_nonneg (sq_nonneg s) (pow_nonneg hD 3)]

lemma near_balanced_energy {α β s D E : ℝ} (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hα : 5 * D / 8 ≤ α) (hβ : 5 * D / 8 ≤ β)
    (he : 4 / 27 * min (s * α * β ^ 2) ((1 - s) * β * α ^ 2) ≤ E) :
    s * (1 - s) * D ^ 3 / 48 ≤ E := by
  have hα0 : 0 ≤ α := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have hs' : 0 ≤ 1 - s := by linarith
  have hprod₁ : (5 * D / 8) ^ 3 ≤ α * β ^ 2 := by
    calc
      (5 * D / 8) ^ 3 = (5 * D / 8) * (5 * D / 8) ^ 2 := by ring
      _ ≤ α * β ^ 2 := by gcongr
  have hprod₂ : (5 * D / 8) ^ 3 ≤ β * α ^ 2 := by
    calc
      (5 * D / 8) ^ 3 = (5 * D / 8) * (5 * D / 8) ^ 2 := by ring
      _ ≤ β * α ^ 2 := by gcongr
  have hmul₁ := mul_le_mul_of_nonneg_left hprod₁ hs
  have hmul₂ := mul_le_mul_of_nonneg_left hprod₂ hs'
  have hz : 0 ≤ s * (1 - s) * D ^ 3 := by positivity
  have hss₁ : s * (1 - s) ≤ s := by nlinarith [sq_nonneg s]
  have hss₂ : s * (1 - s) ≤ 1 - s := by nlinarith [sq_nonneg (1 - s)]
  have ht₁ := mul_le_mul_of_nonneg_right hss₁ (show 0 ≤ D ^ 3 by positivity)
  have ht₂ := mul_le_mul_of_nonneg_right hss₂ (show 0 ≤ D ^ 3 by positivity)
  have hmin : 125 / 512 * (s * (1 - s) * D ^ 3) ≤
      min (s * α * β ^ 2) ((1 - s) * β * α ^ 2) := by
    apply le_min
    · nlinarith only [hmul₁, ht₁]
    · nlinarith only [hmul₂, ht₂]
  nlinarith only [he, hmin, hz]

/-- Lemma 4: the quantitative cubic bound, uniformly in the path length. -/
theorem path_cubic_bound (L : ℕ) (a b : ℕ → ℝ) (c D s : ℝ)
    (ha : ∀ i < L, 0 ≤ a i) (hb : ∀ i < L, 0 ≤ b i)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hend : a L = 0)
    (hmass : (∑ i ∈ range L, a i) + (∑ i ∈ range L, b i) + c + D = 1) :
    s * (∑ i ∈ range L, a i * (b i + c) * ((∑ j ∈ range L, b j) - b i + D)) +
      (1 - s) * (∑ i ∈ range L, b i * (a (i + 1) + c) *
        ((∑ j ∈ range L, a j) - a (i + 1) + D)) ≤
        1 / 27 - s * (1 - s) * D ^ 3 / 48 := by
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
  have hpa : 0 ≤ s * D * (A - 1 / 3) ^ 2 / 3 := by positivity
  have hpb : 0 ≤ (1 - s) * D * (B - 1 / 3) ^ 2 / 3 := by positivity
  by_cases hDa : D / 4 ≤ |A - 1 / 3|
  · have h := large_deviation_loss hD hs hDa
    linarith only [hbase, h, hpb, he]
  by_cases hDb : D / 4 ≤ |B - 1 / 3|
  · have h := large_deviation_loss hD hs' hDb
    have h' : (1 - s) * (1 - (1 - s)) * D ^ 3 = s * (1 - s) * D ^ 3 := by ring
    rw [h'] at h
    linarith only [hbase, h, hpa, he]
  have hDa' := abs_lt.mp (lt_of_not_ge hDa)
  have hDb' := abs_lt.mp (lt_of_not_ge hDb)
  have hDpos : 0 < D := by linarith [abs_nonneg (A - 1 / 3)]
  have hDsmall : D ≤ 2 / 3 := by linarith
  have hαl : 5 * D / 8 ≤ α := by dsimp [α]; linarith
  have hβl : 5 * D / 8 ≤ β := by dsimp [β]; linarith
  have hαu : α ≤ 11 * D / 8 := by dsimp [α]; linarith
  have hβu : β ≤ 11 * D / 8 := by dsimp [β]; linarith
  have hαpos : 0 < α := by linarith
  have hβpos : 0 < β := by linarith
  have hA : α / 3 ≤ A := by dsimp [α]; linarith
  have hB : β / 3 ≤ B := by dsimp [β]; linarith
  have henergy := path_square_energy L a b α β s hαpos hβpos hs hs1 ha hb hend hA hB
  have h := near_balanced_energy hD hs hs1 hαl hβl henergy
  change _ ≤ E at h
  linarith only [hbase, h, hpa, hpb]

end Erdos1075
