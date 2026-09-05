import Erdos1075.Scalar

namespace Erdos1075

open Finset

noncomputable def baseDensity : ℝ := 1 / 16 ^ 16

lemma baseDensity_pos : 0 < baseDensity := by norm_num [baseDensity]

/-- The homogeneous, scalar part of the sixteen-uniform path bound. -/
lemma path_product_bound (h q t d s ω δ P : ℝ)
    (hh : 0 ≤ h) (hq : 0 ≤ q) (ht : 0 ≤ t) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hmass : h + q + t = 1)
    (_hω : 0 ≤ ω) (hωbound : ω ≤ (h / 12) ^ 12)
    (hδbound : δ ≤ (t * d / 14) ^ 14)
    (hP : 0 ≤ P) (hPbound : P ≤ q * t ^ 3 * (1 / 27 - s * (1-s) * d ^ 3 / 1200)) :
    ω * P + q ^ 2 * s * (1-s) * δ ≤ baseDensity := by
  let z := s * (1-s) * d ^ 3
  have hs' : 0 ≤ 1-s := by linarith
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hss : s * (1-s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s-1/2)]
  have hd3 : d ^ 3 ≤ 1 := by
    calc
      d^3 ≤ (1:ℝ)^3 := by gcongr
      _ = 1 := by norm_num
  have hz1 : z ≤ 1/4 := by
    dsimp [z]
    calc s*(1-s)*d^3 ≤ s*(1-s)*1 := mul_le_mul_of_nonneg_left hd3 (by positivity)
         _ ≤ 1/4 := by simpa using hss
  have hc : 0 ≤ 1 - 9*z/400 := by linarith
  have hqbound : q*t^3/27 ≤ ((q+t)/4)^4 := by
    have h := pow_mul_pow_le_weighted_mean q (t/3) 1 3 hq (by positivity) (by norm_num)
    convert h using 1 <;> ring
  have hqbound' : q^2*t^14/14^14 ≤ 4*((q+t)/16)^16 := by
    have h := pow_mul_pow_le_weighted_mean (q/2) (t/14) 2 14
      (by positivity) (by positivity) (by norm_num)
    calc
      q^2*t^14/14^14 = 4*((q/2)^2*(t/14)^14) := by ring
      _ ≤ 4*((2*(q/2)+14*(t/14))/(2+14))^(2+14) := by exact mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 4*((q+t)/16)^16 := by ring
  have hd14 : d^14 ≤ d^3 := by
    calc d^14 = d^3*d^11 := by ring
         _ ≤ d^3*1^11 := by gcongr
         _ = d^3 := by ring
  have hfirst : ω*P ≤ baseDensity * pathShape h * (1-9*z/400) := by
    calc
      ω*P ≤ (h/12)^12 * (q*t^3*(1/27-z/1200)) :=
        mul_le_mul hωbound hPbound hP (by positivity)
      _ = (h/12)^12 * (q*t^3/27) * (1-9*z/400) := by ring
      _ ≤ (h/12)^12 * ((q+t)/4)^4 * (1-9*z/400) := by gcongr
      _ = baseDensity * pathShape h * (1-9*z/400) := by
        have hqt : q+t = 1-h := by linarith
        rw [hqt]
        unfold baseDensity pathShape
        ring
  have hsecond : q^2*s*(1-s)*δ ≤ baseDensity * z * (4*(1-h)^16) := by
    calc
      q^2*s*(1-s)*δ ≤ q^2*s*(1-s)*(t*d/14)^14 := by gcongr
      _ = (q^2*t^14/14^14) * (s*(1-s)*d^14) := by ring
      _ ≤ (4*((q+t)/16)^16) * (s*(1-s)*d^3) := by
        apply mul_le_mul hqbound' _ (by positivity) (by positivity)
        gcongr
      _ = baseDensity*z*(4*(1-h)^16) := by
        have hqt : q+t = 1-h := by linarith
        rw [hqt]
        unfold baseDensity
        dsimp [z]
        ring
  have hscalar := path_scalar_bound hh (show h ≤ 1 by linarith) hz0 hz1
  calc
    ω*P + q^2*s*(1-s)*δ ≤ baseDensity*pathShape h*(1-9*z/400) +
        baseDensity*z*(4*(1-h)^16) := add_le_add hfirst hsecond
    _ = baseDensity * (pathShape h + z*(4*(1-h)^16-9/400*pathShape h)) := by ring
    _ ≤ baseDensity*1 := mul_le_mul_of_nonneg_left hscalar baseDensity_pos.le
    _ = baseDensity := mul_one _

noncomputable def cubicForm (L : ℕ) (a b : ℕ → ℝ) (c D : ℝ) : ℝ :=
  ∑ i ∈ range L, a i * (b i + c) * ((∑ j ∈ range L, b j) - b i + D)

noncomputable def shiftedCubic (L : ℕ) (a b : ℕ → ℝ) (c D : ℝ) : ℝ :=
  ∑ i ∈ range L, b i * (a (i+1) + c) * ((∑ j ∈ range L, a j) - a (i+1) + D)

lemma cubicForm_scale (L : ℕ) (a b : ℕ → ℝ) (c D k : ℝ) :
    cubicForm L (fun i => k*a i) (fun i => k*b i) (k*c) (k*D) =
      k^3*cubicForm L a b c D := by
  unfold cubicForm
  rw [← mul_sum]
  conv_rhs => rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

lemma shiftedCubic_scale (L : ℕ) (a b : ℕ → ℝ) (c D k : ℝ) :
    shiftedCubic L (fun i => k*a i) (fun i => k*b i) (k*c) (k*D) =
      k^3*shiftedCubic L a b c D := by
  unfold shiftedCubic
  rw [← mul_sum]
  conv_rhs => rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

lemma cubicForm_nonneg (L : ℕ) (a b : ℕ → ℝ) (c D : ℝ)
    (ha : ∀ i < L, 0 ≤ a i) (hb : ∀ i < L, 0 ≤ b i)
    (hc : 0 ≤ c) (hD : 0 ≤ D) : 0 ≤ cubicForm L a b c D := by
  apply sum_nonneg
  intro i hi
  have hi' := mem_range.mp hi
  have hbi : b i ≤ ∑ j ∈ range L, b j :=
    single_le_sum (f := b) (fun j hj => hb j (mem_range.mp hj)) hi
  exact mul_nonneg (mul_nonneg (ha i hi') (add_nonneg (hb i hi') hc)) (by linarith)

lemma shiftedCubic_nonneg (L : ℕ) (a b : ℕ → ℝ) (c D : ℝ)
    (ha : ∀ i < L, 0 ≤ a i) (hb : ∀ i < L, 0 ≤ b i)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hend : a L = 0) : 0 ≤ shiftedCubic L a b c D := by
  apply sum_nonneg
  intro i hi
  have hi' := mem_range.mp hi
  have hA : 0 ≤ ∑ j ∈ range L, a j := sum_nonneg fun j hj => ha j (mem_range.mp hj)
  have hai : 0 ≤ a (i+1) ∧ a (i+1) ≤ ∑ j ∈ range L, a j := by
    by_cases h : i+1 < L
    · exact ⟨ha _ h, single_le_sum (f := a) (fun j hj => ha j (mem_range.mp hj)) (mem_range.mpr h)⟩
    · have heq : i+1 = L := by omega
      simpa [heq, hend] using hA
  exact mul_nonneg (mul_nonneg (hb i hi') (add_nonneg hai.1 hc)) (by linarith [hai.2])

lemma path_cubic_homogeneous (L : ℕ) (a b : ℕ → ℝ) (c D s t : ℝ)
    (ha : ∀ i < L, 0 ≤ a i) (hb : ∀ i < L, 0 ≤ b i)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hend : a L = 0)
    (hmass : (∑ i ∈ range L, a i) + (∑ i ∈ range L, b i) + c + D = t) :
    s*cubicForm L a b c D + (1-s)*shiftedCubic L a b c D ≤
      t^3*(1/27-s*(1-s)*(D/t)^3/1200) := by
  have hA := sum_nonneg (s := range L) (f := a) (fun i hi => ha i (mem_range.mp hi))
  have hB := sum_nonneg (s := range L) (f := b) (fun i hi => hb i (mem_range.mp hi))
  have ht : 0 ≤ t := by linarith
  rcases ht.eq_or_lt with ht0 | htpos
  · have hAz : (∑ i ∈ range L, a i) = 0 := by linarith
    have hBz : (∑ i ∈ range L, b i) = 0 := by linarith
    have haz : ∀ i ∈ range L, a i = 0 := (sum_eq_zero_iff_of_nonneg (fun i hi => ha i (mem_range.mp hi))).mp hAz
    have hbz : ∀ i ∈ range L, b i = 0 := (sum_eq_zero_iff_of_nonneg (fun i hi => hb i (mem_range.mp hi))).mp hBz
    have hp1 : cubicForm L a b c D = 0 := by
      apply sum_eq_zero
      intro i hi
      simp [haz i hi]
    have hp2 : shiftedCubic L a b c D = 0 := by
      apply sum_eq_zero
      intro i hi
      simp [hbz i hi]
    simp [hp1, hp2, ← ht0]
  · have htne : t ≠ 0 := ne_of_gt htpos
    have hnorm := path_cubic_bound L (fun i => (1/t)*a i) (fun i => (1/t)*b i)
      ((1/t)*c) ((1/t)*D) s
      (fun i hi => mul_nonneg (by positivity) (ha i hi))
      (fun i hi => mul_nonneg (by positivity) (hb i hi))
      (by positivity) (by positivity) hs hs1 (by simp [hend])
      (by
        simp only [← mul_sum]
        field_simp
        linarith)
    change s*cubicForm L (fun i => (1/t)*a i) (fun i => (1/t)*b i) ((1/t)*c) ((1/t)*D) +
      (1-s)*shiftedCubic L (fun i => (1/t)*a i) (fun i => (1/t)*b i) ((1/t)*c) ((1/t)*D) ≤ _ at hnorm
    rw [cubicForm_scale, shiftedCubic_scale] at hnorm
    have hout := mul_le_mul_of_nonneg_left hnorm (pow_nonneg ht 3)
    convert hout using 1 <;> first | rfl | (field_simp [htne])

/-- The full weighted polynomial bound for every open path. -/
theorem path_bound (L : ℕ) (a b : ℕ → ℝ) (c u v : ℝ)
    (w : Fin 12 → ℝ) (d : Fin 14 → ℝ)
    (ha : ∀ i < L, 0 ≤ a i) (hb : ∀ i < L, 0 ≤ b i)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : ∀ i, 0 ≤ w i) (hd : ∀ i, 0 ≤ d i) (hend : a L = 0)
    (hmass : (∑ i ∈ range L, a i) + (∑ i ∈ range L, b i) + c + u + v +
      (∑ i, w i) + (∑ i, d i) = 1) :
    (∏ i, w i)*(u*cubicForm L a b c (∑ i, d i) + v*shiftedCubic L a b c (∑ i, d i)) +
      u*v*(∏ i, d i) ≤ baseDensity := by
  let D := ∑ i, d i
  let t := (∑ i ∈ range L, a i) + (∑ i ∈ range L, b i) + c + D
  let q := u+v
  have hD : 0 ≤ D := sum_nonneg fun i hi => hd i
  have ht : 0 ≤ t := by dsimp [t]; exact add_nonneg (add_nonneg
    (add_nonneg (sum_nonneg fun i hi => ha i (mem_range.mp hi))
      (sum_nonneg fun i hi => hb i (mem_range.mp hi))) hc) hD
  have hA : 0 ≤ ∑ i ∈ range L, a i := sum_nonneg fun i hi => ha i (mem_range.mp hi)
  have hB : 0 ≤ ∑ i ∈ range L, b i := sum_nonneg fun i hi => hb i (mem_range.mp hi)
  have hDt : D ≤ t := by dsimp [t]; linarith
  have hq : 0 ≤ q := add_nonneg hu hv
  by_cases hq0 : q = 0
  · have hu0 : u = 0 := by dsimp [q] at hq0; linarith
    have hv0 : v = 0 := by dsimp [q] at hq0; linarith
    simpa [hu0, hv0] using baseDensity_pos.le
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hs0 : 0 ≤ u/q := div_nonneg hu hq
  have hs1 : u/q ≤ 1 := (div_le_one hqpos).mpr (by dsimp [q]; linarith)
  have hs_eq : 1-u/q = v/q := by
    have hvq : v = q-u := by dsimp [q]; ring
    rw [hvq]
    field_simp [hq0]
  have hdn0 : 0 ≤ D/t := div_nonneg hD ht
  have hdn1 : D/t ≤ 1 := by
    rcases ht.eq_or_lt with h | h
    · simp [← h]
    · exact (div_le_one h).mpr hDt
  have hω := prod_le_mean_pow univ w univ_nonempty (fun i hi => hw i)
  have hδ := prod_le_mean_pow univ d univ_nonempty (fun i hi => hd i)
  simp only [card_univ, Fintype.card_fin, Nat.cast_ofNat] at hω hδ
  have htD : t*(D/t) = D := by
    rcases ht.eq_or_lt with h | h
    · have hzero : D = 0 := by linarith
      simp [hzero]
    · field_simp
  have hPc := path_cubic_homogeneous L a b c D (u/q) t ha hb hc hD hs0 hs1 hend rfl
  have hPbound : u*cubicForm L a b c D + v*shiftedCubic L a b c D ≤
      q*t^3*(1/27-(u/q)*(1-u/q)*(D/t)^3/1200) := by
    calc
      _ = q*((u/q)*cubicForm L a b c D + (1-u/q)*shiftedCubic L a b c D) := by
        rw [hs_eq]
        field_simp [hq0]
      _ ≤ q*(t^3*(1/27-(u/q)*(1-u/q)*(D/t)^3/1200)) := mul_le_mul_of_nonneg_left hPc hq
      _ = _ := by ring
  have hresult := path_product_bound (∑ i,w i) q t (D/t) (u/q)
    (∏ i,w i) (∏ i,d i) (u*cubicForm L a b c D + v*shiftedCubic L a b c D)
    (sum_nonneg fun i hi => hw i) hq ht hdn0 hdn1 hs0 hs1
    (by dsimp [q,t,D]; linarith) (prod_nonneg fun i hi => hw i) hω
    (by simpa only [htD] using hδ)
    (add_nonneg (mul_nonneg hu (cubicForm_nonneg L a b c D ha hb hc hD))
      (mul_nonneg hv (shiftedCubic_nonneg L a b c D ha hb hc hD hend))) hPbound
  have huv : q^2*(u/q)*(1-u/q) = u*v := by rw [hs_eq]; field_simp [hq0]
  simpa only [huv] using hresult

end Erdos1075
