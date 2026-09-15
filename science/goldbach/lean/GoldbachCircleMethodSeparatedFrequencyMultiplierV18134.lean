import GoldbachCircleMethodSignedDirichletMultiplierV18133

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodSignedWindowFourierAdapterV18130
open GoldbachCircleMethodSignedDirichletMultiplierV18133
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodOriginalMaskDisjointnessV1860
open GoldbachCircleMethodFiniteAbelAdapterV1863

namespace GoldbachCircleMethodSeparatedFrequencyMultiplierV18134

theorem complex_sum_range_residues (q : ℕ) [NeZero q] (g : ZMod q → ℂ) :
    (∑ n ∈ Finset.range q, g (n : ZMod q)) = ∑ a : ZMod q, g a := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ZMod q))
  · intro n _
    exact Finset.mem_univ _
  · intro n hn l hl he
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hn),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hl)] using hv
  · intro a _
    exact ⟨a.val, Finset.mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
  · intro n _
    rfl

theorem unit_residues_as_natural_range (q Q : ℕ) [NeZero q] (hq : q ≤ Q)
    (F : ℕ → ℂ) :
    (∑ a : ZMod q, if IsUnit a then F a.val else 0) =
      ∑ a ∈ Finset.range Q, if a<q ∧ Nat.Coprime a q then F a else 0 := by
  rw [← complex_sum_range_residues q (fun a => if IsUnit a then F a.val else 0)]
  have he : (∑ n ∈ Finset.range q, if IsUnit (n : ZMod q) then F (n : ZMod q).val else 0) =
      ∑ n ∈ Finset.range q, if n<q ∧ Nat.Coprime n q then F n else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnq := Finset.mem_range.mp hn
    simp [ZMod.isUnit_iff_coprime, ZMod.val_natCast, Nat.mod_eq_of_lt hnq, hnq]
  rw [he]
  apply Finset.sum_subset (Finset.range_mono hq)
  intro n _ hn
  simp only [Finset.mem_range] at hn
  simp [hn]

/-- Only a reindexing of the actual all-modulus, all-unit multiplier. -/
theorem signed_multiplier_reduced_centers (Q : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (w : ℕ → ℂ) (x : UnitAddCircle) :
    (∑ k ∈ shiftCarrier H, signedWindowKernel Q H w k * fourier k x) =
      ∑ i : ReducedRationalIndex Q, w i.val.1 *
        normalizedDirichlet H (x+majorArcCenter i) := by
  rw [signed_kernel_fourier_multiplier_formula Q H hH w x]
  have he : (∑ q : PositiveLevel Q, w q.val * ∑ a : ZMod q.val,
      if IsUnit a then normalizedDirichlet H
        (x+(((a.val : ℝ)/(q.val : ℝ) : ℝ) : UnitAddCircle)) else 0) =
      ∑ q : PositiveLevel Q, w q.val * ∑ a ∈ Finset.range Q,
        if a<q.val ∧ Nat.Coprime a q.val then
          normalizedDirichlet H (x+(((a : ℝ)/(q.val : ℝ) : ℝ) : UnitAddCircle))
        else 0 := by
    apply Finset.sum_congr rfl
    intro q _
    rw [unit_residues_as_natural_range q.val Q (Finset.mem_Icc.mp q.property).2
      (fun a : ℕ => normalizedDirichlet H
        (x+(((a : ℝ)/(q.val : ℝ) : ℝ) : UnitAddCircle)))]
  rw [he]
  unfold majorArcCenter
  change (∑ q : ↥(Finset.Icc 1 Q), w q.val * ∑ a ∈ Finset.range Q,
      if a<q.val ∧ Nat.Coprime a q.val then
        normalizedDirichlet H (x+(((a : ℝ)/(q.val : ℝ) : ℝ) : UnitAddCircle)) else 0) = _
  rw [Finset.sum_coe_sort (Finset.Icc 1 Q) (fun q : ℕ =>
    w q * ∑ a ∈ Finset.range Q, if a<q ∧ Nat.Coprime a q then
      normalizedDirichlet H (x+(((a : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle)) else 0)]
  rw [Finset.sum_coe_sort (reducedRationalPairs Q) (fun qa : ℕ×ℕ =>
    w qa.1 * normalizedDirichlet H
      (x+(((qa.2 : ℝ)/(qa.1 : ℝ) : ℝ) : UnitAddCircle)))]
  unfold reducedRationalPairs
  rw [Finset.sum_filter, Finset.product_eq_sprod]
  rw [Finset.sum_product (Finset.Icc 1 Q) (Finset.range Q) (fun qa : ℕ×ℕ =>
    if qa.2<qa.1 ∧ Nat.Coprime qa.2 qa.1 then w qa.1 * normalizedDirichlet H
      (x+(((qa.2 : ℝ)/(qa.1 : ℝ) : ℝ) : UnitAddCircle)) else 0)]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a<q ∧ Nat.Coprime a q
  · simp [ha]
  · simp [ha]

theorem reduced_center_count (Q : ℕ) :
    Fintype.card (ReducedRationalIndex Q) ≤ Q^2 := by
  rw [Fintype.card_coe]
  unfold reducedRationalPairs
  apply (Finset.card_filter_le _ _).trans
  simp [Finset.card_product, Nat.card_Icc, pow_two]

theorem center_denominator_le (Q : ℕ) (i : ReducedRationalIndex Q) :
    i.val.1 ≤ Q :=
  (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp i.property).1).1).2

theorem uniform_center_separation (Q : ℕ)
    (i j : ReducedRationalIndex Q) (hij : i≠j) :
    1/(Q : ℝ)^2 ≤ dist (majorArcCenter i) (majorArcCenter j) := by
  have hi : (0 : ℝ) < i.val.1 := by exact_mod_cast index_denominator_pos i
  have hj : (0 : ℝ) < j.val.1 := by exact_mod_cast index_denominator_pos j
  have hib : (i.val.1 : ℝ)≤Q := by exact_mod_cast center_denominator_le Q i
  have hjb : (j.val.1 : ℝ)≤Q := by exact_mod_cast center_denominator_le Q j
  apply (one_div_le_one_div_of_le (mul_pos hi hj) ?_).trans
    (distinct_centers_distance_lower Q i j hij)
  nlinarith

theorem torus_norm_lift (x : UnitAddCircle) :
    ∃ β : ℝ, (β : UnitAddCircle)=x ∧ |β|=‖x‖ ∧ |β|≤1/2 := by
  have hn : ‖x‖≤1/2 := by
    simpa using AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := x) (by norm_num)
  have hx : x ∈ Metric.closedBall (0 : UnitAddCircle) (1/2 : ℝ) := by
    simpa using hn
  obtain ⟨β,hβ,he⟩ := closedBall_real_lift 0 x (1/2) hx
  have he' : (β : UnitAddCircle)=x := by simpa using he.symm
  have hab : ‖(β : UnitAddCircle)‖=|β| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hβ)
  exact ⟨β,he',by rw [←he',hab],hβ⟩

theorem dirichlet_norm_off_zero_torus (H : ℝ) (hH : 0<H) (x : UnitAddCircle)
    (hx : 0<‖x‖) : ‖normalizedDirichlet H x‖≤1/(4*H*‖x‖) := by
  obtain ⟨β,he,hn,hb⟩ := torus_norm_lift x
  rw [←hn,←he]
  exact normalized_dirichlet_off_zero H hH β (by rwa [hn]) hb

theorem dirichlet_error_torus (H : ℝ) (hH : 1≤H) (x : UnitAddCircle) :
    ‖normalizedDirichlet H x-1‖≤1/(2*H)+3*Real.pi*H*‖x‖ := by
  obtain ⟨β,he,hn,_⟩ := torus_norm_lift x
  rw [←hn,←he]
  exact normalized_dirichlet_error_le H hH β

theorem shifted_center_norm (Q : ℕ) (x : UnitAddCircle) (i : ReducedRationalIndex Q) :
    ‖x+majorArcCenter i‖=dist (-x) (majorArcCenter i) := by
  rw [dist_eq_norm]
  have he : -x-majorArcCenter i=-(x+majorArcCenter i) := by abel
  rw [he,norm_neg]

/-- Nearest-frequency geometry alone; no prime estimate enters. -/
theorem nearest_other_distance (Q : ℕ) (x : UnitAddCircle)
    (i j : ReducedRationalIndex Q) (hij : i≠j)
    (hi : dist (-x) (majorArcCenter i)≤dist (-x) (majorArcCenter j)) :
    1/(2*(Q : ℝ)^2) ≤ ‖x+majorArcCenter j‖ := by
  rw [shifted_center_norm]
  have hs := uniform_center_separation Q i j hij
  have ht := dist_triangle (majorArcCenter i) (-x) (majorArcCenter j)
  rw [dist_comm (majorArcCenter i) (-x)] at ht
  have hid : 1/(2*(Q : ℝ)^2)=(1/(Q : ℝ)^2)/2 := by ring
  rw [hid]
  linarith

/-- The same separation applies near any specified center inside half the gap. -/
theorem near_center_other_distance (Q : ℕ) (x : UnitAddCircle)
    (i j : ReducedRationalIndex Q) (hij : i≠j)
    (hi : ‖x+majorArcCenter i‖≤1/(2*(Q : ℝ)^2)) :
    1/(2*(Q : ℝ)^2) ≤ ‖x+majorArcCenter j‖ := by
  rw [shifted_center_norm] at hi ⊢
  have hs := uniform_center_separation Q i j hij
  have ht := dist_triangle (majorArcCenter i) (-x) (majorArcCenter j)
  rw [dist_comm (majorArcCenter i) (-x)] at ht
  have hid : 1/(2*(Q : ℝ)^2)=(1/(Q : ℝ)^2)/2 := by ring
  rw [hid] at hi ⊢
  linarith


/-- Explicit nonresonant pointwise estimate from the finite separation. -/
theorem separated_dirichlet_norm_le (Q : ℕ) (hQ : 0<Q) (H : ℝ) (hH : 0<H)
    (y : UnitAddCircle) (hy : 1/(2*(Q : ℝ)^2)≤‖y‖) :
    ‖normalizedDirichlet H y‖≤(Q : ℝ)^2/(2*H) := by
  have hq : (0 : ℝ)<Q := by exact_mod_cast hQ
  have ht : 0<1/(2*(Q : ℝ)^2) := by positivity
  have hy0 := ht.trans_le hy
  apply (dirichlet_norm_off_zero_torus H hH y hy0).trans
  calc
    _ ≤ 1/(4*H*(1/(2*(Q : ℝ)^2))) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left hy (by positivity))
    _ = _ := by field_simp; ring

/-- A conservative all-frequency remainder. No harmonic packing claim is needed. -/
theorem other_frequency_mass_le (Q : ℕ) (hQ : 0<Q) (H : ℝ) (hH : 0<H)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0≤M) (x : UnitAddCircle)
    (i : ReducedRationalIndex Q)
    (hw : ∀ j : ReducedRationalIndex Q, ‖w j.val.1‖≤M)
    (hsep : ∀ j : ReducedRationalIndex Q, j≠i →
      1/(2*(Q : ℝ)^2)≤‖x+majorArcCenter j‖) :
    (∑ j ∈ Finset.univ.erase i, ‖w j.val.1 *
      normalizedDirichlet H (x+majorArcCenter j)‖) ≤ M*(Q : ℝ)^4/(2*H) := by
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, M*((Q : ℝ)^2/(2*H)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hw j)
        (separated_dirichlet_norm_le Q hQ H hH _ (hsep j (Finset.mem_erase.mp hj).1))
        (norm_nonneg _) hM
    _ = ((Finset.univ.erase i).card : ℝ)*(M*((Q : ℝ)^2/(2*H))) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (Q : ℝ)^2*(M*((Q : ℝ)^2/(2*H))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_erase_le (a := i)
        (s := (Finset.univ : Finset (ReducedRationalIndex Q)))).trans
        (by simpa using reduced_center_count Q)
    _ = _ := by ring

theorem reduced_center_nonempty (Q : ℕ) (hQ : 0<Q) :
    Nonempty (ReducedRationalIndex Q) := by
  refine ⟨⟨(1,0),?_⟩⟩
  simp [reducedRationalPairs, Finset.mem_Icc, Finset.mem_range, hQ, Nat.succ_le_iff.mpr hQ]

/-- Actual finite-window multiplier bound, uniform in every frequency. -/
theorem actual_multiplier_global_bound (Q : ℕ) (hQ : 0<Q) (H : ℝ) (hH : 1≤H)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0≤M)
    (hw : ∀ j : ReducedRationalIndex Q, ‖w j.val.1‖≤M) (x : UnitAddCircle) :
    ‖∑ k ∈ shiftCarrier H, signedWindowKernel Q H w k * fourier k x‖ ≤
      (3/2)*M+M*(Q : ℝ)^4/(2*H) := by
  rw [signed_multiplier_reduced_centers Q H (by linarith) w x]
  obtain ⟨base⟩ := reduced_center_nonempty Q hQ
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ
    (fun j : ReducedRationalIndex Q => dist (-x) (majorArcCenter j))
    ⟨base,Finset.mem_univ _⟩
  have hm := other_frequency_mass_le Q hQ H (by linarith) w M hM x i hw
    (fun j hji => nearest_other_distance Q x i j hji.symm (hi j (Finset.mem_univ _)))
  have ht : ‖w i.val.1*normalizedDirichlet H (x+majorArcCenter i)‖≤(3/2)*M := by
    rw [norm_mul]
    have hb := mul_le_mul (hw i) (normalized_dirichlet_norm_le_three_halves H hH
      (x+majorArcCenter i))
      (norm_nonneg _) hM
    nlinarith
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  exact (norm_add_le _ _).trans (by
    linarith [(norm_sum_le _ _).trans hm])

/-- Near a specified reduced center whose weight is exactly one.
The half-gap restriction and normalization error remain explicit. -/
theorem actual_multiplier_near_center (Q : ℕ) (hQ : 0<Q) (H : ℝ) (hH : 1≤H)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0≤M) (x : UnitAddCircle)
    (i : ReducedRationalIndex Q)
    (hw : ∀ j : ReducedRationalIndex Q, ‖w j.val.1‖≤M) (hwi : w i.val.1=1)
    (hi : ‖x+majorArcCenter i‖≤1/(2*(Q : ℝ)^2)) :
    ‖(∑ k ∈ shiftCarrier H, signedWindowKernel Q H w k * fourier k x)-1‖ ≤
      1/(2*H)+3*Real.pi*H*‖x+majorArcCenter i‖+M*(Q : ℝ)^4/(2*H) := by
  rw [signed_multiplier_reduced_centers Q H (by linarith) w x]
  have hm := other_frequency_mass_le Q hQ H (by linarith) w M hM x i hw
    (fun j hji => near_center_other_distance Q x i j hji.symm hi)
  have ht := dirichlet_error_torus H hH (x+majorArcCenter i)
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),hwi,one_mul]
  rw [add_sub_assoc]
  exact (norm_add_le _ _).trans (by
    linarith [(norm_sum_le _ _).trans hm])

end GoldbachCircleMethodSeparatedFrequencyMultiplierV18134
