import GoldbachCircleMethodActualUnitPairArithmeticV18194
import GoldbachCircleMethodExceptionalModelDiagonalV18107

/-! Actual finite weighted unit-pair lower bound. No global model reserve,
exceptional character existence or Goldbach conclusion is asserted. -/
set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodSmallConductorPairReserveV18108
open GoldbachCircleMethodExceptionalModelDiagonalV18107

namespace GoldbachCircleMethodActualUnitPairWeightedReserveV18195

theorem actual_first_marginal (r : ℕ) [NeZero r] (m : ℤ)
    (chi : DirichletCharacter ℂ r) (hchi : chi.IsPrimitive) :
    (∑ x ∈ unitPairResidues r m, chi x) =
      ((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi (m : ZMod r) := by
  exact primitiveUnitPairMarginal_eq_moebius_mul r chi hchi m

theorem actual_second_marginal (r : ℕ) [NeZero r] (m : ℤ)
    (chi : DirichletCharacter ℂ r) (hchi : chi.IsPrimitive) :
    (∑ x ∈ unitPairResidues r m, chi ((m : ZMod r) - x)) =
      ((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi (m : ZMod r) := by
  have hinv : ∀ x : ZMod r, (m : ZMod r) - ((m : ZMod r) - x) = x := by
    intro x
    ring
  calc
    _ = ∑ y ∈ unitPairResidues r m, chi y := by
      apply Finset.sum_bij (fun x _hx => (m : ZMod r) - x)
      · intro x hx
        rw [mem_unitPairResidues] at hx ⊢
        exact ⟨hx.2, by simpa only [hinv] using hx.1⟩
      · intro x hx y hy h
        have hh := congrArg (fun z : ZMod r => (m : ZMod r) - z) h
        simpa only [hinv] using hh
      · intro y hy
        refine ⟨(m : ZMod r) - y, ?_, hinv y⟩
        rw [mem_unitPairResidues] at hy ⊢
        exact ⟨hy.2, by simpa only [hinv] using hy.1⟩
      · intro x _hx
        rfl
    _ = _ := actual_first_marginal r m chi hchi

theorem self_inverse_character_im_zero (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (hInv : chi⁻¹ = chi) (x : ZMod r) :
    (chi x).im = 0 := by
  by_cases hx : IsUnit x
  · have hs := quadratic_value_square r chi hInv x
    rw [if_pos hx] at hs
    rcases mul_self_eq_one_iff.mp hs with h | h <;> simp [h]
  · rw [MulChar.map_nonunit chi hx]
    rfl

/-- Elementary pointwise inequality; its inputs will be real character values. -/
theorem product_factor_lower (x y w1 w2 t : ℝ)
    (hx : x ≤ 1) (hy : y ≤ 1)
    (hw1 : 0 ≤ w1) (hw1t : w1 ≤ t)
    (hw2 : 0 ≤ w2) (hw2t : w2 ≤ t) (ht : t ≤ 1) :
    (1-t)*(1-w2*y) ≤ (1-w1*x)*(1-w2*y) := by
  have hw1x : w1*x ≤ t :=
    (mul_le_mul_of_nonneg_left hx hw1).trans (by simpa using hw1t)
  have hw2y : w2*y ≤ 1 :=
    (mul_le_mul_of_nonneg_left hy hw2).trans
      (by simpa using hw2t.trans ht)
  exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)

/-- Exact actual-carrier weighted lower bound with the first marginal retained.
No denominator bound, residue independence or exceptional-zero fact is assumed. -/
theorem actual_weighted_unit_pair_lower (r : ℕ) [NeZero r] (m : ℤ)
    (chi : DirichletCharacter ℂ r) (hchi : chi.IsPrimitive)
    (hInv : chi⁻¹ = chi) (w1 w2 t : ℝ)
    (hw1 : 0 ≤ w1) (hw1t : w1 ≤ t)
    (hw2 : 0 ≤ w2) (hw2t : w2 ≤ t) (ht : t ≤ 1) :
    (1-t)*((unitPairCount r m : ℝ) -
      w2 * (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
        chi (m : ZMod r)).re) ≤
      (∑ x ∈ unitPairResidues r m,
        (1-(w1 : ℂ)*chi x) *
          (1-(w2 : ℂ)*chi ((m : ZMod r)-x))).re := by
  have him := self_inverse_character_im_zero r chi hInv
  have hre (x : ZMod r) : (chi x).re ≤ 1 :=
    (Complex.re_le_norm _).trans (chi.norm_le_one x)
  have hreal (x : ZMod r) :
      ((1-(w1 : ℂ)*chi x) * (1-(w2 : ℂ)*chi ((m : ZMod r)-x))).re =
        (1-w1*(chi x).re) * (1-w2*(chi ((m : ZMod r)-x)).re) := by
    simp [Complex.mul_re, Complex.mul_im, him]
  have hsum :
      (∑ x ∈ unitPairResidues r m, (1-t)*(1-w2*(chi ((m : ZMod r)-x)).re)) =
        (1-t)*((unitPairCount r m : ℝ) -
          w2 * (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
            chi (m : ZMod r)).re) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Complex.re_sum, actual_second_marginal r m chi hchi]
    simp [unitPairCount]
  rw [← hsum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro x _hx
  rw [hreal]
  exact product_factor_lower _ _ _ _ _ (hre x) (hre _) hw1 hw1t hw2 hw2t ht

/-- The actual primitive marginal has norm at most one, including its zero cases. -/
theorem actual_primitive_marginal_norm_le_one (r : ℕ) [NeZero r] (m : ℤ)
    (chi : DirichletCharacter ℂ r) :
    ‖((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi (m : ZMod r)‖ ≤ 1 := by
  by_cases hmu : ArithmeticFunction.moebius r = 0
  · simp [hmu]
  · rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp hmu with h | h
    · simpa [h] using chi.norm_le_one (m : ZMod r)
    · simpa [h] using chi.norm_le_one (m : ZMod r)

/-- Actual finite reserve for every modulus r>3 and even target m.
If the first marginal is nonzero, squarefreeness and target coprimality
are derived, not assumed. This is not yet the supported model convolution. -/
theorem actual_weighted_unit_pair_reserve
    (r m : ℕ) [NeZero r] (hr3 : 3 < r) (hm : Even m)
    (chi : DirichletCharacter ℂ r) (hchi : chi.IsPrimitive)
    (hInv : chi⁻¹ = chi) (w1 w2 t : ℝ)
    (hw1 : 0 ≤ w1) (hw1t : w1 ≤ t)
    (hw2 : 0 ≤ w2) (hw2t : w2 ≤ t) (ht : t ≤ 1) :
    (2/3 : ℝ) * (unitPairCount r (m : ℤ) : ℝ) * (1-t) ≤
      (∑ x ∈ unitPairResidues r (m : ℤ),
        (1-(w1 : ℂ)*chi x) *
          (1-(w2 : ℂ)*chi (((m : ℤ) : ZMod r)-x))).re := by
  let z : ℂ := ((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi (m : ZMod r)
  have hbase := actual_weighted_unit_pair_lower r (m : ℤ) chi hchi hInv
    w1 w2 t hw1 hw1t hw2 hw2t ht
  have hnonneg : 0 ≤ (unitPairCount r (m : ℤ) : ℝ) := Nat.cast_nonneg _
  have hbudget : (2/3 : ℝ) * (unitPairCount r (m : ℤ) : ℝ) ≤
      (unitPairCount r (m : ℤ) : ℝ) - w2 * z.re := by
    by_cases hz : z = 0
    · simp only [hz, Complex.zero_re, mul_zero, sub_zero]
      linarith
    · have hmu : ArithmeticFunction.moebius r ≠ 0 := by
        intro h
        exact hz (by simp [z, h])
      have hchar : chi (m : ZMod r) ≠ 0 := by
        intro h
        exact hz (by simp [z, h])
      have hsq : Squarefree r := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
      have hcop : m.Coprime r :=
        (ZMod.isUnit_iff_coprime m r).mp (MulChar.apply_ne_zero_iff.mp hchar)
      have hcount : (3 : ℝ) ≤ (unitPairCount r (m : ℤ) : ℝ) := by
        exact_mod_cast three_le_unitPairCount_of_squarefree_coprime_even
          (NeZero.ne r) hm hsq hcop hr3
      have hzre : z.re ≤ 1 :=
        (Complex.re_le_norm z).trans (by
          simpa [z] using actual_primitive_marginal_norm_le_one r (m : ℤ) chi)
      have hwz : w2 * z.re ≤ 1 :=
        (mul_le_mul_of_nonneg_left hzre hw2).trans (by simpa using hw2t.trans ht)
      linarith
  have h := mul_le_mul_of_nonneg_left hbudget (sub_nonneg.mpr ht)
  calc
    _ = (1-t) * ((2/3 : ℝ) * (unitPairCount r (m : ℤ) : ℝ)) := by ring
    _ ≤ (1-t) * ((unitPairCount r (m : ℤ) : ℝ) - w2 * z.re) := h
    _ ≤ _ := by simpa [z] using hbase

/-- A numerical exponential gap estimate with its nonnegative domain explicit. -/
theorem one_sub_exp_neg_lower (x : ℝ) (hx : 0 ≤ x) :
    min 1 x / 2 ≤ 1 - Real.exp (-x) := by
  have hx1 : 0 < 1+x := by linarith
  have he : 1+x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hi : Real.exp (-x) ≤ 1/(1+x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hx1 he
  have hfrac : min 1 x / 2 ≤ x/(1+x) := by
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<2) hx1).mpr
    by_cases h : x ≤ 1
    · rw [min_eq_right h]
      nlinarith [mul_nonneg hx (sub_nonneg.mpr h)]
    · rw [min_eq_left (le_of_not_ge h)]
      linarith
  have hid : x/(1+x) = 1-1/(1+x) := by
    field_simp
    ring
  rw [hid] at hfrac
  linarith

/-- The literal block power gap dominates a quarter of the declared theta. -/
theorem block_power_gap_lower (B b : ℝ) (hB : 4 ≤ B) (hb : 0 ≤ b) :
    min 1 (b * Real.log B) / 4 ≤ 1 - (B/2)^(-b) := by
  have hBpos : 0 < B := by linarith
  have hhalf : (2:ℝ) ≤ B/2 := by linarith
  have hhpos : 0 < B/2 := by linarith
  have hlog : Real.log B ≤ 2 * Real.log (B/2) := by
    have hlog2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hhalf
    rw [Real.log_div hBpos.ne' (by norm_num)] at hlog2 ⊢
    linarith
  have hx : 0 ≤ b * Real.log (B/2) :=
    mul_nonneg hb (Real.log_nonneg (by linarith))
  have hm : min 1 (b * Real.log B) / 2 ≤ min 1 (b * Real.log (B/2)) := by
    apply le_min
    · have h := min_le_left (1:ℝ) (b * Real.log B)
      linarith
    · have h := mul_le_mul_of_nonneg_left hlog hb
      have hmin := min_le_right (1:ℝ) (b * Real.log B)
      linarith
  have hg := one_sub_exp_neg_lower (b * Real.log (B/2)) hx
  have hp : (B/2)^(-b) = Real.exp (-(b * Real.log (B/2))) := by
    rw [Real.rpow_def_of_pos hhpos]
    congr 1
    ring
  rw [hp]
  linarith

/-- The concrete n^(-b) weights on the actual block satisfy the finite
unit-pair reserve with theta=min(1,b log B). A positive b is retained in
the signature; this does not assert existence of an exceptional zero. -/
theorem actual_block_power_unit_pair_reserve
    (r m B n u : ℕ) [NeZero r] (hr3 : 3 < r) (hm : Even m)
    (hB : 4 ≤ B)
    (hn : n ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hu : u ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (chi : DirichletCharacter ℂ r) (hchi : chi.IsPrimitive)
    (hInv : chi⁻¹ = chi) (b : ℝ) (hb : 0 < b) :
    (unitPairCount r (m : ℤ) : ℝ) * min 1 (b * Real.log B) / 6 ≤
      (∑ x ∈ unitPairResidues r (m : ℤ),
        (1-(((n : ℝ)^(-b) : ℝ) : ℂ)*chi x) *
          (1-(((u : ℝ)^(-b) : ℝ) : ℂ)*chi (((m : ℤ) : ZMod r)-x))).re := by
  have hB' : (4:ℝ) ≤ B := by exact_mod_cast hB
  have hhpos : (0:ℝ) < (B:ℝ)/2 := by linarith
  have hdom (v : ℕ)
      (hv : v ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B) :
      (B:ℝ)/2 ≤ v := by
    have hh := (GoldbachCircleMethodLogCutoffPresieveBindingV18120.mem_blockCarrier B v).mp hv
    have hreal : (B:ℝ) < 2*(v:ℝ) := by exact_mod_cast hh.1
    linarith
  have ht : ((B:ℝ)/2)^(-b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hnwt : (n:ℝ)^(-b) ≤ ((B:ℝ)/2)^(-b) :=
    Real.rpow_le_rpow_of_nonpos hhpos (hdom n hn) (by linarith)
  have huwt : (u:ℝ)^(-b) ≤ ((B:ℝ)/2)^(-b) :=
    Real.rpow_le_rpow_of_nonpos hhpos (hdom u hu) (by linarith)
  have hres := actual_weighted_unit_pair_reserve r m hr3 hm chi hchi hInv
    ((n:ℝ)^(-b)) ((u:ℝ)^(-b)) (((B:ℝ)/2)^(-b))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hnwt
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) huwt ht
  have hgap := mul_le_mul_of_nonneg_left
    (block_power_gap_lower (B:ℝ) b hB' hb.le)
    (show 0 ≤ (2/3:ℝ)*(unitPairCount r (m:ℤ):ℝ) by positivity)
  calc
    _ = (2/3:ℝ)*(unitPairCount r (m:ℤ):ℝ)*(min 1 (b*Real.log B)/4) := by ring
    _ ≤ _ := hgap
    _ ≤ _ := hres

end GoldbachCircleMethodActualUnitPairWeightedReserveV18195
