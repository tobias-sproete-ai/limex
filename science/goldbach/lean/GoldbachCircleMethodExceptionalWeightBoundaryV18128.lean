import GoldbachCircleMethodActualCenteredResidualAssemblyV18127
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodRemovedConvolutionNormV18123
open GoldbachCircleMethodExactPrincipalBoundaryCostV18126

namespace GoldbachCircleMethodExceptionalWeightBoundaryV18128

/-- Counts the actual conductor-dependent cutoff, with no rectangular enlargement. -/
theorem companion_level_count_le (Q : ℕ) (r : PositiveLevel Q) :
    (Finset.univ.filter (fun l : PositiveLevel Q => r.val*l.val ≤ Q)).card ≤ Q/r.val := by
  let S := Finset.univ.filter (fun l : PositiveLevel Q => r.val*l.val ≤ Q)
  have hs : S.image (fun l => l.val) ⊆ Finset.Icc 1 (Q/r.val) := by
    intro l hl
    rcases Finset.mem_image.mp hl with ⟨t, ht, rfl⟩
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp t.property).1,
      (product_cutoff_iff_quotient r t).mp (Finset.mem_filter.mp ht).2⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ Subtype.val_injective, Nat.card_Icc] at hc
  simpa only [Nat.add_sub_cancel] using hc

theorem finite_companion_norm_le_quotient (Q N : ℕ) (r : PositiveLevel Q)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M) :
    ‖finiteCompanion r N w‖ ≤ M*(Q/r.val : ℕ) := by
  unfold finiteCompanion
  calc
    _ ≤ ∑ l : PositiveLevel Q, ‖if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val
        then ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
          unitCharacterSum l.val (N : ZMod l.val) / (l.val.totient : ℂ) *
            w (r.val*l.val) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ l : PositiveLevel Q, if r.val*l.val ≤ Q then M else 0 := by
      apply Finset.sum_le_sum
      intro l _
      by_cases hc : r.val*l.val ≤ Q
      · simp only [hc, if_true, true_and]
        split_ifs
        · rw [norm_mul]
          exact (mul_le_mul (moebius_character_quotient_norm_le_one l.val _)
            (hw _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
        · simpa only [norm_zero] using hM
      · simp only [hc, false_and, if_false, norm_zero, le_refl]
    _ = ((Finset.univ.filter (fun l : PositiveLevel Q => r.val*l.val ≤ Q)).card : ℝ)*M := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q/r.val : ℕ)*M :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (companion_level_count_le Q r)) hM
    _ = _ := by ring

/-- Conductor compensation uses the true coupled cutoff, not a loss of r. -/
theorem window_coefficient_norm_le_linear (Q N : ℕ) (r : PositiveLevel Q)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive}) :
    ‖windowCoefficient r N w χ‖ ≤ M*(Q : ℝ) := by
  have hrpos : 0 < r.val := Nat.pos_of_ne_zero (NeZero.ne r.val)
  have ht : (1 : ℝ) ≤ r.val.totient := by exact_mod_cast Nat.totient_pos.mpr hrpos
  have hr : ‖(r.val : ℂ)/(r.val.totient : ℂ)‖ ≤ (r.val : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg r.val) ht
  have hm : ((Q/r.val : ℕ) : ℝ)*(r.val : ℝ) ≤ Q := by
    exact_mod_cast (Nat.le_div_iff_mul_le hrpos).mp (le_refl (Q/r.val))
  unfold windowCoefficient
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ((r.val : ℝ)*1)*(M*(Q/r.val : ℕ)) :=
      mul_le_mul (mul_le_mul hr (χ.val.norm_le_one _) (norm_nonneg _) (by positivity))
        (finite_companion_norm_le_quotient Q N r w M hM hw) (norm_nonneg _) (by positivity)
    _ = M*(((Q/r.val : ℕ) : ℝ)*(r.val : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm hM

/-- The actual power weight with an explicit nonnegative zero gap. -/
noncomputable def powerWeight (b : ℝ) (n : ℕ) : ℝ := (n : ℝ)^(-b)

theorem power_derivative_bound (B b x : ℝ) (hB : 2 ≤ B) (hb : 0 ≤ b)
    (hx : B/2 ≤ x) :
    ‖(-b)*x^(-b-1)‖ ≤ 2*b/B := by
  have hx1 : 1 ≤ x := by linarith
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hBpos : 0 < B := by linarith
  have hp : x^(-b-1) ≤ x^(-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hi : x⁻¹ ≤ 2/B := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < B/2) hx
    simpa only [one_div, inv_div] using hh
  rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hb,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  calc
    _ ≤ b*x^(-(1 : ℝ)) := mul_le_mul_of_nonneg_left hp hb
    _ ≤ b*(2/B) := by
      rw [Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left hi hb
    _ = _ := by ring

/-- A genuine mean-value estimate for n^(-b), not an assumed Lipschitz contract. -/
theorem power_weight_variation (B : ℕ) (hB : 2 ≤ B) (b : ℝ) (hb : 0 ≤ b)
    (N U : ℕ) (hN : N ∈ blockCarrier B) (hU : U ∈ blockCarrier B) :
    |powerWeight b U-powerWeight b N| ≤
      (2*b/(B : ℝ))*|(U : ℝ)-(N : ℝ)| := by
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hn : (B : ℝ)/2 ≤ N := by
    have hh := (mem_blockCarrier B N).mp hN
    have hh' : (B : ℝ) < 2*(N : ℝ) := by exact_mod_cast hh.1
    linarith
  have hu : (B : ℝ)/2 ≤ U := by
    have hh := (mem_blockCarrier B U).mp hU
    have hh' : (B : ℝ) < 2*(U : ℝ) := by exact_mod_cast hh.1
    linarith
  have hd : ∀ x ∈ Set.Ici ((B : ℝ)/2),
      HasDerivWithinAt (fun x : ℝ => x^(-b)) ((-b)*x^(-b-1))
        (Set.Ici ((B : ℝ)/2)) x := by
    intro x hx
    apply (Real.hasDerivAt_rpow_const (Or.inl (show x ≠ 0 by
      have : (B : ℝ)/2 ≤ x := hx
      linarith))).hasDerivWithinAt
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun x hx => power_derivative_bound (B : ℝ) b x hB' hb hx)
    (convex_Ici ((B : ℝ)/2)) hn hu
  simpa only [powerWeight, Real.norm_eq_abs] using hh


theorem power_weight_abs_le_one (B N : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hN : N ∈ blockCarrier B) :
    |powerWeight b N| ≤ 1 := by
  have hn : 1 ≤ N := by
    have hh := Finset.mem_Ioc.mp hN
    omega
  unfold powerWeight
  rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

noncomputable def normalizedPowerWindow (B N : ℕ) (H b : ℝ) : ℝ :=
  (2*H)⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H, powerWeight b U

theorem power_window_difference_identity (B N : ℕ) (H b : ℝ) :
    normalizedPowerWindow B N H b - powerWeight b N =
      boundaryFactor B N H * powerWeight b N +
      (2*H)⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
        (powerWeight b U-powerWeight b N) := by
  unfold normalizedPowerWindow boundaryFactor
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Clipping and smooth-weight variation remain two separate costs. -/
theorem power_window_difference_le (B : ℕ) (hB : 2 ≤ B) (N : ℕ)
    (hN : N ∈ blockCarrier B) (H : ℝ) (hH : 1 ≤ H) (b : ℝ) (hb : 0 ≤ b) :
    |normalizedPowerWindow B N H b-powerWeight b N| ≤
      |boundaryFactor B N H|+3*b*H/(B : ℝ) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hk : ((centeredWindow (blockCarrier B) N H).card : ℝ) ≤ 3*H := by
    have hh : ((centeredWindow (blockCarrier B) N H).card : ℝ) ≤
        2*(⌊H⌋₊ : ℝ)+1 := by exact_mod_cast centered_window_card_le B N H hHpos.le
    linarith [Nat.floor_le hHpos.le]
  have hv (U : ℕ) (hU : U ∈ centeredWindow (blockCarrier B) N H) :
      |powerWeight b U-powerWeight b N| ≤ (2*b/(B : ℝ))*H := by
    rcases Finset.mem_filter.mp hU with ⟨hUJ, hdist⟩
    apply (power_weight_variation B hB b hb N U hN hUJ).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [abs_sub_comm] using hdist
  have he :
      |(2*H)⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
        (powerWeight b U-powerWeight b N)| ≤ 3*b*H/(B : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2*H)⁻¹)]
    calc
      _ ≤ (2*H)⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
          |powerWeight b U-powerWeight b N| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (2*H)⁻¹ * ∑ _U ∈ centeredWindow (blockCarrier B) N H,
          ((2*b/(B : ℝ))*H) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hv) (by positivity)
      _ = (2*H)⁻¹ * (((centeredWindow (blockCarrier B) N H).card : ℝ)*
          ((2*b/(B : ℝ))*H)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2*H)⁻¹ * (3*H*((2*b/(B : ℝ))*H)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hk (by positivity)) (by positivity)
      _ = _ := by field_simp
  rw [power_window_difference_identity]
  calc
    _ ≤ |boundaryFactor B N H * powerWeight b N| +
        |(2*H)⁻¹ * ∑ U ∈ centeredWindow (blockCarrier B) N H,
          (powerWeight b U-powerWeight b N)| := abs_add_le _ _
    _ ≤ |boundaryFactor B N H|+3*b*H/(B : ℝ) := by
      apply add_le_add _ he
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left
        (power_weight_abs_le_one B N b hb hN) (abs_nonneg _)).trans_eq (mul_one _)

theorem power_window_difference_mass_le (B : ℕ) (hB : 2 ≤ B) (H : ℝ) (hH : 1 ≤ H)
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (∑ N ∈ blockCarrier B, |normalizedPowerWindow B N H b-powerWeight b N|) ≤
      5*H+(B : ℝ)/(2*H) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  calc
    _ ≤ ∑ N ∈ blockCarrier B, (|boundaryFactor B N H|+3*b*H/(B : ℝ)) :=
      Finset.sum_le_sum (fun N hN => power_window_difference_le B hB N hN H hH b hb)
    _ = (∑ N ∈ blockCarrier B, |boundaryFactor B N H|) +
        ((blockCarrier B).card : ℝ)*(3*b*H/(B : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2*H+(B : ℝ)/(2*H))+(B : ℝ)*(3*b*H/(B : ℝ)) :=
      add_le_add (boundary_factor_mass_le B H hH)
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (block_carrier_card_le B)) (by positivity))
    _ = (2*H+(B : ℝ)/(2*H))+3*b*H := by field_simp
    _ ≤ _ := by nlinarith

/-- The active exceptional-character correction; no existence of a zero is asserted. -/
noncomputable def exceptionalBoundary (Q B N : ℕ) (r : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (H b : ℝ) (w : ℕ → ℂ) : ℂ :=
  -windowCoefficient r N w χ *
    ((normalizedPowerWindow B N H b-powerWeight b N : ℝ) : ℂ)

theorem exceptional_boundary_mass_le (Q B : ℕ) (hB : 2 ≤ B) (r : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (H : ℝ) (hH : 1 ≤ H) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M) :
    (∑ N ∈ blockCarrier B, ‖exceptionalBoundary Q B N r χ H b w‖) ≤
      M*(Q : ℝ)*(5*H+(B : ℝ)/(2*H)) := by
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        M*(Q : ℝ)*|normalizedPowerWindow B N H b-powerWeight b N| := by
      apply Finset.sum_le_sum
      intro N _
      unfold exceptionalBoundary
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (window_coefficient_norm_le_linear Q N r w M hM hw χ) (abs_nonneg _)
    _ = M*(Q : ℝ)*(∑ N ∈ blockCarrier B,
        |normalizedPowerWindow B N H b-powerWeight b N|) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (power_window_difference_mass_le B hB H hH b hb hb1) (by positivity)


/-- Original window and logarithmic weight, with explicit active conductor. -/
theorem actual_exceptional_boundary_mass_le_under_scale (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (r : PositiveLevel ⌊R^2⌋₊)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hG : ∀ x : ℝ, |G x| ≤ M)
    (hscale : R^7 ≤ (B : ℝ)) :
    (∑ N ∈ blockCarrier B,
      ‖exceptionalBoundary ⌊R^2⌋₊ B N r χ ((B : ℝ)/R^4) b (logWeight R G)‖) ≤
      (11/2)*M*(B : ℝ)/R := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have h4 : R^4 ≤ (B : ℝ) :=
    (pow_le_pow_right₀ hR.le (by decide : 4 ≤ 7)).trans hscale
  have hH : 1 ≤ (B : ℝ)/R^4 := (one_le_div (by positivity)).mpr h4
  have h6 : R^6 ≤ (B : ℝ)/R := by
    apply (le_div_iff₀ hRpos).mpr
    simpa only [← pow_succ] using hscale
  have hBR : (B : ℝ)/R^2 ≤ (B : ℝ)/R :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg B) hRpos (by nlinarith)
  have hw : ∀ n, ‖logWeight R G n‖ ≤ M := by
    intro n
    simpa only [logWeight, Complex.norm_real, Real.norm_eq_abs] using
      hG (Real.log (n : ℝ)/Real.log R)
  calc
    _ ≤ M*(⌊R^2⌋₊ : ℝ)*(5*((B : ℝ)/R^4)+(B : ℝ)/(2*((B : ℝ)/R^4))) :=
      exceptional_boundary_mass_le ⌊R^2⌋₊ B hB r χ ((B : ℝ)/R^4) hH b hb hb1
        (logWeight R G) M hM hw
    _ ≤ M*R^2*(5*((B : ℝ)/R^4)+(B : ℝ)/(2*((B : ℝ)/R^4))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.floor_le (sq_nonneg R)) hM) (by positivity)
    _ = M*(5*(B : ℝ)/R^2+R^6/2) := by
      field_simp [ne_of_gt hRpos, ne_of_gt hBpos]
    _ ≤ M*(5*((B : ℝ)/R)+((B : ℝ)/R)/2) := by
      apply mul_le_mul_of_nonneg_left _ hM
      rw [mul_div_assoc]
      linarith
    _ = _ := by ring

theorem actual_exceptional_boundary_mass_le_existing_range (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (r : PositiveLevel ⌊R^2⌋₊)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000)) :
    (∑ N ∈ blockCarrier B,
      ‖exceptionalBoundary ⌊R^2⌋₊ B N r χ ((B : ℝ)/R^4) b (logWeight R G)‖) ≤
      (11/2)*M*(B : ℝ)/R := by
  apply actual_exceptional_boundary_mass_le_under_scale B hB R hR r χ b hb hb1 G M hM hG
  exact (pow_le_pow_right₀ hR.le (by decide : 7 ≤ 34)).trans
    (GoldbachCircleMethodActualDiscrepancyScaleAbsorptionV18125.existing_upper_range_implies_scale
      (B : ℝ) R (by exact_mod_cast (by omega : 1 ≤ B))
      (le_of_lt (lt_trans zero_lt_one hR)) hupper)

theorem exceptional_boundary_fourier_norm_le_mass (Q B : ℕ) (r : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (H b : ℝ) (w : ℕ → ℂ) (x : UnitAddCircle) :
    ‖∑ N ∈ blockCarrier B, exceptionalBoundary Q B N r χ H b w * fourier (N : ℤ) x‖ ≤
      ∑ N ∈ blockCarrier B, ‖exceptionalBoundary Q B N r χ H b w‖ := by
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        ‖exceptionalBoundary Q B N r χ H b w * fourier (N : ℤ) x‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro N _
      simp [fourier_apply, Circle.norm_coe]

theorem actual_exceptional_boundary_fourier_bound (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (r : PositiveLevel ⌊R^2⌋₊)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000)) (x : UnitAddCircle) :
    ‖∑ N ∈ blockCarrier B, exceptionalBoundary ⌊R^2⌋₊ B N r χ
        ((B : ℝ)/R^4) b (logWeight R G) * fourier (N : ℤ) x‖ ≤
      (11/2)*M*(B : ℝ)/R :=
  (exceptional_boundary_fourier_norm_le_mass ⌊R^2⌋₊ B r χ
    ((B : ℝ)/R^4) b (logWeight R G) x).trans
    (actual_exceptional_boundary_mass_le_existing_range B hB R hR r χ b hb hb1 G M hM hG hupper)

end GoldbachCircleMethodExceptionalWeightBoundaryV18128
