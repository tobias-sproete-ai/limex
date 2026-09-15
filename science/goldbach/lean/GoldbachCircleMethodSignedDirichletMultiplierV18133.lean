import GoldbachCircleMethodActualOutputTailBoundV18132

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodSignedWindowFourierAdapterV18130
open GoldbachCircleMethodFiniteRamanujanEnergyV18131
open GoldbachCircleMethodComplexArcModelBindingV1856
open GoldbachCircleMethodShiftedClosedArcModelV1858
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodDiscreteGeometricBoundV1853
open GoldbachCircleMethodFiniteAbelAdapterV1863

namespace GoldbachCircleMethodSignedDirichletMultiplierV18133

/-- The exact symmetric finite kernel, normalized by the real radius, not its floor. -/
noncomputable def normalizedDirichlet (H : ℝ) (x : UnitAddCircle) : ℂ :=
  (2*(H : ℂ))⁻¹ * ∑ k ∈ shiftCarrier H, fourier k x

theorem normalization_norm (H : ℝ) (hH : 0 ≤ H) :
    ‖(2*(H : ℂ))⁻¹‖ = (2*H)⁻¹ := by
  rw [norm_inv, norm_mul]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hH]

theorem normalized_dirichlet_at_zero (H : ℝ) :
    normalizedDirichlet H 0 = ((2*(⌊H⌋₊ : ℝ)+1)/(2*H) : ℝ) := by
  simp [normalizedDirichlet, signed_shift_card, div_eq_mul_inv, mul_comm]

theorem normalized_dirichlet_norm_le_card (H : ℝ) (hH : 0 ≤ H) (x : UnitAddCircle) :
    ‖normalizedDirichlet H x‖ ≤ (2*(⌊H⌋₊ : ℝ)+1)/(2*H) := by
  unfold normalizedDirichlet
  rw [norm_mul, normalization_norm H hH]
  calc
    _ ≤ (2*H)⁻¹ * ∑ k ∈ shiftCarrier H, ‖fourier k x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = _ := by
      simp [fourier_apply, Circle.norm_coe, signed_shift_card, div_eq_mul_inv, mul_comm]

theorem normalized_dirichlet_norm_le_three_halves (H : ℝ) (hH : 1 ≤ H)
    (x : UnitAddCircle) : ‖normalizedDirichlet H x‖ ≤ 3/2 := by
  apply (normalized_dirichlet_norm_le_card H (by linarith) x).trans
  apply (div_le_iff₀ (by linarith : 0 < 2*H)).mpr
  have := Nat.floor_le (show 0 ≤ H by linarith)
  linarith

theorem normalized_dirichlet_zero_error (H : ℝ) (hH : 0 < H) :
    ‖normalizedDirichlet H 0 - 1‖ ≤ 1/(2*H) := by
  rw [normalized_dirichlet_at_zero]
  have he : (((2*(⌊H⌋₊ : ℝ)+1)/(2*H) : ℝ) : ℂ)-1 =
      (((2*(⌊H⌋₊ : ℝ)+1-2*H)/(2*H) : ℝ) : ℂ) := by
    push_cast
    field_simp [show (H : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hH]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < 2*H)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply abs_le.mpr
  have hl := Nat.floor_le hH.le
  have hu := Nat.lt_floor_add_one H
  constructor <;> linarith

theorem integer_phase_gap (k : ℤ) (β : ℝ) :
    ‖fourier k (β : UnitAddCircle)-1‖ ≤ 2*Real.pi*|(k : ℝ)| * |β| := by
  have he : fourier k (β : UnitAddCircle) =
      fourier 1 (((k : ℝ)*β : ℝ) : UnitAddCircle) := by
    rw [fourier_coe_apply, fourier_coe_apply]
    push_cast
    norm_num
    congr 1
    ring
  rw [he]
  simpa only [abs_mul, mul_assoc] using character_gap_le_two_pi_abs ((k : ℝ)*β)

theorem normalized_dirichlet_near_zero (H : ℝ) (hH : 1 ≤ H) (β : ℝ) :
    ‖normalizedDirichlet H (β : UnitAddCircle)-normalizedDirichlet H 0‖ ≤
      3*Real.pi*H*|β| := by
  have hh0 : 0 ≤ H := by linarith
  have he : normalizedDirichlet H (β : UnitAddCircle)-normalizedDirichlet H 0 =
      (2*(H : ℂ))⁻¹ * ∑ k ∈ shiftCarrier H, (fourier k (β : UnitAddCircle)-1) := by
    simp [normalizedDirichlet, Finset.sum_sub_distrib, mul_sub]
  rw [he, norm_mul, normalization_norm H hh0]
  calc
    _ ≤ (2*H)⁻¹ * ∑ k ∈ shiftCarrier H, ‖fourier k (β : UnitAddCircle)-1‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (2*H)⁻¹ * ∑ _k ∈ shiftCarrier H, 2*Real.pi*H*|β| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      exact (integer_phase_gap k β).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((mem_shift_carrier H hh0 k).mp hk) (by positivity))
          (abs_nonneg β))
    _ = ((shiftCarrier H).card : ℝ)*Real.pi*|β| := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
    _ ≤ _ := by
      have hc : ((shiftCarrier H).card : ℝ) ≤ 3*H := by
        rw [signed_shift_card]
        have := Nat.floor_le hh0
        push_cast
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ Real.pi*|β| by positivity)]

theorem normalized_dirichlet_error_le (H : ℝ) (hH : 1 ≤ H) (β : ℝ) :
    ‖normalizedDirichlet H (β : UnitAddCircle)-1‖ ≤
      1/(2*H)+3*Real.pi*H*|β| := by
  calc
    _ ≤ ‖normalizedDirichlet H (β : UnitAddCircle)-normalizedDirichlet H 0‖+
        ‖normalizedDirichlet H 0-1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      linarith [normalized_dirichlet_near_zero H hH β,
        normalized_dirichlet_zero_error H (by linarith)]

theorem symmetric_fourier_as_discrete (h : ℕ) (x : UnitAddCircle) :
    (∑ k ∈ Finset.Icc (-(h : ℤ)) (h : ℤ), fourier k x) =
      fourier (-((h+1 : ℕ) : ℤ)) x * discreteMainPolynomial (2*h+1) x := by
  have he : (∑ k ∈ Finset.Icc (-(h : ℤ)) (h : ℤ), fourier k x) =
      ∑ n ∈ Finset.Icc 1 (2*h+1), fourier ((n : ℤ)-((h+1 : ℕ) : ℤ)) x := by
    apply Finset.sum_bij (fun k _ => (k+(h : ℤ)+1).toNat)
    · intro k hk
      have := Finset.mem_Icc.mp hk
      apply Finset.mem_Icc.mpr
      omega
    · intro k hk l hl heq
      have := Finset.mem_Icc.mp hk
      have := Finset.mem_Icc.mp hl
      omega
    · intro n hn
      have := Finset.mem_Icc.mp hn
      refine ⟨(n : ℤ)-((h+1 : ℕ) : ℤ), Finset.mem_Icc.mpr ?_, ?_⟩
      · constructor <;> omega
      · omega
    · intro k hk
      have := Finset.mem_Icc.mp hk
      have heq : k = (((k+(h : ℤ)+1).toNat : ℤ)-((h+1 : ℕ) : ℤ)) := by omega
      exact congrArg (fun t : ℤ => fourier t x) heq
  rw [he]
  simp only [sub_eq_add_neg, fourier_add, discreteMainPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem normalized_dirichlet_off_zero (H : ℝ) (hH : 0 < H) (β : ℝ)
    (hβ0 : 0 < |β|) (hβ : |β| ≤ 1/2) :
    ‖normalizedDirichlet H (β : UnitAddCircle)‖ ≤ 1/(4*H*|β|) := by
  unfold normalizedDirichlet shiftCarrier
  rw [symmetric_fourier_as_discrete, norm_mul, normalization_norm H hH.le, norm_mul]
  simp only [fourier_apply, Circle.norm_coe, one_mul]
  calc
    _ ≤ (2*H)⁻¹ * (1/(2*|β|)) :=
      mul_le_mul_of_nonneg_left (discreteMainPolynomial_norm_le _ β hβ0 hβ) (by positivity)
    _ = _ := by ring

theorem unit_sum_as_positive_fourier (q : ℕ) [NeZero q] (k : ℤ) :
    unitCharacterSum q (k : ZMod q) =
      ∑ r : ZMod q, if IsUnit r then
        fourier k (((r.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) else 0 := by
  unfold unitCharacterSum
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : IsUnit r
  · simp only [hr, if_true, rational_fourier_phase_eq_stdAddChar, mul_comm]
  · simp only [hr, if_false]

/-- Exact plus-sign rational-frequency expansion for the unchanged V130 kernel.
A point near a/q resonates with the reduced residue -a, not a. -/
theorem signed_kernel_fourier_multiplier_formula (Q : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (w : ℕ → ℂ) (x : UnitAddCircle) :
    (∑ k ∈ shiftCarrier H, signedWindowKernel Q H w k * fourier k x) =
      ∑ q : PositiveLevel Q, w q.val *
        ∑ r : ZMod q.val, if IsUnit r then
          normalizedDirichlet H (x+(((r.val : ℝ)/(q.val : ℝ) : ℝ) : UnitAddCircle))
        else 0 := by
  have hs : (∑ k ∈ shiftCarrier H, signedWindowKernel Q H w k * fourier k x) =
      ∑ k ∈ shiftCarrier H, ∑ q : PositiveLevel Q,
        w q.val * ((2*(H : ℂ))⁻¹ *
          (unitCharacterSum q.val (k : ZMod q.val)*fourier k x)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [signedWindowKernel, if_pos ((mem_shift_carrier H hH k).mp hk)]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finset.mul_sum]
  congr 1
  simp only [unit_sum_as_positive_fourier, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : IsUnit r
  · simp only [hr, if_true, normalizedDirichlet, fourier_argument_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp only [hr, if_false, zero_mul, mul_zero, Finset.sum_const_zero]

end GoldbachCircleMethodSignedDirichletMultiplierV18133
