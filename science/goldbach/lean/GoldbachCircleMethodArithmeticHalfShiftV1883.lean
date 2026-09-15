import GoldbachCircleMethodOriginalMaskCountermodelBindingV1882

/-! Arithmetic half-shift ingredients: actual Lambda coefficients, not a generic L2 model. -/
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171

namespace GoldbachCircleMethodArithmeticHalfShiftV1883

theorem even_vonMangoldt_nonzero_power_two (n : ℕ) (he : Even n)
    (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ n = 2^k := by
  rcases (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ) with
    ⟨p,k,hp,hk,hpow⟩
  have hd : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (by rw [hpow]; exact he.two_dvd)
  have htwo : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
  exact ⟨k,hk,by simpa [← htwo] using hpow.symm⟩

noncomputable def evenMangoldtMass (M : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 M).filter Even, ArithmeticFunction.vonMangoldt n

theorem evenMangoldtMass_le_log (M : ℕ) (hM : 0 < M) :
    evenMangoldtMass M ≤ Real.log (M : ℝ) := by
  let s := ((Finset.Icc 1 M).filter Even).filter
    (fun n => ArithmeticFunction.vonMangoldt n ≠ 0)
  have hsub : s ⊆ (2^(Nat.log 2 M)).divisors := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hne,hΛ⟩
    rcases Finset.mem_filter.mp hne with ⟨hnM,he⟩
    rcases even_vonMangoldt_nonzero_power_two n he hΛ with ⟨k,hk,hpow⟩
    have hkM : k ≤ Nat.log 2 M :=
      Nat.le_log_of_pow_le (by decide) (hpow ▸ (Finset.mem_Icc.mp hnM).2)
    apply Nat.mem_divisors.mpr
    refine ⟨?_, by positivity⟩
    rw [hpow]
    exact pow_dvd_pow 2 hkM
  have heq : evenMangoldtMass M = ∑ n ∈ s, ArithmeticFunction.vonMangoldt n := by
    simp only [s, evenMangoldtMass, Finset.sum_filter_ne_zero]
  rw [heq]
  calc
    _ ≤ ∑ n ∈ (2^(Nat.log 2 M)).divisors, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((2^(Nat.log 2 M) : ℕ) : ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ ≤ _ := Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.pow_log_le_self 2 hM.ne')

noncomputable def evenExponentialSum (M : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 M).filter Even,
    (ArithmeticFunction.vonMangoldt n : ℂ)*fourier (n : ℤ) x

theorem evenExponentialSum_norm_le_log (M : ℕ) (hM : 0 < M) (x : UnitAddCircle) :
    ‖evenExponentialSum M x‖ ≤ Real.log (M : ℝ) := by
  calc
    _ ≤ ∑ n ∈ (Finset.Icc 1 M).filter Even,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ)*fourier (n : ℤ) x‖ := norm_sum_le _ _
    _ = evenMangoldtMass M := by
      simp [evenMangoldtMass, fourier_apply, Circle.norm_coe,
        Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ _ := evenMangoldtMass_le_log M hM

theorem fourier_half_value (n : ℕ) :
    fourier (n : ℤ) (((1 : ℝ)/2 : ℝ) : UnitAddCircle) = (-1 : ℂ)^n := by
  have h1 : fourier (1 : ℤ) (((1 : ℝ)/2 : ℝ) : UnitAddCircle) = -1 := by
    simpa using (fourier_add_half_inv_index (n := (1 : ℤ))
      (by decide) (by norm_num : (0 : ℝ) < 1) (0 : UnitAddCircle))
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, fourier_add, ih, h1, pow_succ]

theorem exponentialSum_half_shift (M : ℕ) (x : UnitAddCircle) :
    exponentialSum M.succ (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) +
      exponentialSum M.succ x = 2*evenExponentialSum M x := by
  have hf (n : ℕ) :
      fourier (n : ℤ) (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) +
        fourier (n : ℤ) x =
      if Even n then 2*fourier (n : ℤ) x else 0 := by
    have hchar : fourier (n : ℤ) (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) =
        fourier (n : ℤ) x*fourier (n : ℤ) (((1 : ℝ)/2 : ℝ) : UnitAddCircle) := by
      simp [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]
    rw [hchar, fourier_half_value, neg_one_pow_eq_ite]
    split_ifs <;> ring
  have hsum : (∑ n ∈ Finset.range M.succ,
      if Even n then (ArithmeticFunction.vonMangoldt n : ℂ)*fourier (n : ℤ) x else 0) =
      evenExponentialSum M x := by
    symm
    unfold evenExponentialSum
    rw [Finset.sum_filter]
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_range.mpr (by have h := (Finset.mem_Icc.mp hn).2; omega)
    · intro n hn hnI
      have hn0 : n = 0 := by
        have hr := Finset.mem_range.mp hn
        simp only [Finset.mem_Icc, not_and_or] at hnI
        omega
      subst n
      simp
  calc
    _ = ∑ n ∈ Finset.range M.succ, (ArithmeticFunction.vonMangoldt n : ℂ)*
        (fourier (n : ℤ) (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle))+fourier (n : ℤ) x) := by
      simp [exponentialSum, Finset.sum_add_distrib, mul_add]
    _ = 2*∑ n ∈ Finset.range M.succ,
        if Even n then (ArithmeticFunction.vonMangoldt n : ℂ)*fourier (n : ℤ) x else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [hf]
      split_ifs <;> ring
    _ = _ := by rw [hsum]

theorem exponentialSum_half_shift_norm_le (M : ℕ) (hM : 0 < M) (x : UnitAddCircle) :
    ‖exponentialSum M.succ (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) +
      exponentialSum M.succ x‖ ≤ 2*Real.log (M : ℝ) := by
  rw [exponentialSum_half_shift, norm_mul]
  norm_num
  exact evenExponentialSum_norm_le_log M hM x

/-- Scalar indicator of the unchanged mask, not a replacement mask. -/
noncomputable def minorWeight (M P R : ℕ) (x : UnitAddCircle) : ℂ :=
  (GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorMask M P R).indicator
    (fun _ => 1) x

theorem maskedSquare_half_shift_defect (M P R : ℕ) (x : UnitAddCircle) :
    GoldbachCircleMethodTwoScaleBesselBridgeV1834.maskedSquare M P R
        (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) -
      GoldbachCircleMethodTwoScaleBesselBridgeV1834.maskedSquare M P R x =
    minorWeight M P R (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) *
      (4*(evenExponentialSum M x)^2 -
        4*(exponentialSum M.succ x)*evenExponentialSum M x) +
    (minorWeight M P R (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) -
      minorWeight M P R x)*(exponentialSum M.succ x)^2 := by
  have hm (y : UnitAddCircle) :
      GoldbachCircleMethodTwoScaleBesselBridgeV1834.maskedSquare M P R y =
        minorWeight M P R y*(exponentialSum M.succ y)^2 := by
    by_cases hy : y ∈ GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMinorMask M P R
    · simp [GoldbachCircleMethodTwoScaleBesselBridgeV1834.maskedSquare,
        minorWeight, Set.indicator_of_mem hy, pow_two]
    · simp [GoldbachCircleMethodTwoScaleBesselBridgeV1834.maskedSquare,
        minorWeight, Set.indicator_of_notMem hy]
  rw [hm, hm]
  have hS := exponentialSum_half_shift M x
  have hs' : exponentialSum M.succ (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) =
      2*evenExponentialSum M x-exponentialSum M.succ x := eq_sub_of_add_eq hS
  rw [hs']
  ring

/-- A half-shift does not change ANY even target coefficient, including the actual masked one. -/
theorem even_fourierCoeff_half_shift (f : UnitAddCircle → ℂ) (N : ℕ) (hN : Even N) :
    fourierCoeff (fun x => f (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle))) (N : ℤ) =
      fourierCoeff f (N : ℤ) := by
  have hh : fourier (-(N : ℤ)) (((1 : ℝ)/2 : ℝ) : UnitAddCircle) = 1 := by
    rw [fourier_neg, fourier_half_value, hN.neg_one_pow]
    simp
  have hc (x : UnitAddCircle) :
      fourier (-(N : ℤ)) (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) =
        fourier (-(N : ℤ)) x := by
    calc
      _ = fourier (-(N : ℤ)) x *
          fourier (-(N : ℤ)) (((1 : ℝ)/2 : ℝ) : UnitAddCircle) := by
        simp [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]
      _ = _ := by rw [hh, mul_one]
  rw [fourierCoeff, fourierCoeff]
  calc
    _ = ∫ x : UnitAddCircle,
        fourier (-(N : ℤ)) (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) •
          f (x+(((1 : ℝ)/2 : ℝ) : UnitAddCircle)) ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hc]
    _ = _ := integral_add_right_eq_self
      (fun x : UnitAddCircle => fourier (-(N : ℤ)) x • f x) _

end GoldbachCircleMethodArithmeticHalfShiftV1883
