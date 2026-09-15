import GoldbachCircleMethodArbitraryCutoffExceptionBoundV1878

/-! # V1.8.79: conditional global logarithmic exceptional-set decay.
The two analytic inputs remain explicit parameters. No new density record
or pointwise Goldbach theorem is asserted.
-/
set_option autoImplicit false
open scoped BigOperators Classical
open Filter Topology
open GoldbachCircleMethodFiniteDyadicExceptionCarrierV1876
open GoldbachCircleMethodArbitraryCutoffExceptionBoundV1878
open GoldbachCircleMethodArithmeticProgressionInputMatchV1871
open GoldbachCircleMethodRealApproximationMinorAdapterV1873

namespace GoldbachCircleMethodConditionalGlobalExceptionDecayV1879

theorem normalized_remainder_identity (A X : ℕ) (hX : 0 < X) :
    Real.sqrt (2*(X : ℝ))*(Real.log (X : ℝ))^A/(X : ℝ) =
      Real.sqrt 2*((Real.log (X : ℝ))^A/(X : ℝ)^((1 : ℝ)/2)) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hs : Real.sqrt (X : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hr : Real.sqrt (X : ℝ)/(X : ℝ) = 1/Real.sqrt (X : ℝ) := by
    apply (div_eq_div_iff hx.ne' hs).mpr
    simpa only [one_mul, pow_two] using Real.sq_sqrt hx.le
  calc
    _ = Real.sqrt 2*(Real.log (X : ℝ))^A*(Real.sqrt (X : ℝ)/(X : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = Real.sqrt 2*((Real.log (X : ℝ))^A/Real.sqrt (X : ℝ)) := by rw [hr]; ring
    _ = _ := by rw [Real.sqrt_eq_rpow (X : ℝ)]

theorem normalized_remainder_tendsto_zero (A : ℕ) :
    Tendsto (fun X : ℕ => Real.sqrt (2*(X : ℝ))*(Real.log (X : ℝ))^A/(X : ℝ))
      atTop (𝓝 0) := by
  have hbase := (isLittleO_log_rpow_rpow_atTop (A : ℝ)
    (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
  have h : Tendsto (fun X : ℕ => Real.sqrt 2*
      ((Real.log (X : ℝ))^A/(X : ℝ)^((1 : ℝ)/2))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, mul_zero] using
      (hbase.comp tendsto_natCast_atTop_atTop).const_mul (Real.sqrt 2)
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  exact (normalized_remainder_identity A X hX).symm

theorem eventual_remainder_absorption (A : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      Real.sqrt (2*(X : ℝ)) ≤ (X : ℝ)/(Real.log (X : ℝ))^A := by
  have hsmall := (normalized_remainder_tendsto_zero A).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℕ)] with X hs hX
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hxpos : (0 : ℝ) < X := by linarith
  have hp : 0 < (Real.log (X : ℝ))^A := pow_pos (Real.log_pos hx) _
  apply (le_div_iff₀ hp).mpr
  have h := (div_le_iff₀ hxpos).mp hs.le
  simpa only [one_mul] using h

theorem conditional_global_exception_bound (A k₀ : ℕ) (Csw csw Cv : ℝ)
    (hCsw : 0 ≤ Csw) (hcsw : 0 < csw) (hCv : 0 ≤ Cv)
    (hAP : ScaleAPEstimate (A+12) k₀ Csw csw) (hV : RealVaughanEstimate Cv) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      ((globalExceptions X).card : ℝ) ≤
        (1+(2 : ℝ)^(A+2))*((X : ℝ)/(Real.log (X : ℝ))^A) := by
  obtain ⟨M₀, hb⟩ := conditional_global_cutoff_bound
    A k₀ Csw csw Cv hCsw hcsw hCv hAP hV
  apply eventually_atTop.mp
  filter_upwards [eventual_remainder_absorption A, eventually_ge_atTop (M₀^2),
      eventually_gt_atTop (1 : ℕ)] with X hr hlarge hX
  calc
    _ ≤ Real.sqrt (2*(X : ℝ))+
        (2 : ℝ)^(A+2)*(X : ℝ)/(Real.log (X : ℝ))^A := hb X hX hlarge
    _ ≤ (X : ℝ)/(Real.log (X : ℝ))^A+
        (2 : ℝ)^(A+2)*(X : ℝ)/(Real.log (X : ℝ))^A :=
      add_le_add hr le_rfl
    _ = _ := by ring

theorem conditional_global_exception_isBigO (A k₀ : ℕ) (Csw csw Cv : ℝ)
    (hCsw : 0 ≤ Csw) (hcsw : 0 < csw) (hCv : 0 ≤ Cv)
    (hAP : ScaleAPEstimate (A+12) k₀ Csw csw) (hV : RealVaughanEstimate Cv) :
    Asymptotics.IsBigO atTop
      (fun X : ℕ => ((globalExceptions X).card : ℝ))
      (fun X : ℕ => (X : ℝ)/(Real.log (X : ℝ))^A) := by
  obtain ⟨X₀, hb⟩ := conditional_global_exception_bound
    A k₀ Csw csw Cv hCsw hcsw hCv hAP hV
  apply Asymptotics.IsBigO.of_bound (1+(2 : ℝ)^(A+2))
  filter_upwards [eventually_ge_atTop X₀, eventually_gt_atTop (1 : ℕ)] with X hlarge hX
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hnonneg : 0 ≤ (X : ℝ)/(Real.log (X : ℝ))^A :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.log_pos hx).le _)
  have hcard : (0 : ℝ) ≤ ((globalExceptions X).card : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hcard,
    abs_of_nonneg hnonneg] using hb X hlarge

end GoldbachCircleMethodConditionalGlobalExceptionDecayV1879
