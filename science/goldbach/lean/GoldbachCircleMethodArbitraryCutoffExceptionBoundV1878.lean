import GoldbachCircleMethodDyadicLogarithmicSumTransferV1877

/-! # V1.8.78: arbitrary natural cutoffs with the finite remainder retained. -/
set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodFiniteDyadicExceptionCarrierV1876
open GoldbachCircleMethodDyadicLogarithmicSumTransferV1877
open GoldbachCircleMethodLogarithmicBlockDecayV1875
open GoldbachCircleMethodArithmeticProgressionInputMatchV1871
open GoldbachCircleMethodRealApproximationMinorAdapterV1873

namespace GoldbachCircleMethodArbitraryCutoffExceptionBoundV1878

theorem half_clog_threshold (X M₀ : ℕ) (hX : M₀^2 ≤ X) :
    M₀ ≤ 2^((Nat.clog 2 X)/2+1) := by
  have hD := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) X
  have hex : Nat.clog 2 X ≤ ((Nat.clog 2 X)/2+1)*2 := by omega
  have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hex
  rw [pow_mul] at hp
  exact (pow_le_pow_iff_left₀ (Nat.zero_le M₀) (Nat.zero_le _) (by norm_num : (2 : ℕ) ≠ 0)).mp
    (hX.trans (hD.trans hp))

theorem half_dyadic_remainder_le_sqrt (X : ℕ) (hX : 1 < X) :
    (2 : ℝ)^((Nat.clog 2 X)/2) ≤ Real.sqrt (2*(X : ℝ)) := by
  have hD := (clog_dyadic_assignment X hX).2.2.2
  have hp : (2 : ℝ)^(((Nat.clog 2 X)/2)*2) ≤ (2 : ℝ)^(Nat.clog 2 X) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_mul] at hp
  have hDR : (2 : ℝ)^(Nat.clog 2 X) ≤ 2*(X : ℝ) := by exact_mod_cast hD.le
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  exact hp.trans hDR

theorem cutoff_log_weight_le (A X : ℕ) (hX : 1 < X) :
    (2 : ℝ)^(A+1)*(2 : ℝ)^(Nat.clog 2 X) /
      (Real.log ((2 : ℝ)^(Nat.clog 2 X)))^A ≤
        (2 : ℝ)^(A+2)*(X : ℝ)/(Real.log (X : ℝ))^A := by
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hxpos : (0 : ℝ) < X := by linarith
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hx
  have hDX : (X : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 X) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) X
  have hD2 : (2 : ℝ)^(Nat.clog 2 X) ≤ 2*(X : ℝ) := by
    exact_mod_cast (clog_dyadic_assignment X hX).2.2.2.le
  have hl : Real.log (X : ℝ) ≤ Real.log ((2 : ℝ)^(Nat.clog 2 X)) :=
    Real.log_le_log hxpos hDX
  have hpow := pow_le_pow_left₀ hlog.le hl A
  have hden : 0 < (Real.log (X : ℝ))^A := pow_pos hlog _
  calc
    _ ≤ (2 : ℝ)^(A+1)*(2 : ℝ)^(Nat.clog 2 X)/(Real.log (X : ℝ))^A :=
      div_le_div_of_nonneg_left (by positivity) hden hpow
    _ ≤ (2 : ℝ)^(A+1)*(2*(X : ℝ))/(Real.log (X : ℝ))^A :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD2 (by positivity)) hden.le
    _ = _ := by rw [show A+2=(A+1)+1 by omega, pow_succ]; ring

theorem global_cutoff_bound_of_block_bound (A X M₀ : ℕ)
    (hX : 1 < X) (hlarge : M₀^2 ≤ X)
    (hblock : ∀ M ≥ M₀,
      (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
        (M : ℝ)/(Real.log (M : ℝ))^A) :
    ((globalExceptions X).card : ℝ) ≤
      Real.sqrt (2*(X : ℝ))+(2 : ℝ)^(A+2)*(X : ℝ)/(Real.log (X : ℝ))^A := by
  have hc : ((globalExceptions X).card : ℝ) ≤
      ((globalExceptions (2^(Nat.clog 2 X))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (globalExceptions_mono
      (Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) X))
  have hb := global_dyadic_bound_of_block_bound A (Nat.clog 2 X) M₀
    (Nat.clog_pos (by norm_num) hX) (half_clog_threshold X M₀ hlarge) hblock
  exact (hc.trans hb).trans
    (add_le_add (half_dyadic_remainder_le_sqrt X hX) (cutoff_log_weight_le A X hX))

theorem conditional_global_cutoff_bound (A k₀ : ℕ) (Csw csw Cv : ℝ)
    (hCsw : 0 ≤ Csw) (hcsw : 0 < csw) (hCv : 0 ≤ Cv)
    (hAP : ScaleAPEstimate (A+12) k₀ Csw csw) (hV : RealVaughanEstimate Cv) :
    ∃ M₀ : ℕ, ∀ X : ℕ, 1 < X → M₀^2 ≤ X →
      ((globalExceptions X).card : ℝ) ≤
        Real.sqrt (2*(X : ℝ))+(2 : ℝ)^(A+2)*(X : ℝ)/(Real.log (X : ℝ))^A := by
  obtain ⟨M₀, hb⟩ := eventual_evenBlock_log_decay_of_two_analytic_inputs
    A k₀ Csw csw Cv hCsw hcsw hCv hAP hV
  exact ⟨M₀, fun X hX hlarge => global_cutoff_bound_of_block_bound A X M₀ hX hlarge hb⟩

end GoldbachCircleMethodArbitraryCutoffExceptionBoundV1878
