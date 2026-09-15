import GoldbachCircleMethodRealApproximationMinorAdapterV1873
import Mathlib.Algebra.Order.Floor.Semifield

/-! # V1.8.74: explicit finite minor-moment and even-block transfer.
Vaughan and Major-reserve hypotheses stay explicit.
-/
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodTwoScaleBesselBridgeV1834
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachPurePrimeAdequacyV15
open Filter GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodArithmeticProgressionInputMatchV1871

namespace GoldbachCircleMethodQuantitativeMinorEvenBlockV1874

theorem ceil_ratio_le_twice (M P Q : ℕ) (hP : 0 < P) (hPM : P ≤ M)
    (hQ : Q = ⌈(M : ℝ)/(P : ℝ)⌉₊) :
    (Q : ℝ) ≤ 2*(M : ℝ)/(P : ℝ) := by
  have hp : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hr : 1 ≤ (M : ℝ)/(P : ℝ) := (one_le_div hp).mpr (by exact_mod_cast hPM)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ (M : ℝ)/(P : ℝ) by linarith)
  rw [hQ]
  calc
    _ ≤ (M : ℝ)/(P : ℝ)+1 := hc.le
    _ ≤ 2*(M : ℝ)/(P : ℝ) := by rw [mul_div_assoc]; linarith

theorem minorEnvelope_sq_le (M P Q R₀ : ℕ) (C : ℝ)
    (hP : 0 < P) (hPM : P ≤ M) (hQ : Q = ⌈(M : ℝ)/(P : ℝ)⌉₊) :
    (minorEnvelope M R₀ Q C)^2 ≤
      3*C^2*(Real.log (M : ℝ))^8 *
        ((M : ℝ)^2/(R₀ : ℝ)+(M : ℝ)^((8 : ℝ)/5)+2*(M : ℝ)^2/(P : ℝ)) := by
  have ha : ((M : ℝ)/Real.sqrt (R₀ : ℝ))^2 = (M : ℝ)^2/(R₀ : ℝ) := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hb : ((M : ℝ)^((4 : ℝ)/5))^2 = (M : ℝ)^((8 : ℝ)/5) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg M) ((4 : ℝ)/5) 2]
    norm_num
  have hc : (Real.sqrt ((M : ℝ)*(Q : ℝ)))^2 = (M : ℝ)*(Q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hs :
      ((M : ℝ)/Real.sqrt (R₀ : ℝ)+(M : ℝ)^((4 : ℝ)/5)+
        Real.sqrt ((M : ℝ)*(Q : ℝ)))^2 ≤
      3*((M : ℝ)^2/(R₀ : ℝ)+(M : ℝ)^((8 : ℝ)/5)+(M : ℝ)*(Q : ℝ)) := by
    nlinarith [sq_nonneg ((M : ℝ)/Real.sqrt (R₀ : ℝ)-(M : ℝ)^((4 : ℝ)/5)),
      sq_nonneg ((M : ℝ)/Real.sqrt (R₀ : ℝ)-Real.sqrt ((M : ℝ)*(Q : ℝ))),
      sq_nonneg ((M : ℝ)^((4 : ℝ)/5)-Real.sqrt ((M : ℝ)*(Q : ℝ)))]
  have hMQ : (M : ℝ)*(Q : ℝ) ≤ 2*(M : ℝ)^2/(P : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (ceil_ratio_le_twice M P Q hP hPM hQ)
      (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    calc
      _ ≤ (M : ℝ)*(2*(M : ℝ)/(P : ℝ)) := h
      _ = _ := by ring
  unfold minorEnvelope
  calc
    _ = C^2*(Real.log (M : ℝ))^8 *
      (((M : ℝ)/Real.sqrt (R₀ : ℝ)+(M : ℝ)^((4 : ℝ)/5)+
        Real.sqrt ((M : ℝ)*(Q : ℝ)))^2) := by ring
    _ ≤ C^2*(Real.log (M : ℝ))^8 *
        (3*((M : ℝ)^2/(R₀ : ℝ)+(M : ℝ)^((8 : ℝ)/5)+(M : ℝ)*(Q : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ _ := by
      have hp := mul_le_mul_of_nonneg_left hMQ
        (show 0 ≤ C^2*(Real.log (M : ℝ))^8 by positivity)
      nlinarith [hp]

noncomputable def fourthMomentBudget (M P R₀ : ℕ) (C : ℝ) : ℝ :=
  3*C^2*(M : ℝ)*(Real.log (M : ℝ))^10 *
    ((M : ℝ)^2/(R₀ : ℝ)+(M : ℝ)^((8 : ℝ)/5)+2*(M : ℝ)^2/(P : ℝ))

theorem minorFourthMoment_le_explicit_budget (C : ℝ) (hC : 0 ≤ C)
    (hV : RealVaughanEstimate C) (M P R₀ : ℕ) (hM : 3 ≤ M)
    (hP : 0 < P) (hPM : P ≤ M) (hR : 0 < R₀) :
    minorFourthMoment M P R₀ ≤ fourthMomentBudget M P R₀ C := by
  let Q : ℕ := ⌈(M : ℝ)/(P : ℝ)⌉₊
  have h := minorFourthMoment_bound_of_real_estimate C hC hV M P Q R₀ hM hP hR rfl
  have hs := mul_le_mul_of_nonneg_right (minorEnvelope_sq_le M P Q R₀ C hP hPM rfl)
    (show 0 ≤ (M : ℝ)*(Real.log (M : ℝ))^2 by positivity)
  apply h.trans
  convert hs using 1
  unfold fourthMomentBudget
  ring

theorem evenBlock_exceptions_le_explicit_budget (C : ℝ) (hC : 0 ≤ C)
    (hV : RealVaughanEstimate C) (M P R₀ : ℕ) (hM : 3 ≤ M)
    (hP : 0 < P) (hPM : P ≤ M) (hR : 0 < R₀)
    (hLarge : defectScaleThreshold ≤ M)
    (hMajor : ∀ N ∈ evenTargetBlock M,
      (M : ℝ)/14 ≤ twoScaleMajorIntegralReal M P R₀ N) :
    (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
      784*fourthMomentBudget M P R₀ C/(M : ℝ)^2 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hFourth : minorFourthMoment M P R₀ ≤
      4*(M : ℝ)^2*(fourthMomentBudget M P R₀ C/(4*(M : ℝ)^2)) := by
    rw [mul_div_cancel₀ _ (by positivity : (4*(M : ℝ)^2) ≠ 0)]
    exact minorFourthMoment_le_explicit_budget C hC hV M P R₀ hM hP hPM hR
  have h := evenBlock_exceptions_card_le_3136_of_fourthMoment M P R₀
    (fourthMomentBudget M P R₀ C/(4*(M : ℝ)^2)) hLarge hMajor hFourth
  calc
    _ ≤ 3136 * (fourthMomentBudget M P R₀ C/(4*(M : ℝ)^2)) := h
    _ = _ := by field_simp; ring

theorem eventual_evenBlock_budget_of_two_analytic_inputs
    (K k₀ : ℕ) (hK : 0 < K) (Csw csw Cv : ℝ)
    (hCsw : 0 ≤ Csw) (hcsw : 0 < csw) (hCv : 0 ≤ Cv)
    (hAP : ScaleAPEstimate (K+1) k₀ Csw csw) (hV : RealVaughanEstimate Cv) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀,
      (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
        784*fourthMomentBudget M (logWidth K M) (logRadius K M) Cv/(M : ℝ)^2 := by
  obtain ⟨M₁, hMajor⟩ := uniform_major_reserve_of_AP_estimate K k₀ hK Csw csw hCsw hcsw hAP
  have hev : ∀ᶠ M : ℕ in atTop,
      (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
        784*fourthMomentBudget M (logWidth K M) (logRadius K M) Cv/(M : ℝ)^2 := by
    filter_upwards [log_scales_eventually_disjoint K, eventually_ge_atTop (3 : ℕ),
      eventually_ge_atTop defectScaleThreshold, eventually_ge_atTop M₁] with M hs h3 hd hM₁
    obtain ⟨hR, hP, hdisj⟩ := hs
    have hPM : logWidth K M ≤ M := by
      have hpR := Nat.mul_le_mul_left (logWidth K M) hR
      nlinarith
    apply evenBlock_exceptions_le_explicit_budget Cv hCv hV M (logWidth K M) (logRadius K M)
      h3 hP hPM (by omega) hd
    intro N hN
    obtain ⟨h4, hNM, he, hhalf⟩ := (mem_evenTargetBlock_iff M N).mp hN
    exact hMajor M hM₁ N h4 hNM he hhalf
  exact eventually_atTop.mp hev

end GoldbachCircleMethodQuantitativeMinorEvenBlockV1874
