import GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Fixed-mask Bessel bridge, V1.8.34
The unchanged minor operator is a Fourier coefficient of the masked square.
Bessel controls the finite negative-part moment by the minor fourth moment.
No estimate of that fourth moment or Major reserve is supplied here.
-/
set_option autoImplicit false

namespace GoldbachCircleMethodTwoScaleBesselBridgeV1834

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodFixedScaleTransferV1824
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachPurePrimeAdequacyV15

/-- A single function for all frequencies N; M,P,R0 remain fixed. -/
noncomputable def maskedSquare (M P R0 : Nat) : UnitAddCircle → Complex :=
  (twoScaleMinorMask M P R0).indicator
    (fun x => exponentialSum M.succ x * exponentialSum M.succ x)

/-- The actual minor fourth moment, with the existing normalized Haar measure. -/
noncomputable def minorFourthMoment (M P R0 : Nat) : Real :=
  ∫ x in twoScaleMinorMask M P R0,
    ‖exponentialSum M.succ x‖ ^ 4 ∂haarAddCircle

theorem maskedSquare_memLp_two (M P R0 : Nat) :
    MemLp (maskedSquare M P R0) 2 haarAddCircle := by
  exact MemLp.indicator (twoScaleMinorMask_measurable M P R0)
    (ContinuousMap.memLp (p := 2) haarAddCircle Complex
      (exponentialSum M.succ * exponentialSum M.succ))

/-- No target-range restriction is needed for the coefficient identity. -/
theorem fourierCoeff_maskedSquare (M P R0 N : Nat) :
    fourierCoeff (maskedSquare M P R0) (N : Int) =
      ∫ x in twoScaleMinorMask M P R0,
        fixedScalePairFourierIntegrand M N x ∂haarAddCircle := by
  rw [fourierCoeff, ← integral_indicator (twoScaleMinorMask_measurable M P R0)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ twoScaleMinorMask M P R0
  · simp [maskedSquare, Set.indicator_of_mem hx, fixedScalePairFourierIntegrand,
      smul_eq_mul]
  · simp [maskedSquare, Set.indicator_of_notMem hx]

theorem minorReal_eq_re_fourierCoeff (M P R0 N : Nat) :
    twoScaleMinorIntegralReal M P R0 N =
      (fourierCoeff (maskedSquare M P R0) (N : Int)).re := by
  rw [fourierCoeff_maskedSquare]
  rfl

theorem integral_maskedSquare_norm_sq (M P R0 : Nat) :
    (∫ x : UnitAddCircle, ‖maskedSquare M P R0 x‖ ^ 2 ∂haarAddCircle) =
      minorFourthMoment M P R0 := by
  unfold minorFourthMoment
  rw [← integral_indicator (twoScaleMinorMask_measurable M P R0)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ twoScaleMinorMask M P R0
  · simp only [maskedSquare, Set.indicator_of_mem hx, norm_mul]
    ring
  · simp [maskedSquare, Set.indicator_of_notMem hx]

theorem hasSum_sq_maskedFourierCoeff (M P R0 : Nat) :
    HasSum (fun k : Int => ‖fourierCoeff (maskedSquare M P R0) k‖ ^ 2)
      (minorFourthMoment M P R0) := by
  let h := maskedSquare_memLp_two M P R0
  have hc := fourierCoeff_congr_ae h.coeFn_toLp
  have hi :
      (∫ x : UnitAddCircle, ‖h.toLp (maskedSquare M P R0) x‖ ^ 2 ∂haarAddCircle) =
        ∫ x : UnitAddCircle, ‖maskedSquare M P R0 x‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [h.coeFn_toLp] with x hx
    rw [hx]
  have hp := hasSum_sq_fourierCoeff (h.toLp (maskedSquare M P R0))
  rw [hc, hi, integral_maskedSquare_norm_sq] at hp
  exact hp

/-- Finite Nat frequencies are embedded injectively into the full integer spectrum. -/
theorem finite_sq_coeff_le_minorFourthMoment (M P R0 : Nat) (s : Finset Nat) :
    (∑ N ∈ s, ‖fourierCoeff (maskedSquare M P R0) (N : Int)‖ ^ 2) ≤
      minorFourthMoment M P R0 := by
  have hs := sum_le_hasSum (s.image (fun N : Nat => (N : Int)))
    (fun k _ => sq_nonneg ‖fourierCoeff (maskedSquare M P R0) k‖)
    (hasSum_sq_maskedFourierCoeff M P R0)
  rw [Finset.sum_image] at hs
  · exact hs
  · intro a ha b hb hab
    exact Int.ofNat_inj.mp hab

theorem negativePart_re_sq_le_norm_sq (z : Complex) :
    negativePart z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  have hAbs := Complex.abs_re_le_norm z
  have hBound : negativePart z.re ≤ ‖z‖ := by
    exact max_le ((neg_le_abs z.re).trans hAbs) (norm_nonneg z)
  have hNonneg : 0 ≤ negativePart z.re := le_max_right _ _
  nlinarith [norm_nonneg z]

/-- Unconditional finite Bessel bound; no analytic moment decay is claimed. -/
theorem negativePartMoment_le_minorFourthMoment
    (M P R0 : Nat) (s : Finset Nat) :
    negativePartSquaredMoment s (twoScaleMinorIntegralReal M P R0) ≤
      minorFourthMoment M P R0 := by
  unfold negativePartSquaredMoment
  calc
    _ ≤ ∑ N ∈ s, ‖fourierCoeff (maskedSquare M P R0) (N : Int)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro N hN
      rw [minorReal_eq_re_fourierCoeff]
      exact negativePart_re_sq_le_norm_sq _
    _ ≤ _ := finite_sq_coeff_le_minorFourthMoment M P R0 s

/-- Replace the old moment premise by the still-open actual fourth-moment bound. -/
theorem evenBlock_exceptions_card_le_3136_of_fourthMoment
    (M P R0 : Nat) (B : Real) (hLarge : defectScaleThreshold ≤ M)
    (hMajor : ∀ N ∈ evenTargetBlock M,
      (M : Real) / 14 ≤ twoScaleMajorIntegralReal M P R0 N)
    (hFourth : minorFourthMoment M P R0 ≤ 4 * (M : Real) ^ 2 * B) :
    (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : Real) ≤ 3136 * B := by
  apply evenBlock_exceptions_card_le_3136_of_threshold M P R0 B hLarge hMajor
  exact (negativePartMoment_le_minorFourthMoment M P R0 (evenTargetBlock M)).trans hFourth

end GoldbachCircleMethodTwoScaleBesselBridgeV1834
