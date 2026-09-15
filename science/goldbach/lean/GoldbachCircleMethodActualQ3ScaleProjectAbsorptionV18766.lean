import GoldbachCircleMethodActualQ3ScaleCombinedPrefixEnvelopeV18765
import GoldbachCircleMethodPrefixBudgetAbsorptionV1870

/-!
# V1.8.766: eventual project absorption of the source-matched q=3 envelope

The combined genuine-character ceiling is inserted into the literal project
scale envelope.  Elementary project-schedule bounds and two existing decay
lemmas show that the normalized debit tends to zero.

The distribution estimate and the signed local-density reserve remain open
inputs in later composition.  No Goldbach conclusion is asserted.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology

namespace GoldbachCircleMethodActualQ3ScaleProjectAbsorptionV18766

open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformMajorPrefixReductionV1865
open GoldbachCircleMethodPrefixBudgetAbsorptionV1870
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756
open GoldbachCircleMethodActualQ3SmallPrefixProjectAbsorptionV18763
open GoldbachCircleMethodActualQ3ScaleCombinedPrefixEnvelopeV18765

/-- A transparent absolute majorant for the q=3 project debit. -/
noncomputable def actualQ3ScaleProjectMajorant
    (M : Nat) (C c : Real) : Real :=
  512 * chebyshevConstant ^ 2 * Real.log (M : Real) ^ 21 *
      Real.sqrt (M : Real) +
    1024 * chebyshevConstant * C * Real.log (M : Real) ^ 21 *
      (M : Real) * Real.exp (-(c / 2) * Real.sqrt (Real.log (M : Real))) +
    512 * chebyshevConstant * Real.log (M : Real) ^ 22 *
      Real.sqrt (M : Real)

/-- The corresponding dimensionless majorant. -/
noncomputable def actualQ3ScaleProjectNormalizedMajorant
    (M : Nat) (C c : Real) : Real :=
  512 * chebyshevConstant ^ 2 *
      (Real.log (M : Real) ^ 21 / Real.sqrt (M : Real)) +
    1024 * chebyshevConstant * C *
      (Real.log (M : Real) ^ 21 *
        Real.exp (-(c / 2) * Real.sqrt (Real.log (M : Real)))) +
    512 * chebyshevConstant *
      (Real.log (M : Real) ^ 22 / Real.sqrt (M : Real))

/-- Exact normalization identity for positive scales. -/
theorem actualQ3ScaleProjectMajorant_eq_mul_normalized
    (M : Nat) (hM : 0 < M) (C c : Real) :
    actualQ3ScaleProjectMajorant M C c =
      (M : Real) * actualQ3ScaleProjectNormalizedMajorant M C c := by
  have hm : (0 : Real) < M := by exact_mod_cast hM
  have hs : Real.sqrt (M : Real) ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  have hs2 := Real.sq_sqrt hm.le
  unfold actualQ3ScaleProjectMajorant
  unfold actualQ3ScaleProjectNormalizedMajorant
  field_simp [hs]
  ring_nf
  rw [hs2]

/-- The literal q=3 project envelope is bounded by the transparent majorant. -/
theorem actualQ3UnitDifferenceScaleEnvelope_combined_le_majorant
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hq : q.val.val = 3)
    (C c : Real) (hC : 0 ≤ C)
    (hlog : 1 ≤ Real.log (M : Real)) :
    actualQ3UnitDifferenceScaleEnvelope M q
        (actualQ3ScaleCombinedPrefixEnvelope M C c +
          Real.log (M : Real)) ≤
      actualQ3ScaleProjectMajorant M C c := by
  have hm : (0 : Real) < M := by exact_mod_cast hM
  have hmne : (M : Real) ≠ 0 := hm.ne'
  have hqR : (q.val.val : Real) = 3 := by exact_mod_cast hq
  have hP := oddProjectWidth_le_log20 M hlog
  have hlog0 : 0 ≤ Real.log (M : Real) := le_trans (by norm_num) hlog
  have hOneLog : 1 + Real.log (M : Real) ≤
      2 * Real.log (M : Real) := by linarith
  have hWeight :
      8 * chebyshevConstant * (oddProjectWidth M : Real) *
          (1 + Real.log (M : Real)) ≤
        512 * chebyshevConstant * Real.log (M : Real) ^ 21 := by
    have hA :
        (oddProjectWidth M : Real) * (1 + Real.log (M : Real)) ≤
          (32 * Real.log (M : Real) ^ 20) *
            (2 * Real.log (M : Real)) :=
      mul_le_mul hP hOneLog (by positivity) (by positivity)
    have hB :
        (8 * chebyshevConstant) *
            ((oddProjectWidth M : Real) * (1 + Real.log (M : Real))) ≤
          (8 * chebyshevConstant) *
            ((32 * Real.log (M : Real) ^ 20) *
              (2 * Real.log (M : Real))) :=
      mul_le_mul_of_nonneg_left hA
        (mul_nonneg (by norm_num) chebyshevConstant_pos.le)
    calc
      8 * chebyshevConstant * (oddProjectWidth M : Real) *
          (1 + Real.log (M : Real)) =
          (8 * chebyshevConstant) *
            ((oddProjectWidth M : Real) * (1 + Real.log (M : Real))) := by ring
      _ ≤ (8 * chebyshevConstant) *
          ((32 * Real.log (M : Real) ^ 20) *
            (2 * Real.log (M : Real))) := hB
      _ = 512 * chebyshevConstant * Real.log (M : Real) ^ 21 := by ring
  have hD0 :
      0 ≤ actualQ3ScaleCombinedPrefixEnvelope M C c +
        Real.log (M : Real) := by
    unfold actualQ3ScaleCombinedPrefixEnvelope prefixEnvelope
    exact add_nonneg
      (add_nonneg
        (mul_nonneg chebyshevConstant_pos.le (Real.sqrt_nonneg _))
        (mul_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg M))
            (Real.exp_pos _).le)))
      hlog0
  have hs1 : (1 : Real) ≤ Real.sqrt (M : Real) := by
    have hm1 : (1 : Real) ≤ M := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hM.ne')
    nlinarith [Real.sq_sqrt hm.le, Real.sqrt_nonneg (M : Real)]
  have hThird0 :
      0 ≤ 512 * chebyshevConstant * Real.log (M : Real) ^ 22 := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) chebyshevConstant_pos.le)
      (pow_nonneg hlog0 22)
  have hEnvelopeEq :
      actualQ3UnitDifferenceScaleEnvelope M q
          (actualQ3ScaleCombinedPrefixEnvelope M C c +
            Real.log (M : Real)) =
        (8 * chebyshevConstant * (oddProjectWidth M : Real) *
          (1 + Real.log (M : Real))) *
          (actualQ3ScaleCombinedPrefixEnvelope M C c +
            Real.log (M : Real)) := by
    unfold actualQ3UnitDifferenceScaleEnvelope
    rw [hqR]
    field_simp
    ring
  rw [hEnvelopeEq]
  calc
    (8 * chebyshevConstant * (oddProjectWidth M : Real) *
        (1 + Real.log (M : Real))) *
        (actualQ3ScaleCombinedPrefixEnvelope M C c +
          Real.log (M : Real)) ≤
      (512 * chebyshevConstant * Real.log (M : Real) ^ 21) *
        (actualQ3ScaleCombinedPrefixEnvelope M C c +
          Real.log (M : Real)) :=
      mul_le_mul_of_nonneg_right hWeight hD0
    _ = 512 * chebyshevConstant ^ 2 * Real.log (M : Real) ^ 21 *
          Real.sqrt (M : Real) +
        1024 * chebyshevConstant * C * Real.log (M : Real) ^ 21 *
          (M : Real) * Real.exp (-(c / 2) * Real.sqrt (Real.log (M : Real))) +
        512 * chebyshevConstant * Real.log (M : Real) ^ 22 := by
      unfold actualQ3ScaleCombinedPrefixEnvelope prefixEnvelope
      ring
    _ ≤ actualQ3ScaleProjectMajorant M C c := by
      unfold actualQ3ScaleProjectMajorant
      have hthird :
          512 * chebyshevConstant * Real.log (M : Real) ^ 22 ≤
            512 * chebyshevConstant * Real.log (M : Real) ^ 22 *
              Real.sqrt (M : Real) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 hThird0
      exact add_le_add le_rfl hthird

/-- The normalized q=3 project majorant tends to zero for every positive
source-decay constant. -/
theorem actualQ3ScaleProjectNormalizedMajorant_tendsto_zero
    (C c : Real) (hc : 0 < c) :
    Tendsto (fun M : Nat =>
      actualQ3ScaleProjectNormalizedMajorant M C c) atTop (𝓝 0) := by
  have h21 :=
    (log_power_exp_div_sqrt_tendsto_zero 21 0).const_mul
      (512 * chebyshevConstant ^ 2)
  have hdecay :=
    ((log_power_sqrt_exp_decay 21 (c / 2) (by positivity)).comp
      tendsto_natCast_atTop_atTop).const_mul
        (1024 * chebyshevConstant * C)
  have h22 :=
    (log_power_exp_div_sqrt_tendsto_zero 22 0).const_mul
      (512 * chebyshevConstant)
  have h := h21.add hdecay |>.add h22
  simpa [actualQ3ScaleProjectNormalizedMajorant, Function.comp_def,
    Real.exp_zero, mul_assoc] using h

/-- For every positive reserve proportion, the literal source-matched q=3
project debit is eventually strictly absorbed. -/
theorem eventually_actualQ3ScaleProjectEnvelope_lt_linear
    (C c rho : Real) (hC : 0 ≤ C) (hc : 0 < c) (hrho : 0 < rho) :
    ∀ᶠ M : Nat in atTop,
      ∀ q : PairedOddBase (oddProjectRadius M), q.val.val = 3 →
        actualQ3UnitDifferenceScaleEnvelope M q
            (actualQ3ScaleCombinedPrefixEnvelope M C c +
              Real.log (M : Real)) <
          rho * (M : Real) := by
  have hlt :=
    (actualQ3ScaleProjectNormalizedMajorant_tendsto_zero C c hc).eventually_lt_const hrho
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hlt, hlog, eventually_gt_atTop (0 : Nat)] with M hnorm hlogM hM
  intro q hq
  have hmajor := actualQ3UnitDifferenceScaleEnvelope_combined_le_majorant
    M hM q hq C c hC hlogM
  rw [actualQ3ScaleProjectMajorant_eq_mul_normalized M hM C c] at hmajor
  have hm : (0 : Real) < M := by exact_mod_cast hM
  exact hmajor.trans_lt <| by
    rw [mul_comm rho]
    exact mul_lt_mul_of_pos_left hnorm hm

end GoldbachCircleMethodActualQ3ScaleProjectAbsorptionV18766
