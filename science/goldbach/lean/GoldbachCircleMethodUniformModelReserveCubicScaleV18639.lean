import GoldbachCircleMethodActualChannelProjectBudgetV18638

/-!
# V1.8.639: concrete cubic-scale inhabitation of the discrete model reserve

This module removes the free discrete-model reserve premise from the exact
V1.8.638 channel budget at the concrete scale `P = 8 * R^2`.  The proof uses
only the already kernel-checked finite discrete arc reserve from V1.8.55 and
the explicit elementary scale conditions `32 ≤ M`, `1 ≤ R`, and
`16 * R^3 < M`.

`RealVaughanEstimate C`, the local Major approximation, and the logarithmic
prime-power scale gate remain explicit premises.  No analytic input is
inhabited here, no exception-set decay is proved, and no Goldbach theorem is
claimed.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodDiscreteMainKernelV1852
open GoldbachCircleMethodDiscreteArcModelReserveV1855
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodMajorOperatorErrorEnergyV18634
open GoldbachCircleMethodActualChannelProjectBudgetV18638

namespace GoldbachCircleMethodUniformModelReserveCubicScaleV18639

/-- The fixed scale used to make the V1.8.55 finite reserve quantitative. -/
def cubicModelScale (R : ℕ) : ℕ := 8 * R ^ 2

theorem cubicModelScale_pos (R : ℕ) (hR : 1 ≤ R) :
    0 < cubicModelScale R := by
  simp only [cubicModelScale]
  positivity

theorem cubicModelScale_window
    (M R : ℕ) (hcubic : 16 * R ^ 3 < M) :
    2 * cubicModelScale R * R < M := by
  calc
    2 * cubicModelScale R * R = 16 * R ^ 3 := by
      simp only [cubicModelScale]
      ring
    _ < M := hcubic

theorem cubicModelScale_le_scale
    (M R : ℕ) (hR : 1 ≤ R) (hcubic : 16 * R ^ 3 < M) :
    cubicModelScale R ≤ M := by
  have hwindow := cubicModelScale_window M R hcubic
  have hle : cubicModelScale R ≤ 2 * cubicModelScale R * R := by
    calc
      cubicModelScale R ≤ 2 * cubicModelScale R := by omega
      _ = (2 * cubicModelScale R) * 1 := by simp
      _ ≤ (2 * cubicModelScale R) * R := Nat.mul_le_mul_left _ hR
  exact hle.trans (Nat.le_of_lt hwindow)

theorem cubicModelScale_real_cap
    (M R : ℕ) (hR : 1 ≤ R) (hcubic : 16 * R ^ 3 < M) :
    2 * (cubicModelScale R : ℝ) ≤ (M : ℝ) := by
  have hwindow := cubicModelScale_window M R hcubic
  have hle : 2 * cubicModelScale R ≤ M := by
    calc
      2 * cubicModelScale R = (2 * cubicModelScale R) * 1 := by simp
      _ ≤ (2 * cubicModelScale R) * R := Nat.mul_le_mul_left _ hR
      _ ≤ M := Nat.le_of_lt hwindow
  exact_mod_cast hle

theorem cubicModelScale_budget
    (M R : ℕ) (hM : 32 ≤ M) (hR : 1 ≤ R) :
    (2 / 7 : ℝ) +
        ((M : ℝ) / (2 * (cubicModelScale R : ℝ))) * (R : ℝ) ^ 2 ≤
      (M : ℝ) / 14 := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
  have hcancel :
      ((M : ℝ) / (2 * (cubicModelScale R : ℝ))) * (R : ℝ) ^ 2 =
        (M : ℝ) / 16 := by
    simp only [cubicModelScale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    field_simp
    norm_num
  rw [hcancel]
  have hMreal : (32 : ℝ) ≤ M := by exact_mod_cast hM
  linarith

/-- The formerly free V1.8.638 model-reserve premise is inhabited uniformly
on the exact even target block at the explicit cubic scale. -/
theorem uniform_discrete_model_reserve_cubic_scale
    (M R : ℕ) (hM : 32 ≤ M) (hR : 1 ≤ R)
    (hcubic : 16 * R ^ 3 < M) :
    ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤
        discreteArcMainModel M N R (cubicModelScale R) := by
  intro N hN
  rcases (mem_evenTargetBlock_iff M N).mp hN with
    ⟨hN4, hNM, hEven, hMN⟩
  have hblock : (M : ℝ) / 2 ≤ (N : ℝ) := by
    have hMNreal : (M : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hMN
    linarith
  exact discreteArcMainModel_ge_one_fourteenth M N R (by omega) hNM hEven hR
    hblock (cubicModelScale R) (by exact_mod_cast cubicModelScale_pos R hR)
    (cubicModelScale_real_cap M R hR hcubic)
    (cubicModelScale_budget M R hM hR)

/-- V1.8.638 with the model reserve and all elementary scale obligations
discharged at `P = 8 * R^2`.  The two analytic source premises remain visible. -/
theorem exception_card_mul_threshold_sq_le_explicitProjectBudget_cubic_scale
    (C ε : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (M R : ℕ) (hM : 32 ≤ M) (hR : 1 ≤ R)
    (hcubic : 16 * R ^ 3 < M) (hε : 0 ≤ ε)
    (hScale : 112 * (Real.log (M : ℝ)) ^ 2 ≤ Real.sqrt (M : ℝ))
    (happrox : ∀ i : ReducedRationalIndex R,
      ∀ x ∈ Metric.closedBall (majorArcCenter i)
          (twoScaleArcRadius M (cubicModelScale R) i),
        ‖exponentialSum M.succ x -
          (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ) /
            (Nat.totient i.val.1 : ℂ)) *
              discreteMainPolynomial M (x - majorArcCenter i)‖ ≤ ε) :
    ((((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) *
        ((M : ℝ) / 28) ^ 2) ≤
      2 * (majorOperatorErrorEnvelope M ε) ^ 2 +
        2 * chebyshevFourthBudget M (cubicModelScale R) R C := by
  exact exception_card_mul_threshold_sq_le_explicitProjectBudget
    C ε hC hV M (cubicModelScale R) R (by omega)
    (cubicModelScale_pos R hR) (cubicModelScale_le_scale M R hR hcubic)
    hR (cubicModelScale_window M R hcubic) hε hScale
    (uniform_discrete_model_reserve_cubic_scale M R hM hR hcubic) happrox

end GoldbachCircleMethodUniformModelReserveCubicScaleV18639
