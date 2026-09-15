import GoldbachCircleMethodSubunitFourthMomentGateV18625

/-!
# V1.8.626: sign-sensitive subunit decision gate

The total minor fourth moment in V1.8.625 is only a sufficient Bessel
majorant. The smaller exact object needed by the finite transfer is the squared
negative-part moment of the actual minor Fourier coefficients. This module
proves its exact strict threshold for an empty even target block.

No estimate of that sign-sensitive moment is supplied here.
`proof_status = NO_PROOF`.
-/
set_option autoImplicit false
open scoped Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833

namespace GoldbachCircleMethodNegativePartSubunitGateV18626

/-- A strict `M^2/784` bound for the exact negative-part squared moment,
together with the already isolated Major and defect gates, empties the literal
non-Goldbach subset of the current even block. -/
theorem evenBlock_goldbachExceptions_empty_of_negativePartMoment
    (M P R₀ : ℕ)
    (hLarge : defectScaleThreshold ≤ M)
    (hMajor : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ twoScaleMajorIntegralReal M P R₀ N)
    (hMoment : negativePartSquaredMoment (evenTargetBlock M)
      (twoScaleMinorIntegralReal M P R₀) < (M : ℝ)^2 / 784) :
    (evenTargetBlock M).filter (fun N => ¬ GoldbachAt N) = ∅ := by
  have hMpos : (0 : ℝ) < M := by
    have hExp : Real.exp 40 ≤ (M : ℝ) :=
      (Nat.le_ceil (Real.exp 40)).trans (by exact_mod_cast hLarge)
    exact (Real.exp_pos 40).trans_le hExp
  have hDen : 4 * (M : ℝ)^2 ≠ 0 := by positivity
  have hMomentIdentity :
      negativePartSquaredMoment (evenTargetBlock M)
          (twoScaleMinorIntegralReal M P R₀) =
        4 * (M : ℝ)^2 *
          (negativePartSquaredMoment (evenTargetBlock M)
            (twoScaleMinorIntegralReal M P R₀) / (4 * (M : ℝ)^2)) := by
    rw [mul_div_cancel₀ _ hDen]
  have hCard := evenBlock_exceptions_card_le_3136_of_threshold
    M P R₀
      (negativePartSquaredMoment (evenTargetBlock M)
        (twoScaleMinorIntegralReal M P R₀) / (4 * (M : ℝ)^2))
      hLarge hMajor hMomentIdentity.le
  have hScaled :
      negativePartSquaredMoment (evenTargetBlock M)
        (twoScaleMinorIntegralReal M P R₀) * 784 < (M : ℝ)^2 :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < 784)).mp hMoment
  have hTarget :
      3136 *
        (negativePartSquaredMoment (evenTargetBlock M)
          (twoScaleMinorIntegralReal M P R₀) / (4 * (M : ℝ)^2)) < 1 := by
    calc
      _ = (3136 * negativePartSquaredMoment (evenTargetBlock M)
          (twoScaleMinorIntegralReal M P R₀)) / (4 * (M : ℝ)^2) := by ring
      _ < 1 := (div_lt_one (by positivity : (0 : ℝ) < 4 * (M : ℝ)^2)).mpr (by
        nlinarith)
  have hCardLt :
      (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) < 1 :=
    hCard.trans_lt hTarget
  have hCardLtNat :
      ((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card < 1 := by
    exact_mod_cast hCardLt
  have hCardZero :
      ((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card = 0 := by
    omega
  exact Finset.card_eq_zero.mp hCardZero

end GoldbachCircleMethodNegativePartSubunitGateV18626
