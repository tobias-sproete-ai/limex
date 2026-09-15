import GoldbachCircleMethodSubunitDecisionGateV18624
import GoldbachCircleMethodTwoScaleBesselBridgeV1834

/-!
# V1.8.625: exact fourth-moment threshold for an empty even block

The existing Bessel/Markov transfer becomes a decision theorem on one dyadic
block only when the actual minor fourth moment is strictly below `M^2 / 784`,
in addition to the frozen Major reserve and defect threshold.

This module proves the transfer but supplies none of those analytic premises.
It is therefore a target interface, not a Goldbach proof.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false
open scoped Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodTwoScaleBesselBridgeV1834

namespace GoldbachCircleMethodSubunitFourthMomentGateV18625

/-- Strictly subcritical actual minor fourth moment forces the literal
non-Goldbach subset of the even target block to be empty. -/
theorem evenBlock_goldbachExceptions_empty_of_subunit_fourthMoment
    (M P R₀ : ℕ)
    (hLarge : defectScaleThreshold ≤ M)
    (hMajor : ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ twoScaleMajorIntegralReal M P R₀ N)
    (hFourth : minorFourthMoment M P R₀ < (M : ℝ)^2 / 784) :
    (evenTargetBlock M).filter (fun N => ¬ GoldbachAt N) = ∅ := by
  have hMpos : (0 : ℝ) < M := by
    have hExp : Real.exp 40 ≤ (M : ℝ) :=
      (Nat.le_ceil (Real.exp 40)).trans (by exact_mod_cast hLarge)
    exact (Real.exp_pos 40).trans_le hExp
  have hDen : 4 * (M : ℝ)^2 ≠ 0 := by positivity
  have hMomentIdentity :
      minorFourthMoment M P R₀ =
        4 * (M : ℝ)^2 * (minorFourthMoment M P R₀ / (4 * (M : ℝ)^2)) := by
    rw [mul_div_cancel₀ _ hDen]
  have hCard := evenBlock_exceptions_card_le_3136_of_fourthMoment
    M P R₀ (minorFourthMoment M P R₀ / (4 * (M : ℝ)^2))
      hLarge hMajor hMomentIdentity.le
  have hScaled :
      minorFourthMoment M P R₀ * 784 < (M : ℝ)^2 :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < 784)).mp hFourth
  have hTarget :
      3136 * (minorFourthMoment M P R₀ / (4 * (M : ℝ)^2)) < 1 := by
    calc
      _ = (3136 * minorFourthMoment M P R₀) / (4 * (M : ℝ)^2) := by ring
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

end GoldbachCircleMethodSubunitFourthMomentGateV18625
