import GoldbachCircleMethodActualQ3TriangularPairCarrierPullbackV18750
import GoldbachCircleMethodActualQ3EndpointSpectralBudgetV18745

/-!
# V1.8.751: actual q=3 triangular reduction to one-dimensional Lambda modes

The V1.8.750 obstruction is a literal triangular odd--odd von-Mangoldt pair
sum.  This append-only successor factors that triangle exactly into two
one-dimensional incomplete additive modes modulo three.  It then proves the
precise conditional norm transfer from a uniform one-dimensional prefix
ceiling to the adverse triangular debit.

No prefix ceiling is asserted or inhabited.  In particular, the available
Chebyshev size estimate is not relabelled as cancellation.  No prime number
theorem in progressions, absorption theorem, exceptional-set estimate, or
Goldbach conclusion is proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3TriangularOneDimensionalModeReductionV18751

open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualQ3PairFourierFactorizationV18743
open GoldbachCircleMethodActualQ3UnitModeSquareBudgetV18744
open GoldbachCircleMethodActualQ3EndpointSpectralBudgetV18745
open GoldbachCircleMethodActualQ3SourceBudgetScaleAuditV18738
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748
open GoldbachCircleMethodActualQ3TriangularPairCarrierPullbackV18750

/-- Genuine odd-von-Mangoldt additive mode on a variable initial segment of
the fixed carrier. -/
noncomputable def oddLambdaQ3Prefix
    (M B : Nat) (xi : ZMod 3) : Complex :=
  ∑ b ∈ oddCarrier M,
    if b < B then
      (ArithmeticFunction.vonMangoldt b : Complex) *
        ZMod.stdAddChar ((b : ZMod 3) * xi)
    else 0

/-- One unit-frequency component of the literal triangular pair transform. -/
noncomputable def actualQ3TriangularPairMode
    (M n k : Nat) (xi : ZMod 3) : Complex :=
  ∑ ab ∈ actualOddOddPairCarrier M,
    if oddOddHalfSum ab < k then
      (lambdaPairWeight ab : Complex) *
        ZMod.stdAddChar
          (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3) * xi)
    else 0

/-- On the odd--odd carrier, the half-sum triangle is exactly a one-sided
cutoff in the second coordinate. -/
theorem oddOddHalfSum_lt_iff_second_lt_two_mul_sub
    (M k a b : Nat)
    (ha : a ∈ oddCarrier M)
    (hb : b ∈ oddCarrier M) :
    oddOddHalfSum (a, b) < k ↔ b < 2 * k - a := by
  have hab : (a, b) ∈ actualOddOddPairCarrier M :=
    Finset.mem_product.mpr ⟨ha, hb⟩
  have hsum := oddOddHalfSum_eq_iff_sum_eq_two_mul
    M (oddOddHalfSum (a, b)) (a, b) hab
  have heq : a + b = 2 * oddOddHalfSum (a, b) := hsum.mp rfl
  omega

/-- Exact Fubini factorization of a triangular pair mode into an outer odd
Lambda sum and a one-dimensional incomplete q=3 mode. -/
theorem actualQ3TriangularPairMode_eq_outer_prefix
    (M n k : Nat) (xi : ZMod 3) :
    actualQ3TriangularPairMode M n k xi =
      ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * xi) *
        (∑ a ∈ oddCarrier M,
          ((ArithmeticFunction.vonMangoldt a : Complex) *
              ZMod.stdAddChar ((a : ZMod 3) * xi)) *
            oddLambdaQ3Prefix M (2 * k - a) xi) := by
  unfold actualQ3TriangularPairMode actualOddOddPairCarrier lambdaPairWeight
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simp_rw [Complex.ofReal_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  unfold oddLambdaQ3Prefix
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [q3PairPhase_factor]
  have hiff := oddOddHalfSum_lt_iff_second_lt_two_mul_sub M k a b ha hb
  by_cases htri : oddOddHalfSum (a, b) < k
  · have hbk : b < 2 * k - a := hiff.mp htri
    simp only [htri, hbk, if_true]
    ring
  · have hbk : ¬ b < 2 * k - a := fun h => htri (hiff.mpr h)
    simp [htri, hbk]

/-- Pointwise enumeration of the two unit additive phases modulo three. -/
theorem unitCharacterSum_three_eq_two_unit_phases (x : ZMod 3) :
    @unitCharacterSum 3 ⟨by norm_num⟩ x =
      ZMod.stdAddChar (x * (1 : ZMod 3)) +
        ZMod.stdAddChar (x * (2 : ZMod 3)) := by
  unfold unitCharacterSum
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv]
  have h01 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h12 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  rw [Finset.sum_insert h01, Finset.sum_insert h12,
    Finset.sum_singleton]
  simp only [show ¬ IsUnit (0 : ZMod 3) by decide, if_false,
    show IsUnit (1 : ZMod 3) by decide, if_true,
    show IsUnit (2 : ZMod 3) by decide, zero_add]

/-- Concrete enumeration of the two nonzero frequencies modulo three. -/
theorem actualQ3RawTriangularPairPrefix_eq_two_modes
    (M n k : Nat) :
    actualQ3RawTriangularPairPrefix M n k =
      actualQ3TriangularPairMode M n k (1 : ZMod 3) +
        actualQ3TriangularPairMode M n k (2 : ZMod 3) := by
  unfold actualQ3RawTriangularPairPrefix actualQ3TriangularPairMode
  calc
    (∑ ab ∈ actualOddOddPairCarrier M,
        if oddOddHalfSum ab < k then
          (lambdaPairWeight ab : Complex) *
            @unitCharacterSum 3 ⟨by norm_num⟩
              (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3))
        else 0) =
      ∑ ab ∈ actualOddOddPairCarrier M,
        ((if oddOddHalfSum ab < k then
            (lambdaPairWeight ab : Complex) *
              ZMod.stdAddChar
                (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3) *
                  (1 : ZMod 3))
          else 0) +
        (if oddOddHalfSum ab < k then
            (lambdaPairWeight ab : Complex) *
              ZMod.stdAddChar
                (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3) *
                  (2 : ZMod 3))
          else 0)) := by
        apply Finset.sum_congr rfl
        intro ab _hab
        by_cases htri : oddOddHalfSum ab < k
        · simp only [htri, if_true]
          rw [unitCharacterSum_three_eq_two_unit_phases]
          ring
        · simp [htri]
    _ = (∑ ab ∈ actualOddOddPairCarrier M,
          if oddOddHalfSum ab < k then
            (lambdaPairWeight ab : Complex) *
              ZMod.stdAddChar
                (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3) *
                  (1 : ZMod 3))
          else 0) +
        (∑ ab ∈ actualOddOddPairCarrier M,
          if oddOddHalfSum ab < k then
            (lambdaPairWeight ab : Complex) *
              ZMod.stdAddChar
                (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3) *
                  (2 : ZMod 3))
          else 0) := Finset.sum_add_distrib

/-- The exact open arithmetic contract: both nonzero q=3 odd-Lambda modes
must be uniformly bounded on every finite prefix. -/
def ActualOddLambdaQ3PrefixCeiling (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧
    ∀ (B : Nat) (xi : ZMod 3), IsUnit xi →
      ‖oddLambdaQ3Prefix M B xi‖ ≤ D

/-- One triangular mode costs at most total odd Lambda mass times the supplied
one-dimensional prefix ceiling. -/
theorem actualQ3TriangularPairMode_norm_le
    (M n k : Nat) (xi : ZMod 3) (D : Real)
    (hxi : IsUnit xi)
    (hD : ActualOddLambdaQ3PrefixCeiling M D) :
    ‖actualQ3TriangularPairMode M n k xi‖ ≤ oddLambdaSum M * D := by
  rw [actualQ3TriangularPairMode_eq_outer_prefix]
  rw [norm_mul, norm_q3_targetPhase_eq_one, one_mul]
  calc
    _ ≤ ∑ a ∈ oddCarrier M,
        ‖((ArithmeticFunction.vonMangoldt a : Complex) *
              ZMod.stdAddChar ((a : ZMod 3) * xi)) *
            oddLambdaQ3Prefix M (2 * k - a) xi‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ oddCarrier M,
        ArithmeticFunction.vonMangoldt a * D := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul, norm_mul]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hchar : ‖ZMod.stdAddChar ((a : ZMod 3) * xi)‖ = 1 := by simp
      rw [hchar, mul_one]
      exact mul_le_mul_of_nonneg_left
        (hD.2 (2 * k - a) xi hxi)
        ArithmeticFunction.vonMangoldt_nonneg
    _ = oddLambdaSum M * D := by
      unfold oddLambdaSum
      rw [Finset.sum_mul]

/-- The complete raw triangle is controlled by exactly two such one-variable
prefix channels. -/
theorem actualQ3RawTriangularPairPrefix_norm_le
    (M n k : Nat) (D : Real)
    (hD : ActualOddLambdaQ3PrefixCeiling M D) :
    ‖actualQ3RawTriangularPairPrefix M n k‖ ≤
      2 * oddLambdaSum M * D := by
  rw [actualQ3RawTriangularPairPrefix_eq_two_modes]
  calc
    _ ≤ ‖actualQ3TriangularPairMode M n k (1 : ZMod 3)‖ +
        ‖actualQ3TriangularPairMode M n k (2 : ZMod 3)‖ := norm_add_le _ _
    _ ≤ oddLambdaSum M * D + oddLambdaSum M * D :=
      add_le_add
        (actualQ3TriangularPairMode_norm_le M n k (1 : ZMod 3) D (by decide) hD)
        (actualQ3TriangularPairMode_norm_le M n k (2 : ZMod 3) D (by decide) hD)
    _ = 2 * oddLambdaSum M * D := by ring

/-- After exact centering, the only extra cost is the bounded three-periodic
constant prefix. -/
theorem actualQ3CenteredTriangularPairPrefix_norm_le
    (M n k : Nat) (D : Real)
    (hD : ActualOddLambdaQ3PrefixCeiling M D) :
    ‖actualQ3CenteredTriangularPairPrefix M n k‖ ≤
      2 * oddLambdaSum M * D + 4 * actualLambdaPairSourceMean M := by
  unfold actualQ3CenteredTriangularPairPrefix
  calc
    _ ≤ ‖actualQ3RawTriangularPairPrefix M n k‖ +
        ‖(actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k‖ :=
      norm_sub_le _ _
    _ ≤ 2 * oddLambdaSum M * D +
        4 * actualLambdaPairSourceMean M := by
      apply add_le_add
      · exact actualQ3RawTriangularPairPrefix_norm_le M n k D hD
      · rw [norm_mul]
        have hMean := actualLambdaPairSourceMean_nonneg_local M
        have hConst := q3ConstantPrefix_norm_le_four n k
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hMean]
        calc
          actualLambdaPairSourceMean M * ‖q3ConstantPrefix n k‖ ≤
              actualLambdaPairSourceMean M * 4 :=
            mul_le_mul_of_nonneg_left hConst hMean
          _ = 4 * actualLambdaPairSourceMean M := by ring

/-- Exact source-specific norm transfer for the whole triangular Abel
remainder.  The premise is now only the one-dimensional q=3 prefix ceiling. -/
theorem actualQ3TriangularPrefixRemainder_norm_le_oneDimensional
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3)
    (D : Real)
    (hD : ActualOddLambdaQ3PrefixCeiling M D) :
    ‖actualQ3TriangularPrefixRemainder M q n‖ ≤
      (∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖) *
        (2 * oddLambdaSum M * D +
          4 * actualLambdaPairSourceMean M) := by
  rw [actualQ3TriangularPrefixRemainder_eq_pairPrefixes M q n hq]
  rw [norm_neg]
  calc
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a *
          actualQ3CenteredTriangularPairPrefix M n (a + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
          (2 * oddLambdaSum M * D +
            4 * actualLambdaPairSourceMean M) := by
      apply Finset.sum_le_sum
      intro a _ha
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (actualQ3CenteredTriangularPairPrefix_norm_le M n (a + 1) D hD)
        (norm_nonneg _)
    _ = (∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖) *
        (2 * oddLambdaSum M * D +
          4 * actualLambdaPairSourceMean M) := by
      rw [Finset.sum_mul]

/-- Final sign-sensitive project gate.  The antecedent is the exact numerical
inequality still requiring arithmetic evidence for the genuine source. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_oneDimensionalPrefixCeiling
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (D : Real)
    (hD : ActualOddLambdaQ3PrefixCeiling M D)
    (hAbsorb :
      (∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖) *
          (2 * oddLambdaSum M * D +
            4 * actualLambdaPairSourceMean M) <
        actualQ3PairResidueProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  apply projectReserve_add_negativeAggregate_re_pos_of_triangularSignDebit_lt_pairResidueReserve
    M q n hTarget hq
  have hDebit := actualQ3TriangularPrefixSignDebit_le_norm M q n
  have hNorm := actualQ3TriangularPrefixRemainder_norm_le_oneDimensional
    M q n hq D hD
  exact lt_of_le_of_lt (hDebit.trans hNorm) hAbsorb

end GoldbachCircleMethodActualQ3TriangularOneDimensionalModeReductionV18751
