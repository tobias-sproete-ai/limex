import GoldbachCircleMethodArithmeticFactorDivisorBoundV18416

/-!
# Goldbach V1.8.417: one scalar divisor envelope for the central sweep

The targetwise arithmetic-factor condition from V1.8.415 is reduced to one
explicit scalar condition over the whole central block.  The only imported
number-theoretic growth statement remains the declared divisor-function bound.

No character-family estimate and no Goldbach theorem is proved here.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCentralDivisorEnvelopeV18417

open GoldbachCircleMethodArithmeticFactorDivisorBoundV18416
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCenteredDimensionlessBudgetV18411
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodBadPrimeUniformFrequencyV18169
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodMertensProductFromHarmonicV18174
open GoldbachCircleMethodRadicalCorrelationTransferV18161

/-- All targets in the central sweep are positive and at most `14*m`. -/
theorem centralTargetNat_pos_le_fourteen_mul
    (m i : ℕ) (hm : 1 ≤ m) (hi : i < 2 * m + 1) :
    0 < centralTargetNat m i ∧ centralTargetNat m i ≤ 14 * m := by
  simp only [centralTargetNat]
  omega

/-- The dimensionless centered-correction coefficient is nonnegative under
the sign conditions already carried by the central bridge. -/
theorem centeredCorrectionDimensionlessCoefficient_nonneg
    (CE CB D c CH rho : ℝ)
    (hCE : 0 ≤ CE) (hCB : 0 ≤ CB) (hCH : 0 ≤ CH) (hrho : 0 < rho) :
    0 ≤ centeredCorrectionDimensionlessCoefficient CE CB D c CH rho := by
  unfold centeredCorrectionDimensionlessCoefficient
  have hJ : 0 < tenthDecayMass := tenthDecayMass_pos
  have hMC : 0 < mertensProductConstant D c := mertensProductConstant_pos D c
  have hOC : 0 < oneFrequencyConstant D c := oneFrequencyConstant_pos D c
  positivity

/-- A global divisor subpower bound yields one uniform arithmetic envelope for
every target in the central sweep. -/
theorem central_arithmeticFactor_le_subpower_envelope
    (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 ≤ eps)
    (hdivisor : ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ eps)
    (m i : ℕ) (hm : 1 ≤ m) (hi : i < 2 * m + 1) :
    arithmeticFactor (centralTargetNat m i) ≤
      C * ((14 * m : ℕ) : ℝ) ^ eps := by
  obtain ⟨hpos, hle⟩ := centralTargetNat_pos_le_fourteen_mul m i hm hi
  have hbase : ((centralTargetNat m i : ℕ) : ℝ) ≤ ((14 * m : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hrpow : ((centralTargetNat m i : ℕ) : ℝ) ^ eps ≤
      ((14 * m : ℕ) : ℝ) ^ eps :=
    Real.rpow_le_rpow (by positivity) hbase heps
  calc
    arithmeticFactor (centralTargetNat m i) ≤
        C * ((centralTargetNat m i : ℕ) : ℝ) ^ eps :=
      arithmeticFactor_subpower_of_divisor_bound C eps hdivisor hpos
    _ ≤ C * ((14 * m : ℕ) : ℝ) ^ eps :=
      mul_le_mul_of_nonneg_left hrpow hC

/-- One scalar inequality implies every targetwise smallness premise required
by the central literal source bridge. -/
theorem central_targetwise_smallness_of_divisor_envelope
    (CE CB D c CH rho A C eps : ℝ)
    (hCE : 0 ≤ CE) (hCB : 0 ≤ CB) (hCH : 0 ≤ CH) (hrho : 0 < rho)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (heps : 0 ≤ eps)
    (hdivisor : ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ eps)
    (m : ℕ) (hm : 1 ≤ m)
    (hscalar :
      (2 * A) * (C * ((14 * m : ℕ) : ℝ) ^ eps) *
          centeredCorrectionDimensionlessCoefficient CE CB D c CH rho <
        (1 : ℝ) / 2048) :
    ∀ i ∈ Finset.range (2 * m + 1),
      (2 * A) * arithmeticFactor (centralTargetNat m i) *
          centeredCorrectionDimensionlessCoefficient CE CB D c CH rho <
        (1 : ℝ) / 2048 := by
  intro i hi
  have hfactor := central_arithmeticFactor_le_subpower_envelope
    C eps hC heps hdivisor m i hm (Finset.mem_range.mp hi)
  have h2A : 0 ≤ 2 * A := mul_nonneg (by norm_num) hA
  have hcoef : 0 ≤ centeredCorrectionDimensionlessCoefficient CE CB D c CH rho :=
    centeredCorrectionDimensionlessCoefficient_nonneg CE CB D c CH rho
      hCE hCB hCH hrho
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfactor h2A) hcoef
  exact hmul.trans_lt hscalar

end GoldbachCircleMethodCentralDivisorEnvelopeV18417
