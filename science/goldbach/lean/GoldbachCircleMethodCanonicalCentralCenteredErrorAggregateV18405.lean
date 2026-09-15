import GoldbachCircleMethodCanonicalCentralSourceTransferV18404
import GoldbachCircleMethodAdjustedCenteredCorrectionNumericAbsorptionV18254

/-!
# Goldbach V1.8.405: canonical central centered-error aggregate

The existing targetwise adjusted centered-correction absorption theorem is
summed over the V1.8.403 central target sweep.  This sweep was chosen precisely
so that every target satisfies the theorem's `5B <= 4N <= 7B` contract.

All arithmetic-correlation, fluctuation-mass, Mertens-input, and numeric-budget
premises remain explicit.  Under them, the complete centered-error aggregate
is strictly below `B^2/2048`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction

namespace GoldbachCircleMethodCanonicalCentralCenteredErrorAggregateV18405

open GoldbachCircleMethodActiveCharacterRadicalErrorV18158
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActiveResidualExactDecompositionV18251
open GoldbachCircleMethodAdjustedCenteredCorrectionNumericAbsorptionV18254
open GoldbachCircleMethodBadPrimeProductComparisonV18165
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCanonicalCentralSourceTransferV18404
open GoldbachCircleMethodDirectLambdaRadicalDominationV18178
open GoldbachCircleMethodDisjointPrimeFactorCompositionV18171
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodGlobalSieveFiniteFactorV18173
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodMertensUniformConstantsV18168
open GoldbachCircleMethodRadicalCorrelationTransferV18161
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Exact summation of the pointwise V1.8.254 contract over the central sweep.
The constants are selected before the block and active slot. -/
theorem eventual_central_adjusted_centered_error_target_sum_lt_one_over_2048 :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ CB : ℝ, 0 ≤ CB ∧
      ∀ (D c CH : ℝ) (_hD : 0 ≤ D) (_hCH : 0 ≤ CH)
        (_hweighted : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixLogMoment X t - Real.log t| ≤ D)
        (_hharmonic : ∀ (X : ℕ), 2 ≤ X → ∀ t : ℝ, 2 ≤ t → t ≤ (X : ℝ) →
          |prefixHarmonicMoment X t - Real.log (Real.log t) - c| ≤
            D / Real.log t)
        (rho : ℝ) (_hrho : 0 < rho) (_hrho1 : rho ≤ 1),
      ∃ B₀ : ℕ, ∀ (m : ℕ) (_hm : 1 ≤ m) (b eta : ℝ)
        (e : StructurallyAdmissibleActiveSlot
          ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
        B₀ ≤ 8 * m → 0 ≤ b → 0 ≤ eta →
        (∀ i ∈ Finset.range (2 * m + 1), ∀ ξ η' : ℝ,
          arithmeticCorrelation (((8 * m : ℕ) : ℝ) ^ rho) ξ η'
              (Finset.Ioc ((8 * m) / 2) (8 * m)) (centralTargetNat m i) ≤
            CH * (((8 * m : ℕ) : ℝ) / 2) *
              finiteSieveProduct (centralTargetNat m i) ((8 * m) / 2) *
              goodBadProduct (((8 * m : ℕ) : ℝ) ^ rho) ξ η'
                (centralTargetNat m i) ((8 * m) / 2)) →
        (∀ n ∈ blockCarrier (8 * m),
          activeFluctuationMass ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊
            (8 * m) n
            (((8 * m : ℕ) : ℝ) /
              (((8 * m : ℕ) : ℝ) ^ rho) ^ 4)
            b (blockInput (8 * m)) e.val ≤ eta) →
        (∀ i ∈ Finset.range (2 * m + 1),
          adjustedCenteredCorrectionBudgetExpression
            CE CB D c CH rho eta (8 * m) (centralTargetNat m i) <
              ((8 * m : ℕ) : ℝ) / 2048) →
        |centralAdjustedCenteredErrorTargetSum m rho b e| <
          ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
  obtain ⟨CE, hCE, CB, hCB, hcore⟩ :=
    eventual_adjustedCenteredCorrection_subthreshold_of_numeric_budget
  refine ⟨CE, hCE, CB, hCB, ?_⟩
  intro D c CH hD hCH hweighted hharmonic rho hrho hrho1
  obtain ⟨B₀, hbound⟩ :=
    hcore D c CH hD hCH hweighted hharmonic rho hrho hrho1
  refine ⟨B₀, ?_⟩
  intro m hm b eta e hB₀ hb heta hsource hmass hbudget
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (2 * m + 1)) :
      |(canonicalAdjustedCenteredErrorCorrectionAt
          (8 * m) rho b e.val ((centralTargetNat m i : ℕ) : ℤ)).re| ≤
        ((8 * m : ℕ) : ℝ) / 2048 := by
    have hi' : i < 2 * m + 1 := Finset.mem_range.mp hi
    have hnorm := hbound (M := 8 * m) (B := 8 * m)
      (N := centralTargetNat m i) b eta e.val hB₀
      (by simp only [centralTargetNat]; omega)
      (by simp only [centralTargetNat]; omega)
      hb heta (hsource i hi) hmass (hbudget i hi)
    exact (Complex.abs_re_le_norm _).trans (le_of_lt hnorm)
  unfold centralAdjustedCenteredErrorTargetSum
  calc
    |∑ i ∈ Finset.range (2 * m + 1),
        (canonicalAdjustedCenteredErrorCorrectionAt
            (8 * m) rho b e.val ((centralTargetNat m i : ℕ) : ℤ)).re| ≤
      ∑ i ∈ Finset.range (2 * m + 1),
        |(canonicalAdjustedCenteredErrorCorrectionAt
            (8 * m) rho b e.val ((centralTargetNat m i : ℕ) : ℤ)).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (2 * m + 1),
        ((8 * m : ℕ) : ℝ) / 2048 := Finset.sum_le_sum hpoint
    _ < ((8 * m : ℕ) : ℝ) ^ 2 / 2048 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith

end GoldbachCircleMethodCanonicalCentralCenteredErrorAggregateV18405
