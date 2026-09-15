import GoldbachCircleMethodPrincipalDiagonalCoefficientBoundV18498
import GoldbachCircleMethodRealWeightCompanionReflectionV18491
import GoldbachCircleMethodFiniteIntervalRemainderReserveV18229

/-!
# Goldbach V1.8.499: explicit sparse principal-block bound

The exact principal-block transfer and its linear diagonal budget are combined.
For the canonical logarithmic weight this removes all abstract envelopes from
the principal correction.  The retained quartic endpoint term is stated
literally and is not declared negligible here.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodPrincipalBlockExplicitBoundV18499

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodSupportSeparatedCoefficientMomentsV18490
open GoldbachCircleMethodRealWeightCompanionReflectionV18491
open GoldbachCircleMethodPrincipalBlockCoefficientBoundV18497
open GoldbachCircleMethodPrincipalDiagonalCoefficientBoundV18498
open GoldbachCircleMethodFiniteIntervalRemainderReserveV18229
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

/-- A real norm-one weight gives an explicit principal-block budget. -/
theorem blockPrincipalCoefficientMoment_le_explicit
    (Q B : ℕ) (hQ : 1 ≤ Q) (w : ℕ → ℂ)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (hw : ∀ n : ℕ, ‖w n‖ ≤ 1) :
    blockPrincipalCoefficientMoment Q B w ≤
      ((B + 1 : ℕ) : ℝ) * (Q : ℝ) + 2 * (Q : ℝ) ^ 4 := by
  have hbase := blockPrincipalCoefficientMoment_le_diagonal_add_quartic
    Q B hQ w hwReal 1 zero_le_one (by
      intro q _hsupport
      exact hw ((oneLevel hQ).val * q.val))
  have hdiag := principal_diagonal_sum_le_cutoff Q hQ w hw
  calc
    blockPrincipalCoefficientMoment Q B w ≤
        ((B + 1 : ℕ) : ℝ) * (∑ q : PositiveLevel Q,
          ‖GoldbachCircleMethodActualCompanionCompleteDiagonalV18204.literalCoefficient
              (oneLevel hQ) q w‖ ^ 2 * (q.val.totient : ℝ)) +
          2 * (Q : ℝ) ^ 4 * 1 * 1 := hbase
    _ ≤ ((B + 1 : ℕ) : ℝ) * (Q : ℝ) +
          2 * (Q : ℝ) ^ 4 * 1 * 1 := by
      gcongr
    _ = ((B + 1 : ℕ) : ℝ) * (Q : ℝ) + 2 * (Q : ℝ) ^ 4 := by ring

/-- Canonical specialization: the principal sparse correction is bounded by
`(B+1)Q + 2Q^4` with no additional hypothesis. -/
theorem canonical_blockPrincipalCoefficientMoment_le
    (Q B : ℕ) (hQ : 1 ≤ Q) (R : ℝ) :
    blockPrincipalCoefficientMoment Q B
        (logWeight R canonicalLogBump) ≤
      ((B + 1 : ℕ) : ℝ) * (Q : ℝ) + 2 * (Q : ℝ) ^ 4 := by
  exact blockPrincipalCoefficientMoment_le_explicit Q B hQ
    (logWeight R canonicalLogBump)
    (star_logWeight R canonicalLogBump)
    (norm_logWeight_canonical_le_one R)

end GoldbachCircleMethodPrincipalBlockExplicitBoundV18499
