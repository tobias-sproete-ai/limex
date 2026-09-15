import GoldbachCircleMethodVariableUnitPairExactCorrectionV18344

/-!
# V1.8.345: scalar factorization of the exact variable correction

V1.8.344 identifies the variable unit-pair deficit with the real part of an
exact mixed Ramanujan/character correction.  This module factors that
correction into two scalar weight sums.  The carrier cardinality does not
appear in either scalar channel.

No sign or analytic smallness is claimed.  The factorization is the finite
algebraic interface for the subsequent unit/nonunit arithmetic case split.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableUnitPairCorrectionFactorizationV18345

open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodVariableUnitPairExactCorrectionV18344

/-- Sum of the two one-sided power weights. -/
noncomputable def variableLinearPowerWeightSum
    (N A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    ((powerWeight b (N - (A + i)) : ℂ) +
      (powerWeight b (A + i) : ℂ))

/-- Sum of the products of the two one-sided power weights. -/
noncomputable def variableQuadraticPowerWeightSum
    (N A T : ℕ) (b : ℝ) : ℂ :=
  ∑ i ∈ Finset.range T,
    (powerWeight b (N - (A + i)) : ℂ) *
      (powerWeight b (A + i) : ℂ)

/-- Exact two-channel factorization of the V1.8.344 correction. -/
theorem variableUnitPairCorrectionSum_eq_scalar_channels
    (r N A T : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r) (b : ℝ) :
    variableUnitPairCorrectionSum r N A T chi b =
      variableLinearPowerWeightSum N A T b *
          ((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi (N : ZMod r) -
        variableQuadraticPowerWeightSum N A T b * chi (-1) *
          unitCharacterSum r (N : ZMod r) := by
  unfold variableUnitPairCorrectionSum variableLinearPowerWeightSum
    variableQuadraticPowerWeightSum
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_mul]

end GoldbachCircleMethodVariableUnitPairCorrectionFactorizationV18345
