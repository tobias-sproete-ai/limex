import GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333
import GoldbachCircleMethodPairwiseMeanDiagonalCompatibilityV18324

/-!
# Goldbach V1.8.334: variable mean diagonal normal form

The Abel route in V1.8.333 reduces the canonical adjusted convolution to a
variable arithmetic mean.  This module identifies that mean pointwise with the
already audited frozen pairwise mean, and then rewrites every summand in the
complete-diagonal normal form from V1.8.324.

The common period occurs only in the arithmetic compatibility identity below.
It is not used in the boundary estimate, whose cost remains the pairwise
`Q^4` budget from V1.8.333.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodVariableMeanDiagonalNormalFormV18334

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodFullFrozenPairwiseIntervalV18323
open GoldbachCircleMethodPairwiseMeanDiagonalCompatibilityV18324
open GoldbachCircleMethodPowerWeightAbelIntervalV18331
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodVariableFourChannelAbelV18330

/-- The variable four-channel mean is exactly the pointwise sum of frozen
pairwise means.  This is a distributive identity, not an estimate. -/
theorem variableFourChannelMean_eq_sum_fullFrozenPairwiseMean
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (u z : ℕ → ℝ) (N T : ℕ) :
    variableFourChannelMean hQ r chi v w u z N T =
      ∑ i ∈ Finset.range T,
        fullFrozenPairwiseMean hQ r chi v w (u i : ℂ) (z i : ℂ) N := by
  unfold variableFourChannelMean fullFrozenPairwiseMean
  apply Finset.sum_congr rfl
  intro i _hi
  push_cast
  ring

/-- The power-weight variable mean therefore has no hidden averaging object:
it is the literal sum of the fixed arithmetic means at the two endpoint
weights occurring at each index. -/
theorem powerPairwiseVariableMean_eq_sum_fullFrozenPairwiseMean
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) :
    powerPairwiseVariableMean hQ r chi v w b N A T =
      ∑ i ∈ Finset.range T,
        fullFrozenPairwiseMean hQ r chi v w
          (powerWeight b (N - (A + i)) : ℂ)
          (powerWeight b (A + i) : ℂ) N := by
  unfold powerPairwiseVariableMean
  exact variableFourChannelMean_eq_sum_fullFrozenPairwiseMean
    hQ r chi v w
      (fun i => powerWeight b (N - (A + i)))
      (fun i => powerWeight b (A + i)) N T

/-- Complete-diagonal normal form for the variable power-weight mean.  The
only remaining mathematical question is the real-part lower bound of this
explicit finite sum; the off-divisor boundary loss has already been absorbed
in V1.8.333. -/
theorem powerPairwiseVariableMean_eq_sum_completeDiagonal
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q)
    (chi : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (b : ℝ) (N A T : ℕ) :
    powerPairwiseVariableMean hQ r chi v w b N A T =
      ∑ i ∈ Finset.range T,
        (principalDiagonal hK v w (N : ZMod K) +
          ((r.val : ℂ) / (r.val.totient : ℂ) ^ 2) *
            (((powerWeight b (N - (A + i)) : ℂ) *
                (powerWeight b (A + i) : ℂ)) * chi.val (-1) *
                unitCharacterSum r.val
                  (ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K)) -
              ((powerWeight b (N - (A + i)) : ℂ) +
                (powerWeight b (A + i) : ℂ)) *
                ((ArithmeticFunction.moebius r.val : ℤ) : ℂ) *
                chi.val
                  (ZMod.castHom (hK r) (ZMod r.val) (N : ZMod K))) *
            coupledDiagonal hK r v w (N : ZMod K)) := by
  rw [powerPairwiseVariableMean_eq_sum_fullFrozenPairwiseMean]
  apply Finset.sum_congr rfl
  intro i _hi
  exact fullFrozenPairwiseMean_eq_completeDiagonal
    hQ hK r chi v w
      (powerWeight b (N - (A + i)) : ℂ)
      (powerWeight b (A + i) : ℂ) N

end GoldbachCircleMethodVariableMeanDiagonalNormalFormV18334
