import GoldbachCircleMethodTotientRatioLocalPrimeMajorantV18562

/-!
# Goldbach V1.8.563: positive convolution for the totient fourth moment

The finite prime-product majorant from V1.8.562 is expanded exactly into a
positive convolution over subsets of the prime support.  This is the entry
point for incidence transposition and an Euler-kernel mean bound.  No prefix
mean estimate is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientFourthPositiveConvolutionV18563

open GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556
open GoldbachCircleMethodTotientRatioLocalPrimeMajorantV18562

/-- Positive subset weight produced by the local `30/p` majorant. -/
noncomputable def totientFourthSubsetWeight (t : Finset ℕ) : ℝ :=
  ∏ p ∈ t, (30 : ℝ) / (p : ℝ)

theorem totientFourthSubsetWeight_nonneg (t : Finset ℕ) :
    0 ≤ totientFourthSubsetWeight t := by
  unfold totientFourthSubsetWeight
  positivity

/-- Exact positive powerset expansion of the finite prime majorant. -/
theorem primeMajorantProduct_eq_positive_powerset_sum (n : ℕ) :
    (∏ p ∈ n.primeFactors, (1 + (30 : ℝ) / (p : ℝ))) =
      ∑ t ∈ n.primeFactors.powerset, totientFourthSubsetWeight t := by
  unfold totientFourthSubsetWeight
  exact Finset.prod_one_add n.primeFactors

/-- Pointwise reduction of the fourth-power totient ratio to a finite,
nonnegative divisor-expandable convolution. -/
theorem levelTotientRatio_pow_four_le_positive_powerset_sum
    (n : ℕ) (hn : n ≠ 0) :
    levelTotientRatio n ^ 4 ≤
      ∑ t ∈ n.primeFactors.powerset, totientFourthSubsetWeight t := by
  calc
    levelTotientRatio n ^ 4 ≤
        ∏ p ∈ n.primeFactors, (1 + (30 : ℝ) / (p : ℝ)) :=
      levelTotientRatio_pow_four_le_primeMajorantProduct n hn
    _ = ∑ t ∈ n.primeFactors.powerset, totientFourthSubsetWeight t :=
      primeMajorantProduct_eq_positive_powerset_sum n

end GoldbachCircleMethodTotientFourthPositiveConvolutionV18563
