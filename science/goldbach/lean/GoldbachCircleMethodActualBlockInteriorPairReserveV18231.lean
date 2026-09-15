import GoldbachCircleMethodDyadicScaleMismatchNegativeWitnessV18230

/-!
# Goldbach V1.8.231: actual block interior pair reserve

After V1.8.230 rejected the naive same-scale target adapter, this module gives
an exact sufficient condition for a target to lie far enough inside the true
self-convolution support of `(B/2, B]`.  Under that condition, the literal pair
count is at least a freely specified natural reserve `t`.

The resulting principal-model floor retains the quartic boundary cost and
does not claim that a later scale choice satisfies the numerical budget.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodActualBlockInteriorPairReserveV18231

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodPositivePrincipalDiagonalV18221
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodSupportedModelIntervalDiagonalV18228
open GoldbachCircleMethodFiniteIntervalRemainderReserveV18229

/-- A target is `t` lattice points inside both edges of the exact convolution
support.  The formulation avoids truncated subtraction. -/
def HasInteriorPairReserve (B N t : ℕ) : Prop :=
  2 * (B / 2 + 1) + t ≤ N + 1 ∧ N + t ≤ 2 * B + 1

/-- Interior positioning supplies all geometry required by the exact interval
model and at least `t` admissible first coordinates. -/
theorem blockPair_geometry_of_interior_reserve
    (B N t : ℕ) (hB : 1 ≤ B) (htPos : 1 ≤ t)
    (h : HasInteriorPairReserve B N t) :
    B ≤ N ∧
      blockPairLower B N ≤ blockPairUpper B N ∧
      t ≤ blockPairUpper B N - blockPairLower B N + 1 := by
  rcases h with ⟨hleft, hright⟩
  constructor
  · omega
  · constructor
    · simp only [blockPairLower, blockPairUpper, max_le_iff, le_min_iff]
      omega
    · simp only [blockPairLower, blockPairUpper]
      by_cases hmax : B / 2 + 1 ≤ N - B
      · rw [max_eq_right hmax]
        by_cases hmin : B ≤ N - (B / 2 + 1)
        · rw [min_eq_left hmin]
          omega
        · rw [min_eq_right (le_of_not_ge hmin)]
          omega
      · rw [max_eq_left (le_of_not_ge hmax)]
        by_cases hmin : B ≤ N - (B / 2 + 1)
        · rw [min_eq_left hmin]
          omega
        · rw [min_eq_right (le_of_not_ge hmin)]
          omega

/-- The exact pair count of the actual source block inherits the requested
interior reserve. -/
theorem blockPair_count_ge_interior_reserve
    (B N t : ℕ) (hB : 1 ≤ B) (htPos : 1 ≤ t)
    (h : HasInteriorPairReserve B N t) :
    t ≤ blockPairUpper B N - blockPairLower B N + 1 :=
  (blockPair_geometry_of_interior_reserve B N t hB htPos h).2.2

/-- Signed real-part floor in terms of the visible interior reserve `t`, not a
free proxy for the actual pair count. -/
theorem canonicalPrincipalModelAt_real_floor_of_interior_reserve
    {K : ℕ} [NeZero K]
    (B N t : ℕ) (rho : ℝ) (hR : 1 < (B : ℝ) ^ rho)
    (hB : 1 ≤ B) (htPos : 1 ≤ t)
    (hInterior : HasInteriorPairReserve B N t)
    (hEven : Even N)
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K) :
    (t : ℝ) * (2 - Real.exp (Real.pi ^ 2 / 24)) -
        2 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 ≤
      (canonicalPrincipalModelAt B rho (N : ℤ)).re := by
  rcases blockPair_geometry_of_interior_reserve B N t hB htPos hInterior with
    ⟨hBN, hInterval, ht⟩
  have hfloor := canonicalPrincipalModelAt_real_floor
    B N rho hR hB hBN hInterval hEven hK
  have htReal : (t : ℝ) ≤
      ((blockPairUpper B N - blockPairLower B N + 1 : ℕ) : ℝ) := by
    exact_mod_cast ht
  have hkappa : 0 ≤ 2 - Real.exp (Real.pi ^ 2 / 24) :=
    le_of_lt two_sub_exp_pi_sq_div_twentyFour_pos
  have hmul := mul_le_mul_of_nonneg_right htReal hkappa
  linarith

/-- Strict positivity of the actual supported principal model follows under
an explicit interior budget. -/
theorem canonicalPrincipalModelAt_real_pos_of_interior_budget
    {K : ℕ} [NeZero K]
    (B N t : ℕ) (rho : ℝ) (hR : 1 < (B : ℝ) ^ rho)
    (hB : 1 ≤ B) (htPos : 1 ≤ t)
    (hInterior : HasInteriorPairReserve B N t)
    (hEven : Even N)
    (hK : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hbudget :
      2 * (⌊((B : ℝ) ^ rho) ^ 2⌋₊ : ℝ) ^ 4 <
        (t : ℝ) * (2 - Real.exp (Real.pi ^ 2 / 24))) :
    0 < (canonicalPrincipalModelAt B rho (N : ℤ)).re :=
  lt_of_lt_of_le (by linarith)
    (canonicalPrincipalModelAt_real_floor_of_interior_reserve
      B N t rho hR hB htPos hInterior hEven hK)

end GoldbachCircleMethodActualBlockInteriorPairReserveV18231
