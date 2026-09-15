import GoldbachCircleMethodOddDoublePairAmplitudeV18679

/-!
# V1.8.681: local hybrid envelope for an odd/double denominator pair

This append-only module retains the denominator in the elementary small-phase
estimate for the literal sinc radius.  For an odd denominator `q` and its
double `q₂`, the two exact radii contribute at most `2P/(qM)` and `P/(qM)`.
Combining that ceiling with the V1.8.679 harmonic ceiling gives a pointwise
minimum bound for the actual pair of `explicitDenominatorSincTerm`s.

The result is local to one `q`/`2q` pair and one nonzero even signed frequency.
It proves no sign cancellation, summability, target-block moment,
exceptional-set estimate, or Goldbach conclusion.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped Classical

namespace GoldbachCircleMethodOddDoubleHybridBoundV18681

open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOddDoublePairAmplitudeV18679
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodOriginalMaskModelBindingV1859

/-- The literal radius factor retains the exact denominator in the elementary
`|sin x| <= |x|` estimate.  No positivity hypothesis on `P` is needed. -/
theorem norm_explicitSincRadiusFactor_le_q
    {M P R : Nat} (hM : 0 < M) (q : Denominator R)
    (k : Int) (hk : k ≠ 0) :
    ‖explicitSincRadiusFactor M P R k q‖ ≤
      2 * (P : Real) / ((q.val : Real) * (M : Real)) := by
  have hqNat : 1 ≤ q.val := (Finset.mem_Icc.mp q.property).1
  have hq : 0 < (q.val : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqNat)
  have hMReal : 0 < (M : Real) := by exact_mod_cast hM
  have hkReal : (k : Real) ≠ 0 := by exact_mod_cast hk
  have hP : 0 ≤ (P : Real) := Nat.cast_nonneg P
  simp only [explicitSincRadiusFactor, Complex.norm_real, Real.norm_eq_abs,
    abs_div]
  calc
    |Real.sin
        (2 * Real.pi * (k : Real) *
          ((P : Real) / ((q.val : Real) * (M : Real))))| /
        |Real.pi * (k : Real)| ≤
      |2 * Real.pi * (k : Real) *
        ((P : Real) / ((q.val : Real) * (M : Real)))| /
        |Real.pi * (k : Real)| := by
          exact div_le_div_of_nonneg_right
            Real.abs_sin_le_abs (abs_nonneg _)
    _ = 2 * (P : Real) / ((q.val : Real) * (M : Real)) := by
      simp only [abs_mul, abs_div,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
        abs_of_pos Real.pi_pos, abs_of_pos hq, abs_of_pos hMReal,
        abs_of_nonneg hP]
      field_simp

/-- The exact `q` and `2*q` radius pair has the small-phase ceiling
`3P/(qM)`.  Both original radius factors remain present. -/
theorem norm_explicitSincRadiusFactor_odd_double_sum_le_small
    {M P R : Nat} (hM : 0 < M) (k : Int) (hk : k ≠ 0)
    (q q₂ : Denominator R) (hq₂ : q₂.val = 2 * q.val) :
    ‖explicitSincRadiusFactor M P R k q +
        explicitSincRadiusFactor M P R k q₂‖ ≤
      3 * (P : Real) / ((q.val : Real) * (M : Real)) := by
  have hqNat : 1 ≤ q.val := (Finset.mem_Icc.mp q.property).1
  have hq : 0 < (q.val : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqNat)
  have hMReal : 0 < (M : Real) := by exact_mod_cast hM
  calc
    ‖explicitSincRadiusFactor M P R k q +
        explicitSincRadiusFactor M P R k q₂‖ ≤
      ‖explicitSincRadiusFactor M P R k q‖ +
        ‖explicitSincRadiusFactor M P R k q₂‖ := norm_add_le _ _
    _ ≤ 2 * (P : Real) / ((q.val : Real) * (M : Real)) +
        2 * (P : Real) / ((q₂.val : Real) * (M : Real)) :=
      add_le_add
        (norm_explicitSincRadiusFactor_le_q hM q k hk)
        (norm_explicitSincRadiusFactor_le_q hM q₂ k hk)
    _ = 3 * (P : Real) / ((q.val : Real) * (M : Real)) := by
      rw [hq₂]
      push_cast
      field_simp
      ring

/-- Hybrid pointwise envelope for the exact two-radius sum.  The first branch
is effective at small phase, while the second is the V1.8.679 harmonic bound.
No assertion is made about which branch is smaller at a given frequency. -/
theorem norm_explicitSincRadiusFactor_odd_double_sum_le_hybrid
    {M P R : Nat} (hM : 0 < M) (k : Int) (hk : k ≠ 0)
    (q q₂ : Denominator R) (hq₂ : q₂.val = 2 * q.val) :
    ‖explicitSincRadiusFactor M P R k q +
        explicitSincRadiusFactor M P R k q₂‖ ≤
      min
        (3 * (P : Real) / ((q.val : Real) * (M : Real)))
        (9 / (5 * Real.pi * |(k : Real)|) : Real) := by
  apply le_min
  · exact norm_explicitSincRadiusFactor_odd_double_sum_le_small hM k hk q q₂ hq₂
  · have hHarmonic :=
      norm_explicitSincRadiusFactor_odd_double_sum_le M P R k hk q q₂ hq₂
    have hkReal : (k : Real) ≠ 0 := by exact_mod_cast hk
    have hAbs : |(k : Real)| ≠ 0 := abs_ne_zero.mpr hkReal
    have hNormalize :
        (9 / 5 : Real) / (Real.pi * |(k : Real)|) =
          9 / (5 * Real.pi * |(k : Real)|) := by
      field_simp
    rwa [hNormalize] at hHarmonic

/-- The literal `explicitDenominatorSincTerm` pair inherits the hybrid radius
envelope after V1.8.678 factors its common Ramanujan coefficient. -/
theorem norm_explicitDenominatorSincTerm_odd_double_pair_le_hybrid
    {M P R : Nat} (hM : 0 < M) (k : Int) (hk : k ≠ 0)
    (q q₂ : Denominator R) (hqOdd : Odd q.val)
    (hq₂ : q₂.val = 2 * q.val) (hkEven : Even k) :
    ‖explicitDenominatorSincTerm M P R k q +
        explicitDenominatorSincTerm M P R k q₂‖ ≤
      ‖integerFourierRamanujan q.val (-k) (NeZero.ne q.val)‖ *
        min
          (3 * (P : Real) / ((q.val : Real) * (M : Real)))
          (9 / (5 * Real.pi * |(k : Real)|) : Real) := by
  rw [explicitDenominatorSincTerm_odd_double_pair M P R k q q₂
    hqOdd hq₂ hkEven, Complex.norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_explicitSincRadiusFactor_odd_double_sum_le_hybrid
      hM k hk q q₂ hq₂)
    (norm_nonneg _)

end GoldbachCircleMethodOddDoubleHybridBoundV18681
