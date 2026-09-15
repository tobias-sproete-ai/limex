import GoldbachCircleMethodLocalizedPrincipalArithmeticNormalFormV18295

/-!
# Goldbach V1.8.296: localized principal real nonnegative reserve

The canonical logarithmic bump is nonnegative.  After the V1.8.295
Moebius-square normal form, every localized principal term is real and
nonnegative, while the denominator-one term is exactly one.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedPrincipalRealNonnegativeReserveV18296

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290
open GoldbachCircleMethodLocalizedPrincipalArithmeticNormalFormV18295

/-- Each canonical arithmetic-normal-form summand has nonnegative real part. -/
theorem localizedPrincipalArithmeticTerm_canonical_re_nonneg
    (R : ℝ) (l : ℕ) :
    0 ≤ (localizedPrincipalArithmeticTerm l
      (logWeight R canonicalLogBump)).re := by
  by_cases hsq : Squarefree l
  · have hmu : (((ArithmeticFunction.moebius l : ℤ) : ℂ) ^ 2) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    unfold localizedPrincipalArithmeticTerm logWeight
    rw [hmu]
    have hphi : 0 < l.totient := Nat.totient_pos.mpr hsq.ne_zero.bot_lt
    simp only [Complex.mul_re, Complex.div_re]
    simp
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (canonicalLogBump_nonneg _)
  · unfold localizedPrincipalArithmeticTerm
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    norm_num

/-- The denominator-one canonical term is exactly one. -/
theorem localizedPrincipalArithmeticTerm_canonical_one (R : ℝ) :
    localizedPrincipalArithmeticTerm 1 (logWeight R canonicalLogBump) = 1 := by
  unfold localizedPrincipalArithmeticTerm logWeight
  rw [ArithmeticFunction.moebius_apply_one]
  norm_num [canonicalLogBump_zero]

/-- Under the explicit target/conductor coprimality hypothesis, the real part
of the localized principal companion has the uniform floor one. -/
theorem one_le_divisorLocalizedFiniteCompanion_oneLevel_canonical_re
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q)
    (N : ℕ) (hN : Nat.Coprime N active.val) (R : ℝ) :
    1 ≤ (divisorLocalizedFiniteCompanion active (oneLevel hQ) N
      (logWeight R canonicalLogBump)).re := by
  rw [divisorLocalizedFiniteCompanion_oneLevel_eq_arithmeticSum hQ active N hN]
  change 1 ≤ Complex.reCLM
    (∑ l : PositiveLevel Q,
      if l.val ∣ active.val then
        localizedPrincipalArithmeticTerm l.val (logWeight R canonicalLogBump)
      else 0)
  rw [map_sum]
  have hsum := Finset.single_le_sum
    (f := fun l : PositiveLevel Q =>
      (if l.val ∣ active.val then
        localizedPrincipalArithmeticTerm l.val (logWeight R canonicalLogBump)
      else 0).re)
    (fun l _ => by
      by_cases hdiv : l.val ∣ active.val
      · simp only [hdiv, if_true]
        exact localizedPrincipalArithmeticTerm_canonical_re_nonneg R l.val
      · simp [hdiv])
    (Finset.mem_univ (oneLevel hQ))
  simpa [oneLevel, localizedPrincipalArithmeticTerm_canonical_one] using hsum

end GoldbachCircleMethodLocalizedPrincipalRealNonnegativeReserveV18296
