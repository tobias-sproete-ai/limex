import GoldbachCircleMethodLocalizedRadicalCoefficientReadbackV18300

/-!
# Goldbach V1.8.301: canonical-weight localized radical dichotomy

If the active conductor lies in the plateau range of the canonical logarithmic
weight, then every divisor-localized denominator also has weight one.  The
constant-weight radical dichotomy of V1.8.300 therefore applies to the actual
canonical localized principal companion.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalWeightLocalizedRadicalDichotomyV18301

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodActualMultiplierScaleV18135
open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290
open GoldbachCircleMethodEvenConductorCoprimeBranchObstructionV18298
open GoldbachCircleMethodLocalizedSquarefreeDivisorBindingV18299
open GoldbachCircleMethodLocalizedRadicalCoefficientReadbackV18300

/-- On the active-conductor plateau, the canonical weight is one at every
localized squarefree divisor. -/
theorem localizedSquarefreeDivisorSum_canonical_eq_one
    {Q : ℕ} (active : PositiveLevel Q) (N : ℕ)
    (R : ℝ) (hR : 1 < R) (hactiveR : (active.val : ℝ) ≤ R) :
    localizedSquarefreeDivisorSum active N
        (logWeight R canonicalLogBump) =
      localizedSquarefreeDivisorSum active N (fun _ => 1) := by
  unfold localizedSquarefreeDivisorSum
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hcarrier : Squarefree l.val ∧ l.val ∣ active.val
  · rw [if_pos hcarrier, if_pos hcarrier]
    have hlpos : 0 < l.val := (Finset.mem_Icc.mp l.property).1
    have hlactive : l.val ≤ active.val :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne active.val)) hcarrier.2
    have hlR : (l.val : ℝ) ≤ R :=
      (Nat.cast_le.mpr hlactive).trans hactiveR
    rw [log_weight_eq_one R hR canonicalLogBump
      (fun _ hx0 hx1 => canonicalLogBump_plateau hx0 hx1)
      l.val hlpos hlR]
  · simp [hcarrier]

/-- Exact closed form for the actual canonical localized principal companion
on the active-conductor plateau. -/
theorem divisorLocalizedFiniteCompanion_oneLevel_canonical_eq_ite
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q) (N : ℕ)
    (R : ℝ) (hR : 1 < R) (hactiveR : (active.val : ℝ) ≤ R) :
    divisorLocalizedFiniteCompanion active (oneLevel hQ) N
        (logWeight R canonicalLogBump) =
      if Nat.Coprime N active.val then
        (active.val : ℂ) / (active.val.totient : ℂ)
      else 0 := by
  rw [divisorLocalizedFiniteCompanion_oneLevel_eq_squarefreeDivisorSum hQ]
  rw [localizedSquarefreeDivisorSum_canonical_eq_one active N R hR hactiveR]
  exact localizedSquarefreeDivisorSum_one_eq_ite active N

/-- In the even-target/even-conductor case, the actual canonical localized
principal companion vanishes exactly throughout the plateau range. -/
theorem divisorLocalizedFiniteCompanion_oneLevel_canonical_eq_zero_of_even
    {Q : ℕ} (hQ : 1 ≤ Q) (active : PositiveLevel Q) (N : ℕ)
    (hN : Even N) (hactiveEven : Even active.val)
    (R : ℝ) (hR : 1 < R) (hactiveR : (active.val : ℝ) ≤ R) :
    divisorLocalizedFiniteCompanion active (oneLevel hQ) N
      (logWeight R canonicalLogBump) = 0 := by
  rw [divisorLocalizedFiniteCompanion_oneLevel_canonical_eq_ite
    hQ active N R hR hactiveR]
  exact if_neg (even_even_not_coprime hN hactiveEven)

end GoldbachCircleMethodCanonicalWeightLocalizedRadicalDichotomyV18301

