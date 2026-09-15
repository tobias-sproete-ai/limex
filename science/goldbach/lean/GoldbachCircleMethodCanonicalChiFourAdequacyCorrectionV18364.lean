import GoldbachCircleMethodSourceMatchedExceptionalZeroGateV18363
import GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

/-!
# Goldbach V1.8.364: canonical chi-four adequacy correction

V1.8.362 gives a genuine negative arithmetic-mean witness for constant
conductor weights.  The canonical model used by V1.8.332/V1.8.333 does not
have those weights: at cutoff `R = 2`, its conductor-four weight is exactly
zero.  This module records that semantic boundary and proves that the same
primitive chi-four slot has a nonnegative canonical frozen mean at target
four, independently of the two scalar endpoint weights.

This is a correction of scope, not a Goldbach theorem.  It does not establish
uniform positivity at general conductors or discharge the exceptional-zero
attestation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalChiFourAdequacyCorrectionV18364

open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualLogWeightSquareBindingV18219
open GoldbachCircleMethodActualUnitPairSignedResidualV18214
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrimitiveChiFourFullMeanNegativeWitnessV18360
open GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339
open GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335

theorem canonicalLogBump_two : canonicalLogBump 2 = 0 := by
  rw [canonicalLogBump_eq_right (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.smoothTransition.zero_of_nonpos]

theorem log_four_div_log_two :
    Real.log (4 : ℝ) / Real.log (2 : ℝ) = 2 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  calc
    Real.log (4 : ℝ) / Real.log (2 : ℝ) =
        (2 * Real.log (2 : ℝ)) / Real.log (2 : ℝ) := by
      congr 1
      convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
    _ = 2 := by field_simp

/-- The canonical conductor-four cutoff is zero at `R=2`. -/
theorem canonical_logWeight_two_four :
    logWeight 2 canonicalLogBump 4 = 0 := by
  unfold logWeight
  change (canonicalLogBump
    (Real.log (4 : ℝ) / Real.log (2 : ℝ)) : ℂ) = 0
  rw [log_four_div_log_two, canonicalLogBump_two]
  norm_num

/-- Therefore the constant conductor weights in V1.8.362 are not the literal
canonical weights of V1.8.332/V1.8.333. -/
theorem constant_weight_not_canonical_at_four :
    (1 : ℂ) ≠ logWeight 2 canonicalLogBump 4 := by
  rw [canonical_logWeight_two_four]
  norm_num

/-- At cutoff four, the canonical coupled conductor-four diagonal vanishes
because its only admissible product index is exactly four. -/
theorem coupledDiagonal_four_canonical_zero :
    coupledDiagonal divisorsOfTwelve fourLevel
      (logWeight 2 canonicalLogBump)
      (logWeight 2 canonicalLogBump) ((4 : ℕ) : ZMod 12) = 0 := by
  calc
    coupledDiagonal divisorsOfTwelve fourLevel
        (logWeight 2 canonicalLogBump)
        (logWeight 2 canonicalLogBump) ((4 : ℕ) : ZMod 12) =
      coupledDiagonal divisorsOfTwelve fourLevel
        (fun q => (squaredLogWeightReal 2 canonicalLogBump q : ℂ))
        (fun _ => 1) ((4 : ℕ) : ZMod 12) :=
      coupledDiagonal_logWeight_square_eq divisorsOfTwelve fourLevel 4
        2 canonicalLogBump
    _ = 0 := by
      unfold coupledDiagonal
      apply Finset.sum_eq_zero
      intro l _hl
      by_cases hcut : fourLevel.val * l.val ≤ 4 ∧
          Nat.Coprime fourLevel.val l.val
      · rw [if_pos hcut]
        have hlval : l.val = 1 := by
          have hlpos : 1 ≤ l.val := (Finset.mem_Icc.mp l.property).1
          simp only [fourLevel] at hcut
          omega
        have hindex : fourLevel.val * l.val = 4 := by
          simp [fourLevel, hlval]
        rw [hindex]
        simp [squaredLogWeightReal, log_four_div_log_two,
          canonicalLogBump_two]
      · rw [if_neg hcut]

/-- The chi-four negative constant-weight witness does not transfer to the
canonical log-weighted model: at the matching cutoff and target, the frozen
mean retains the canonical principal floor for arbitrary endpoint weights. -/
theorem fullFrozenPairwiseMean_four_canonical_ge_principal_floor
    (t₁ t₂ : ℂ) :
    2 - Real.exp (Real.pi ^ 2 / 24) ≤
      (GoldbachCircleMethodFullFrozenPairwiseIntervalV18323.fullFrozenPairwiseMean
        (by norm_num : 1 ≤ 4) fourLevel complexChiFourPrimitive
        (logWeight 2 canonicalLogBump)
        (logWeight 2 canonicalLogBump) t₁ t₂ 4).re := by
  rw [fullFrozenPairwiseMean_eq_signedResidual_add_unitPairBracket
    (by norm_num : 1 ≤ 4) divisorsOfTwelve fourLevel
    complexChiFourPrimitive complexChiFour_inv
    (logWeight 2 canonicalLogBump)
    (logWeight 2 canonicalLogBump) t₁ t₂ 4]
  rw [coupledDiagonal_four_canonical_zero]
  simp only [mul_zero, zero_mul, add_zero]
  rw [signedDiagonalResidual, coupledDiagonal_four_canonical_zero]
  simp only [mul_zero, sub_zero]
  have hK : ∀ q : PositiveLevel ⌊((2 : ℝ) ^ 2)⌋₊, q.val ∣ 12 := by
    intro q
    obtain ⟨hq1, hq4⟩ := Finset.mem_Icc.mp q.property
    norm_num at hq4
    interval_cases q.val <;> norm_num
  have hfloor := actual_principalDiagonal_canonicalLogBump_floor
    (K := 12) (N := 4) 2 (by norm_num)
      hK (by norm_num : Even 4)
  convert hfloor using 1
  all_goals norm_num

end GoldbachCircleMethodCanonicalChiFourAdequacyCorrectionV18364
