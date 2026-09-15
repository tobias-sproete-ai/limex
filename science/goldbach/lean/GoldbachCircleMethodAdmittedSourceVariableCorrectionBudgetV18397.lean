import GoldbachCircleMethodSourceBoundVariableCoupledCorrectionV18396
import GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333

/-!
# Goldbach V1.8.397: admitted source-variable correction budget

The source-bound variable correction from V1.8.396 is specialized to the
canonical logarithmic conductor cutoff and bump.  The already kernelized
V1.8.333 scale admission then absorbs its complete pairwise-period `Q^4`
cost into the explicit quadratic block budget `B^2/56`.

This is a numerical budget theorem.  It does not identify `B^2/56` with a
source-side positive reserve and does not prove Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAdmittedSourceVariableCorrectionBudgetV18397

open GoldbachCircleMethodAdmittedCanonicalAbelAbsorptionV18333
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodResidualScaleAdmissionV18196
open GoldbachCircleMethodSourceBoundVariableCoupledCorrectionV18396
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- At every admitted scale, the exact source-variable correction across the
two target branches is strictly below `B^2/56`. -/
theorem admitted_source_variable_correction_norm_lt_quadratic_budget
    (B A Kgrow S : ℕ) (rho b : ℝ)
    (e : StructurallyAdmissibleActiveSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (K : ℕ) [NeZero K]
    (hKperiod : ∀ q : PositiveLevel ⌊((B : ℝ) ^ rho) ^ 2⌋₊, q.val ∣ K)
    (hrho : 0 < rho) (hrhoUpper : rho ≤ (1 : ℝ) / 10000)
    (hScale : blockThreshold rho ≤ B)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hA : Even A)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hKgrow : 1 ≤ Kgrow)
    (hGrowingLast : A + 2 * (Kgrow - 1) ≤ blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst : blockPairTurningTarget B ≤ A + 2 * Kgrow)
    (hFinal : A + 2 * Kgrow + 2 * (S - 1) ≤ 2 * B) :
    ‖sourceNormalizedActualVariableCorrectionTargetSum
        hKperiod e
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        (logWeight ((B : ℝ) ^ rho) canonicalLogBump)
        B A (Kgrow + S) b‖ < (B : ℝ) ^ 2 / 56 := by
  let Q : ℕ := ⌊((B : ℝ) ^ rho) ^ 2⌋₊
  let wt : ℕ → ℂ := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  have hraw := source_variable_correction_norm_le_quartic
    hKperiod e wt wt 1 (by norm_num)
      (canonical_logWeight_norm_le_one ((B : ℝ) ^ rho))
      (canonical_logWeight_norm_le_one ((B : ℝ) ^ rho))
      B A Kgrow S b hb hA hB hBA hNonempty hKgrow hGrowingLast hS
        hShrinkingFirst hFinal
  have h22 :
      ‖sourceNormalizedActualVariableCorrectionTargetSum
          hKperiod e wt wt B A (Kgrow + S) b‖ ≤
        22 * (B : ℝ) * (Q : ℝ) ^ 4 := by
    calc
      _ ≤ 2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 4 * (1 : ℝ) ^ 2 +
          8 * (B : ℝ) * (Q : ℝ) ^ 4 * (1 : ℝ) ^ 2 := hraw
      _ = (B : ℝ) * (Q : ℝ) ^ 4 * (14 + 8 * b) := by ring
      _ ≤ (B : ℝ) * (Q : ℝ) ^ 4 * 22 := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        positivity
      _ = 22 * (B : ℝ) * (Q : ℝ) ^ 4 := by ring
  have h24 := admitted_pairwise_quartic_cost_lt
    rho hrho hrhoUpper B hScale
  have h22Q :
      22 * (Q : ℝ) ^ 4 < (B : ℝ) / 56 := by
    calc
      22 * (Q : ℝ) ^ 4 ≤ 24 * (Q : ℝ) ^ 4 := by
        nlinarith [sq_nonneg ((Q : ℝ) ^ 2)]
      _ < (B : ℝ) / 56 := by simpa only [Q] using h24
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hscaled := mul_lt_mul_of_pos_left h22Q hBpos
  calc
    _ ≤ 22 * (B : ℝ) * (Q : ℝ) ^ 4 := by simpa only [wt] using h22
    _ = (B : ℝ) * (22 * (Q : ℝ) ^ 4) := by ring
    _ < (B : ℝ) * ((B : ℝ) / 56) := hscaled
    _ = (B : ℝ) ^ 2 / 56 := by ring

end GoldbachCircleMethodAdmittedSourceVariableCorrectionBudgetV18397
