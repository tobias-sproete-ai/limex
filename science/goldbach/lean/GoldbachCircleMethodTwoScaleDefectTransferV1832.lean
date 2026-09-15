import GoldbachCircleMethodTwoScaleIntegralPartitionV1831

/-!
# Exact two-scale defect balance and conditional finite transfer, V1.8.32
No mask or integrand is changed. Major reserve, defect reserve and moment
bound in the last theorem are explicit local inputs, not proved estimates.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodTwoScaleDefectTransferV1832

open scoped Classical

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodTwoScaleElementaryKernelV1828

theorem purePrimeSum_eq_twoScaleMajor_add_minor_sub_defect
    (M P R0 N : Nat) (hNM : N ≤ M) :
    purePrimeSum N = twoScaleMajorIntegralReal M P R0 N +
      twoScaleMinorIntegralReal M P R0 N - primePowerDefect N := by
  have hPartition := twoScaleMajor_add_minor_eq_vonMangoldtPairSum M P R0 N hNM
  have hDecomposition := vonMangoldtPairSum_eq_purePrimeSum_add_primePowerDefect N
  linarith

theorem goldbachAt_iff_twoScaleMinor_gt_defect_sub_major
    (M P R0 N : Nat) (hNM : N ≤ M) :
    GoldbachAt N ↔ twoScaleMinorIntegralReal M P R0 N >
      primePowerDefect N - twoScaleMajorIntegralReal M P R0 N := by
  rw [← purePrimeSum_pos_iff_strictGoldbach,
    purePrimeSum_eq_twoScaleMajor_add_minor_sub_defect M P R0 N hNM]
  constructor <;> intro h <;> linarith

/-- Local reserve implication only; neither reserve is supplied by this theorem. -/
theorem not_goldbachAt_implies_twoScaleMinor_le_neg_M_div_28
    (M P R0 N : Nat) (hNM : N ≤ M) (hNot : ¬ GoldbachAt N)
    (hMajor : (M : Real) / 14 ≤ twoScaleMajorIntegralReal M P R0 N)
    (hDefect : primePowerDefect N ≤ (M : Real) / 28) :
    twoScaleMinorIntegralReal M P R0 N ≤ -((M : Real) / 28) := by
  have hNotGt : ¬ twoScaleMinorIntegralReal M P R0 N >
      primePowerDefect N - twoScaleMajorIntegralReal M P R0 N := by
    intro h
    exact hNot ((goldbachAt_iff_twoScaleMinor_gt_defect_sub_major M P R0 N hNM).2 h)
  have hLe := le_of_not_gt hNotGt
  linarith

/-- Actual non-Goldbach indices in a declared finite set enter the fixed threshold. -/
theorem twoScaleExceptions_subset_badIndices
    (M P R0 : Nat) (s : Finset Nat)
    (hRange : ∀ N ∈ s, N ≤ M)
    (hMajor : ∀ N ∈ s, (M : Real) / 14 ≤ twoScaleMajorIntegralReal M P R0 N)
    (hDefect : ∀ N ∈ s, primePowerDefect N ≤ (M : Real) / 28) :
    s.filter (fun N => ¬ GoldbachAt N) ⊆
      badIndices s (twoScaleMinorIntegralReal M P R0) (twoScaleMarkovX (M : Real)) := by
  classical
  intro N hN
  rcases Finset.mem_filter.mp hN with ⟨hNs, hNot⟩
  apply Finset.mem_filter.mpr
  refine ⟨hNs, ?_⟩
  rw [classIIThreshold_mul_twoScaleMarkovX]
  exact not_goldbachAt_implies_twoScaleMinor_le_neg_M_div_28 M P R0 N
    (hRange N hNs) hNot (hMajor N hNs) (hDefect N hNs)

/-- Conditional finite Class-II transfer for the exact mask/operator family.
To study even targets in a dyadic block, instantiate s with that explicit block.
No all-N result or asymptotic choice of B is asserted.
-/
theorem twoScaleExceptions_card_le_3136_of_moment
    (M P R0 : Nat) (s : Finset Nat) (B : Real)
    (hM : 0 < M)
    (hRange : ∀ N ∈ s, N ≤ M)
    (hMajor : ∀ N ∈ s, (M : Real) / 14 ≤ twoScaleMajorIntegralReal M P R0 N)
    (hDefect : ∀ N ∈ s, primePowerDefect N ≤ (M : Real) / 28)
    (hMoment : negativePartSquaredMoment s (twoScaleMinorIntegralReal M P R0) ≤
      4 * (M : Real) ^ 2 * B) :
    ((s.filter (fun N => ¬ GoldbachAt N)).card : Real) ≤ 3136 * B := by
  classical
  have hCard := Finset.card_le_card
    (twoScaleExceptions_subset_badIndices M P R0 s hRange hMajor hDefect)
  have hCardReal :
      ((s.filter (fun N => ¬ GoldbachAt N)).card : Real) ≤
      ((badIndices s (twoScaleMinorIntegralReal M P R0)
        (twoScaleMarkovX (M : Real))).card : Real) := by exact_mod_cast hCard
  exact hCardReal.trans (bad_card_le_3136_of_moment s
    (twoScaleMinorIntegralReal M P R0) (M : Real) B (Nat.cast_pos.mpr hM) hMoment)

end GoldbachCircleMethodTwoScaleDefectTransferV1832
