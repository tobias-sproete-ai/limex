import GoldbachCircleMethodExceptionalTransferV1823
import GoldbachCircleMethodFixedScaleTransferV1824

/-!
# Fixed-scale Class-II composition, V1.8.25

This module composes the V1.8.23 finite one-sided Markov core with the
V1.8.24 fixed-ambient Fourier family.  It proves, for one fixed
`ArcParameters pM` and a finite even target block `[X, 2X]` protected by
`2X ≤ pM.N`, that every non-Goldbach target enters the same negative minor-arc
threshold set.  A locally supplied negative-part second-moment estimate then
bounds the actual exceptional-set cardinality.

The major-arc margin and the second-moment estimate remain ordinary local
hypotheses.  No analytic source theorem, global postulate, or Goldbach result is
installed by this module.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodFixedScaleClassIICompositionV1825

open GoldbachPurePrimeAdequacyV15
open GoldbachVonMangoldtDecompositionV16
open GoldbachPrimePowerDefectBoundV161
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodFixedScaleTransferV1824

/-- Exact target restatement for the actual fixed-scale major/minor family. -/
theorem goldbachAt_iff_fixedScaleMinor_gt_defect_sub_major
    (pM : ArcParameters) (N : Nat) (hNM : N ≤ pM.N) :
    GoldbachAt N ↔
      fixedScaleMinorIntegralReal pM N >
        primePowerDefect N - fixedScaleMajorIntegralReal pM N := by
  rw [← purePrimeSum_pos_iff_strictGoldbach]
  have hPartition := fixedScaleMajor_add_minor_eq_vonMangoldtPairSum pM N hNM
  have hDecomposition :=
    vonMangoldtPairSum_eq_purePrimeSum_add_primePowerDefect N
  constructor <;> intro h <;> linarith

/-!
The next theorem is the fixed-scale counterpart of V1.8.23's native-scale
pointwise bridge.  Its two analytic inputs are visible in the signature:
the `4/35` major margin and the defect-reserve inequality.
-/
theorem not_goldbachAt_implies_fixedScaleMinor_le_negative_threshold
    (pM : ArcParameters) (N : Nat) (E_L : Real)
    (hN : 1 ≤ N)
    (hNM : N ≤ pM.N)
    (hNotGoldbach : ¬ GoldbachAt N)
    (hMajor :
      lowerBandThreshold * (N : Real) - E_L ≤
        fixedScaleMajorIntegralReal pM N)
    (hReserve :
      E_L + 4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2 ≤
        classIIThreshold * (N : Real)) :
    fixedScaleMinorIntegralReal pM N ≤
      -(classIIThreshold * (N : Real)) := by
  have hMinorNotGt :
      ¬ fixedScaleMinorIntegralReal pM N >
          primePowerDefect N - fixedScaleMajorIntegralReal pM N := by
    intro hMinor
    exact hNotGoldbach
      ((goldbachAt_iff_fixedScaleMinor_gt_defect_sub_major pM N hNM).2 hMinor)
  have hMinorLe :
      fixedScaleMinorIntegralReal pM N ≤
        primePowerDefect N - fixedScaleMajorIntegralReal pM N :=
    le_of_not_gt hMinorNotGt
  have hDefect := primePowerDefect_le_four_sqrt_mul_log_sq hN
  have hThresholdIdentity :
      lowerBandThreshold = 2 * classIIThreshold := by
    norm_num [lowerBandThreshold, classIIThreshold]
  rw [hThresholdIdentity] at hMajor
  linarith

/-- Even natural targets in the closed dyadic block `[X, 2X]`. -/
noncomputable def fixedScaleEvenTargetBlock (X : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc X (2 * X)).filter Even

/-- The actual Goldbach exceptions in the fixed finite even target block. -/
noncomputable def fixedScaleGoldbachExceptions (X : Nat) : Finset Nat := by
  classical
  exact (fixedScaleEvenTargetBlock X).filter (fun N => ¬ GoldbachAt N)

theorem mem_fixedScaleEvenTargetBlock_iff {X N : Nat} :
    N ∈ fixedScaleEvenTargetBlock X ↔ X ≤ N ∧ N ≤ 2 * X ∧ Even N := by
  classical
  simp [fixedScaleEvenTargetBlock, and_assoc]

theorem mem_fixedScaleGoldbachExceptions_iff {X N : Nat} :
    N ∈ fixedScaleGoldbachExceptions X ↔
      N ∈ fixedScaleEvenTargetBlock X ∧ ¬ GoldbachAt N := by
  classical
  simp [fixedScaleGoldbachExceptions]

/-!
Dyadic transfer from the target-dependent `-(2/35)N` estimate to the single
fixed threshold `-(2/35)X` used in the V1.8.23 Markov core.
-/
theorem not_goldbachAt_on_fixedScaleBlock_implies_uniform_minor_threshold
    (pM : ArcParameters) (X N : Nat) (E_L : Real)
    (hX : 1 ≤ X)
    (hAmbient : 2 * X ≤ pM.N)
    (hTarget : N ∈ fixedScaleEvenTargetBlock X)
    (hNotGoldbach : ¬ GoldbachAt N)
    (hMajor :
      lowerBandThreshold * (N : Real) - E_L ≤
        fixedScaleMajorIntegralReal pM N)
    (hReserve :
      E_L + 4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2 ≤
        classIIThreshold * (N : Real)) :
    fixedScaleMinorIntegralReal pM N ≤
      -(classIIThreshold * (X : Real)) := by
  have hTargetData := mem_fixedScaleEvenTargetBlock_iff.mp hTarget
  have hN : 1 ≤ N := hX.trans hTargetData.1
  have hNM : N ≤ pM.N := hTargetData.2.1.trans hAmbient
  have hPointwise :=
    not_goldbachAt_implies_fixedScaleMinor_le_negative_threshold
      pM N E_L hN hNM hNotGoldbach hMajor hReserve
  apply negative_threshold_transfer_on_dyadicBlock_X_twoX
    (X : Real) (N : Real) (fixedScaleMinorIntegralReal pM N)
  · constructor
    · exact_mod_cast hTargetData.1
    · exact_mod_cast hTargetData.2.1
  · exact hPointwise

/-!
Every actual Goldbach exception is contained in the one-sided bad-index set
of V1.8.23 for the concrete fixed-scale minor family.  The hypotheses remain
pointwise analytic contracts over the fixed finite block.
-/
theorem fixedScaleGoldbachExceptions_subset_badIndices
    (pM : ArcParameters) (X : Nat) (E_L : Nat → Real)
    (hX : 1 ≤ X)
    (hAmbient : 2 * X ≤ pM.N)
    (hMajor : ∀ N ∈ fixedScaleEvenTargetBlock X,
      lowerBandThreshold * (N : Real) - E_L N ≤
        fixedScaleMajorIntegralReal pM N)
    (hReserve : ∀ N ∈ fixedScaleEvenTargetBlock X,
      E_L N + 4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2 ≤
        classIIThreshold * (N : Real)) :
    fixedScaleGoldbachExceptions X ⊆
      badIndices (fixedScaleEvenTargetBlock X)
        (fixedScaleMinorIntegralReal pM) (X : Real) := by
  classical
  intro N hException
  have hExceptionData := mem_fixedScaleGoldbachExceptions_iff.mp hException
  exact Finset.mem_filter.mpr ⟨hExceptionData.1,
    not_goldbachAt_on_fixedScaleBlock_implies_uniform_minor_threshold
      pM X N (E_L N) hX hAmbient hExceptionData.1 hExceptionData.2
      (hMajor N hExceptionData.1) (hReserve N hExceptionData.1)⟩

/-!
Finite Class-II composition theorem for the actual fixed-scale operator.

`hMoment` is deliberately passed as a local analytic input.  The theorem
proves only the reduction from that input to an exceptional-set cardinality
bound; it does not manufacture or source-bind a moment estimate.
-/
theorem fixedScaleGoldbachExceptions_card_le_of_negativePart_moment
    (pM : ArcParameters) (X : Nat) (E_L : Nat → Real) (M : Real)
    (hX : 1 ≤ X)
    (hAmbient : 2 * X ≤ pM.N)
    (hMajor : ∀ N ∈ fixedScaleEvenTargetBlock X,
      lowerBandThreshold * (N : Real) - E_L N ≤
        fixedScaleMajorIntegralReal pM N)
    (hReserve : ∀ N ∈ fixedScaleEvenTargetBlock X,
      E_L N + 4 * Real.sqrt (N : Real) * (Real.log (N : Real)) ^ 2 ≤
        classIIThreshold * (N : Real))
    (hMoment :
      negativePartSquaredMoment (fixedScaleEvenTargetBlock X)
          (fixedScaleMinorIntegralReal pM) ≤ M) :
    ((fixedScaleGoldbachExceptions X).card : Real) ≤
      M / (classIIThreshold * (X : Real)) ^ 2 := by
  classical
  have hSubset := fixedScaleGoldbachExceptions_subset_badIndices
    pM X E_L hX hAmbient hMajor hReserve
  have hCardNat :
      (fixedScaleGoldbachExceptions X).card ≤
        (badIndices (fixedScaleEvenTargetBlock X)
          (fixedScaleMinorIntegralReal pM) (X : Real)).card :=
    Finset.card_le_card hSubset
  have hCardReal :
      ((fixedScaleGoldbachExceptions X).card : Real) ≤
        ((badIndices (fixedScaleEvenTargetBlock X)
          (fixedScaleMinorIntegralReal pM) (X : Real)).card : Real) := by
    exact_mod_cast hCardNat
  refine hCardReal.trans ?_
  exact bad_card_le_of_negativePart_moment
    (fixedScaleEvenTargetBlock X) (fixedScaleMinorIntegralReal pM)
    (X : Real) M (by exact_mod_cast hX) hMoment

end GoldbachCircleMethodFixedScaleClassIICompositionV1825
