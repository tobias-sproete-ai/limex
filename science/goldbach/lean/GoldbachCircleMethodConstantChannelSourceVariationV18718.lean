import GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
import GoldbachCircleMethodFiniteRamanujanEnergyV18131
import GoldbachCircleMethodActualCompanionIntervalTransferV18205
import GoldbachCircleMethodOddDoubleHybridBoundV18681

/-!
# V1.8.718: quantitative source-coordinate variation for the actual constant channel

This append-only module puts the first unconditional quantitative ceiling on
the exact V1.8.717 Abel decomposition of the actual V1.8.710 constant channel.
For a nonzero additive frequency it proves:

* every shifted phase prefix is bounded by the literal odd denominator `q`;
* the terminal two-radius sinc weight is bounded by `3P/(qM)`;
* the source-coordinate total variation is bounded by `6P/q`;
* hence the literal constant kernel sum is bounded by
  `q * (3P/(qM) + 6P/q)`.

Here `P = oddProjectWidth M`, and both exact radii `q` and `2q` are retained.
The variation estimate deliberately uses only the already kernelized pointwise
small-phase envelope and the triangle inequality.  It is therefore rigorous
but not claimed to be sharp enough for the final project normalization.

No centered-channel estimate, source-mean estimate, denominator aggregation,
moment estimate, exceptional-set estimate, or Goldbach conclusion is proved.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodConstantChannelSourceVariationV18718

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodFiniteRamanujanEnergyV18131
open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOddDoubleHybridBoundV18681
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualOneFiberDFTRawPhaseSumV18705
open GoldbachCircleMethodActualJointModeCounterModulationV18709
open GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717

/-- The full shifted relative phase has zero mass on one complete period when
the selected additive frequency is nonzero. -/
theorem sum_selectedPairRelativeAddCharPhase_period_eq_zero
    (qNat n : Nat) [NeZero qNat] (xi : ZMod qNat) (hxi : xi ≠ 0) :
    (∑ a : ZMod qNat,
      ZMod.stdAddChar ((((n : ZMod qNat) - a) * xi))) = 0 := by
  calc
    (∑ a : ZMod qNat,
      ZMod.stdAddChar ((((n : ZMod qNat) - a) * xi))) =
        ∑ a : ZMod qNat, ZMod.stdAddChar (a * xi) := by
          exact Fintype.sum_equiv
            (Equiv.subLeft (n : ZMod qNat))
            (fun a : ZMod qNat =>
              ZMod.stdAddChar ((((n : ZMod qNat) - a) * xi)))
            (fun a : ZMod qNat => ZMod.stdAddChar (a * xi))
            (fun _ => rfl)
    _ = ∑ a : ZMod qNat, ZMod.stdAddChar (xi * a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [mul_comm]
    _ = 0 := by
          simpa [hxi] using standard_character_orthogonality qNat xi

/-- Every incomplete prefix of the actual shifted source phase is bounded by
one literal denominator.  Complete periods cancel exactly; only the final
residue interval remains. -/
theorem selectedPairRelativeAddCharPhasePrefix_norm_le_denominator
    (qNat n : Nat) [NeZero qNat] (xi : ZMod qNat) (hxi : xi ≠ 0)
    (k : Nat) :
    ‖selectedPairRelativeAddCharPhasePrefix qNat n xi k‖ ≤ (qNat : Real) := by
  let g : ZMod qNat → Complex := fun a =>
    ZMod.stdAddChar ((((n : ZMod qNat) - a) * xi))
  have hfull : (∑ a : ZMod qNat, g a) = 0 := by
    simpa only [g] using
      sum_selectedPairRelativeAddCharPhase_period_eq_zero qNat n xi hxi
  have hdecomp := residue_interval_decomposition g 0 k
  have hphase : ∀ a : Nat,
      selectedPairRelativeAddCharPhase qNat n a xi = g (a : ZMod qNat) := by
    intro a
    unfold selectedPairRelativeAddCharPhase g
    push_cast
    rfl
  have hrem :
      selectedPairRelativeAddCharPhasePrefix qNat n xi k =
        ∑ a ∈ Finset.range (k % qNat), g (a : ZMod qNat) := by
    unfold selectedPairRelativeAddCharPhasePrefix
    simp_rw [hphase]
    simpa [hfull] using hdecomp
  rw [hrem]
  calc
    ‖∑ a ∈ Finset.range (k % qNat), g (a : ZMod qNat)‖ ≤
        ∑ a ∈ Finset.range (k % qNat), ‖g (a : ZMod qNat)‖ :=
      norm_sum_le _ _
    _ = ((k % qNat : Nat) : Real) := by
      simp [g]
    _ ≤ (qNat : Real) := by
      exact_mod_cast Nat.le_of_lt
        (Nat.mod_lt k (Nat.pos_of_ne_zero (NeZero.ne qNat)))

/-- The literal two-radius source-coordinate sinc weight is pointwise bounded
by the small-phase `q`/`2q` envelope away from its totalized zero at the moving
diagonal. -/
theorem selectedPairSourceCoordinateSincWeight_norm_le_small
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) :
    ‖selectedPairSourceCoordinateSincWeight M q n a‖ ≤
      3 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real)) := by
  by_cases han : a = n
  · subst a
    rw [show selectedPairSourceCoordinateSincWeight M q n n = 0 by
      simp [selectedPairSourceCoordinateSincWeight,
        selectedPairRelativeTwoRadiusSinc_self_eq_zero]]
    simp
    positivity
  · have hk : selectedPairRelativeStepTwoCoordinate n a ≠ 0 := by
      unfold selectedPairRelativeStepTwoCoordinate
      omega
    have hRadius :=
      norm_explicitSincRadiusFactor_odd_double_sum_le_small
        (P := oddProjectWidth M) hM
        (selectedPairRelativeStepTwoCoordinate n a) hk
        q.val (pairedDoubleDenominator q) (pairedDoubleDenominator_val q)
    unfold selectedPairSourceCoordinateSincWeight
      selectedPairRelativeTwoRadiusSinc
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans hRadius

/-- The terminal literal sinc weight appearing in the exact Abel identity has
the same `3P/(qM)` ceiling. -/
theorem selectedPairSourceCoordinateSincWeight_terminal_norm_le
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    ‖selectedPairSourceCoordinateSincWeight M q n M‖ ≤
      3 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real)) :=
  selectedPairSourceCoordinateSincWeight_norm_le_small M hM q n M

/-- A pointwise first-difference ceiling in the source coordinate.  It keeps
the correct denominator and project-width scaling and remains valid across
the moving diagonal because that literal sinc value is exactly zero. -/
theorem selectedPairSourceCoordinateSincVariation_norm_le
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) :
    ‖selectedPairSourceCoordinateSincVariation M q n a‖ ≤
      6 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real)) := by
  unfold selectedPairSourceCoordinateSincVariation
  calc
    ‖selectedPairSourceCoordinateSincWeight M q n (a + 1) -
        selectedPairSourceCoordinateSincWeight M q n a‖ ≤
      ‖selectedPairSourceCoordinateSincWeight M q n (a + 1)‖ +
        ‖selectedPairSourceCoordinateSincWeight M q n a‖ := norm_sub_le _ _
    _ ≤
      3 * (oddProjectWidth M : Real) /
          ((q.val.val : Real) * (M : Real)) +
        3 * (oddProjectWidth M : Real) /
          ((q.val.val : Real) * (M : Real)) :=
      add_le_add
        (selectedPairSourceCoordinateSincWeight_norm_le_small M hM q n (a + 1))
        (selectedPairSourceCoordinateSincWeight_norm_le_small M hM q n a)
    _ = 6 * (oddProjectWidth M : Real) /
          ((q.val.val : Real) * (M : Real)) := by ring

/-- The exact total variation along all `M` first differences is bounded by
`6P/q`.  No derivative estimate or continuous extension of sinc is used. -/
theorem sum_selectedPairSourceCoordinateSincVariation_norm_le
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    (∑ a ∈ Finset.range M,
      ‖selectedPairSourceCoordinateSincVariation M q n a‖) ≤
      6 * (oddProjectWidth M : Real) / (q.val.val : Real) := by
  calc
    (∑ a ∈ Finset.range M,
      ‖selectedPairSourceCoordinateSincVariation M q n a‖) ≤
        ∑ _a ∈ Finset.range M,
          (6 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real))) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact selectedPairSourceCoordinateSincVariation_norm_le M hM q n a
    _ = 6 * (oddProjectWidth M : Real) / (q.val.val : Real) := by
      have hMReal : (M : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
      have hqReal : (q.val.val : Real) ≠ 0 := by
        exact_mod_cast (NeZero.ne q.val.val)
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- Abel's inequality specialized to the literal source phase and two-radius
sinc weight.  The frequency hypothesis is exactly what makes the conductor
prefix bound available. -/
theorem sinc_phase_sum_norm_le_denominator_mul_endpoint_add_variation
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (hxi : xi ≠ 0) :
    ‖∑ a ∈ Finset.range M.succ,
        selectedPairSourceCoordinateSincWeight M q n a *
          selectedPairRelativeAddCharPhase q.val.val n a xi‖ ≤
      (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          6 * (oddProjectWidth M : Real) / (q.val.val : Real)) := by
  have habel := Finset.sum_range_by_parts
    (selectedPairSourceCoordinateSincWeight M q n)
    (fun a => selectedPairRelativeAddCharPhase q.val.val n a xi)
    M.succ
  simp only [Nat.succ_sub_one, smul_eq_mul] at habel
  rw [habel]
  calc
    _ ≤
        ‖selectedPairSourceCoordinateSincWeight M q n M *
            selectedPairRelativeAddCharPhasePrefix q.val.val n xi M.succ‖ +
          ‖∑ a ∈ Finset.range M,
            selectedPairSourceCoordinateSincVariation M q n a *
              selectedPairRelativeAddCharPhasePrefix q.val.val n xi (a + 1)‖ :=
      norm_sub_le _ _
    _ ≤
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real))) * (q.val.val : Real) +
          ∑ a ∈ Finset.range M,
            ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
              (q.val.val : Real) := by
      apply add_le_add
      · rw [Complex.norm_mul]
        exact mul_le_mul
          (selectedPairSourceCoordinateSincWeight_terminal_norm_le M hM q n)
          (selectedPairRelativeAddCharPhasePrefix_norm_le_denominator
            q.val.val n xi hxi M.succ)
          (norm_nonneg _) (by positivity)
      · calc
          _ ≤ ∑ a ∈ Finset.range M,
              ‖selectedPairSourceCoordinateSincVariation M q n a *
                selectedPairRelativeAddCharPhasePrefix q.val.val n xi (a + 1)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ a ∈ Finset.range M,
              ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
                (q.val.val : Real) := by
            apply Finset.sum_le_sum
            intro a _ha
            rw [Complex.norm_mul]
            exact mul_le_mul_of_nonneg_left
              (selectedPairRelativeAddCharPhasePrefix_norm_le_denominator
                q.val.val n xi hxi (a + 1))
              (norm_nonneg _)
    _ =
        (q.val.val : Real) *
          (3 * (oddProjectWidth M : Real) /
              ((q.val.val : Real) * (M : Real)) +
            ∑ a ∈ Finset.range M,
              ‖selectedPairSourceCoordinateSincVariation M q n a‖) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤
        (q.val.val : Real) *
          (3 * (oddProjectWidth M : Real) /
              ((q.val.val : Real) * (M : Real)) +
            6 * (oddProjectWidth M : Real) / (q.val.val : Real)) := by
      gcongr
      exact sum_selectedPairSourceCoordinateSincVariation_norm_le M hM q n

/-- Quantitative constant-kernel ceiling for the exact V1.8.716/V1.8.717
kernel.  The target gate is used only for the exact unchanged-kernel rewrite. -/
theorem sum_selectedPairSourceSeparatedKernel_norm_le
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (hxi : xi ≠ 0)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    ‖∑ a ∈ Finset.range M.succ,
        selectedPairSourceSeparatedKernel M q n xi a‖ ≤
      (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          6 * (oddProjectWidth M : Real) / (q.val.val : Real)) := by
  rw [sum_selectedPairSourceSeparatedKernel_eq_sinc_phase_sum
    M q n xi hTarget]
  exact sinc_phase_sum_norm_le_denominator_mul_endpoint_add_variation
    M hM q n xi hxi

/-- Exact simplification of the conductor-prefix/variation envelope.  The
factor `q` from the character prefix cancels the `1/q` in the crude total
variation bound.  Thus this route gives no denominator saving by itself. -/
theorem denominator_mul_endpoint_add_variation_eq_projectScale
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M)) :
    (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          6 * (oddProjectWidth M : Real) / (q.val.val : Real)) =
      3 * (oddProjectWidth M : Real) / (M : Real) +
        6 * (oddProjectWidth M : Real) := by
  have hMReal : (M : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hqReal : (q.val.val : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne q.val.val)
  field_simp

/-- Equivalent project-scale ceiling for the unchanged constant kernel sum.
It makes explicit that the elementary variation route leaves an `O(P)` term,
not a conductor-decaying term. -/
theorem sum_selectedPairSourceSeparatedKernel_norm_le_projectScale
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (hxi : xi ≠ 0)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    ‖∑ a ∈ Finset.range M.succ,
        selectedPairSourceSeparatedKernel M q n xi a‖ ≤
      3 * (oddProjectWidth M : Real) / (M : Real) +
        6 * (oddProjectWidth M : Real) := by
  calc
    _ ≤ (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          6 * (oddProjectWidth M : Real) / (q.val.val : Real)) :=
      sum_selectedPairSourceSeparatedKernel_norm_le
        M hM q n xi hxi hTarget
    _ = _ := denominator_mul_endpoint_add_variation_eq_projectScale M hM q

/-- The actual constant-channel transform inherits the exact source mean and
the quantitative kernel ceiling.  This is not an absorption theorem: the
right side may remain too large in the full denominator aggregation. -/
theorem actualLambdaPairConstantKernelTransform_norm_le
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (hxi : xi ≠ 0)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    ‖actualLambdaPairConstantKernelTransform M
        (selectedPairSourceSeparatedKernel M q n xi)‖ ≤
      ‖(actualLambdaPairSourceMean M : Complex)‖ *
        ((q.val.val : Real) *
          (3 * (oddProjectWidth M : Real) /
              ((q.val.val : Real) * (M : Real)) +
            6 * (oddProjectWidth M : Real) / (q.val.val : Real))) := by
  rw [actualLambdaPairConstantKernelTransform_eq_mean_mul_sum,
    Complex.norm_mul]
  exact mul_le_mul_of_nonneg_left
    (sum_selectedPairSourceSeparatedKernel_norm_le
      M hM q n xi hxi hTarget)
    (norm_nonneg _)

/-- Project-scale form of the actual constant-channel ceiling.  The surviving
`6P` contribution is explicit and blocks any claim of automatic absorption. -/
theorem actualLambdaPairConstantKernelTransform_norm_le_projectScale
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) (hxi : xi ≠ 0)
    (hTarget : 2 * n ∈ evenTargetBlock M) :
    ‖actualLambdaPairConstantKernelTransform M
        (selectedPairSourceSeparatedKernel M q n xi)‖ ≤
      ‖(actualLambdaPairSourceMean M : Complex)‖ *
        (3 * (oddProjectWidth M : Real) / (M : Real) +
          6 * (oddProjectWidth M : Real)) := by
  rw [actualLambdaPairConstantKernelTransform_eq_mean_mul_sum,
    Complex.norm_mul]
  exact mul_le_mul_of_nonneg_left
    (sum_selectedPairSourceSeparatedKernel_norm_le_projectScale
      M hM q n xi hxi hTarget)
    (norm_nonneg _)

end GoldbachCircleMethodConstantChannelSourceVariationV18718
