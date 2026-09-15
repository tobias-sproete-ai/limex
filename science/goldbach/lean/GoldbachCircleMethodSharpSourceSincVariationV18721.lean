import GoldbachCircleMethodConstantChannelSourceVariationV18718
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# V1.8.721: sharp source-coordinate variation for the literal two-radius sinc kernel

This append-only module leaves the V1.8.710/V1.8.717 source-separated kernel
and its radii `q` and `2q` unchanged.  It resolves the totalized zero notch
explicitly, proves the local inverse-distance first-difference estimate, sums
the two sides of the notch by finite harmonic numbers, and feeds the resulting
`12 P H_M / (q M)` variation ceiling through the existing exact Abel identity.

The final all-target theorem is valid for every source index in
`Finset.range M.succ`: outside `evenTargetBlock M` the unchanged kernel is
definitionally zero; inside it the sharp Abel estimate applies.

No centered-channel estimate, source-mean estimate, denominator aggregation,
minor-arc absorption, exceptional-set estimate, or Goldbach conclusion is
proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodActualDemodulatedOneFiberRelativeConvolutionV18710
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodConstantChannelSourceVariationV18718

namespace GoldbachCircleMethodSharpSourceSincVariationV18721

theorem abs_sin_mul_div_sub_sin_mul_div_le
    (c x y : Real) (hx : x ≠ 0) (hy : y ≠ 0) :
    |Real.sin (c * y) / (Real.pi * y) -
        Real.sin (c * x) / (Real.pi * x)| ≤
      2 * |c| * |y - x| / (Real.pi * |y|) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hid :
      Real.sin (c * y) / (Real.pi * y) -
          Real.sin (c * x) / (Real.pi * x) =
        (Real.sin (c * y) - Real.sin (c * x)) / (Real.pi * y) +
          Real.sin (c * x) * (x - y) / (Real.pi * x * y) := by
    field_simp
    ring
  rw [hid]
  calc
    _ ≤
        |(Real.sin (c * y) - Real.sin (c * x)) / (Real.pi * y)| +
          |Real.sin (c * x) * (x - y) / (Real.pi * x * y)| := abs_add_le _ _
    _ ≤
        |c * y - c * x| / |Real.pi * y| +
          |c * x| * |x - y| / |Real.pi * x * y| := by
      apply add_le_add
      · rw [abs_div]
        exact div_le_div_of_nonneg_right
          (Real.abs_sin_sub_sin_le (c * y) (c * x)) (abs_nonneg _)
      · rw [abs_div, abs_mul]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right Real.abs_sin_le_abs (abs_nonneg _))
          (abs_nonneg _)
    _ = 2 * |c| * |y - x| / (Real.pi * |y|) := by
      have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
      have hyabs : |y| ≠ 0 := abs_ne_zero.mpr hy
      rw [show c * y - c * x = c * (y - x) by ring, abs_mul,
        abs_sub_comm]
      simp only [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
      ring

theorem explicitSincRadiusFactor_step_norm_le
    {M P R : Nat} (hM : 0 < M) (q : Denominator R)
    (x y : Int) (hx : x ≠ 0) (hy : y ≠ 0)
    (hstep : |(y : Real) - (x : Real)| = 2) :
    ‖explicitSincRadiusFactor M P R y q -
        explicitSincRadiusFactor M P R x q‖ ≤
      8 * (P : Real) /
        ((q.val : Real) * (M : Real) * |(y : Real)|) := by
  have hqNat : 1 ≤ q.val := (Finset.mem_Icc.mp q.property).1
  have hqPos : 0 < (q.val : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqNat)
  have hMPos : 0 < (M : Real) := by exact_mod_cast hM
  have hqReal : (q.val : Real) ≠ 0 := by
    exact ne_of_gt hqPos
  have hMReal : (M : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hxReal : (x : Real) ≠ 0 := by exact_mod_cast hx
  have hyReal : (y : Real) ≠ 0 := by exact_mod_cast hy
  have hcore := abs_sin_mul_div_sub_sin_mul_div_le
    (2 * Real.pi * ((P : Real) / ((q.val : Real) * (M : Real))))
    (x : Real) (y : Real) hxReal hyReal
  unfold explicitSincRadiusFactor
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [show
      2 * Real.pi * (y : Real) *
          ((P : Real) / ((q.val : Real) * (M : Real))) =
        (2 * Real.pi * ((P : Real) / ((q.val : Real) * (M : Real)))) *
          (y : Real) by ring]
  rw [show
      2 * Real.pi * (x : Real) *
          ((P : Real) / ((q.val : Real) * (M : Real))) =
        (2 * Real.pi * ((P : Real) / ((q.val : Real) * (M : Real)))) *
          (x : Real) by ring]
  refine hcore.trans_eq ?_
  rw [hstep]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hP : 0 ≤ (P : Real) := Nat.cast_nonneg P
  simp only [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
    abs_of_pos Real.pi_pos, abs_of_pos hqPos, abs_of_pos hMPos,
    abs_of_nonneg hP]
  field_simp
  ring

theorem selectedPairRelativeStepTwoCoordinate_abs_of_lt
    {n a : Nat} (ha : a < n) :
    |(selectedPairRelativeStepTwoCoordinate n a : Real)| =
      2 * ((n - a : Nat) : Real) := by
  have har : (a : Real) ≤ (n : Real) := by exact_mod_cast (Nat.le_of_lt ha)
  unfold selectedPairRelativeStepTwoCoordinate
  push_cast
  rw [abs_of_nonneg]
  · rw [Nat.cast_sub (Nat.le_of_lt ha)]
  · positivity

theorem selectedPairRelativeStepTwoCoordinate_succ_abs_of_le
    {n a : Nat} (ha : n ≤ a) :
    |(selectedPairRelativeStepTwoCoordinate n (a + 1) : Real)| =
      2 * ((a + 1 - n : Nat) : Real) := by
  have hna : n ≤ a + 1 := ha.trans (Nat.le_succ a)
  have hnr : (n : Real) ≤ (a : Real) + 1 := by exact_mod_cast hna
  unfold selectedPairRelativeStepTwoCoordinate
  push_cast
  rw [abs_of_nonpos (by linarith)]
  rw [Nat.cast_sub hna]
  push_cast
  ring

/-- Positive distance attached to the edge `a -> a+1`, measured from the
moving notch `n`.  The two edges incident to the notch both have distance
one. -/
def selectedPairSourceEdgeDistance (n a : Nat) : Nat :=
  if a < n then n - a else a + 1 - n

theorem selectedPairSourceEdgeDistance_pos (n a : Nat) :
    0 < selectedPairSourceEdgeDistance n a := by
  unfold selectedPairSourceEdgeDistance
  split_ifs with h
  · omega
  · omega

theorem selectedPairRelativeStepTwoCoordinate_step_abs
    (n a : Nat) :
    |(selectedPairRelativeStepTwoCoordinate n (a + 1) : Real) -
        (selectedPairRelativeStepTwoCoordinate n a : Real)| = 2 := by
  unfold selectedPairRelativeStepTwoCoordinate
  push_cast
  rw [show
      2 * ((n : Real) - ((a : Real) + 1)) -
          2 * ((n : Real) - (a : Real)) = -2 by ring]
  norm_num

theorem selectedPairSourceCoordinateSincWeight_eq_radius_sum
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) :
    selectedPairSourceCoordinateSincWeight M q n a =
      explicitSincRadiusFactor M
        (oddProjectWidth M) (oddProjectRadius M)
        (selectedPairRelativeStepTwoCoordinate n a) q.val +
      explicitSincRadiusFactor M
        (oddProjectWidth M) (oddProjectRadius M)
        (selectedPairRelativeStepTwoCoordinate n a)
        (pairedDoubleDenominator q) := by
  have hreal : ∀ (d : Denominator (oddProjectRadius M)) (k : Int),
      (((explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
          k d).re : Real) : Complex) =
        explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M) k d := by
    intro d k
    rfl
  unfold selectedPairSourceCoordinateSincWeight
    selectedPairRelativeTwoRadiusSinc
  rw [Complex.add_re]
  push_cast
  rw [hreal, hreal]

theorem selectedPairSourceCoordinateSincVariation_norm_le_radius_steps
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) :
    ‖selectedPairSourceCoordinateSincVariation M q n a‖ ≤
      ‖explicitSincRadiusFactor M
          (oddProjectWidth M) (oddProjectRadius M)
          (selectedPairRelativeStepTwoCoordinate n (a + 1)) q.val -
        explicitSincRadiusFactor M
          (oddProjectWidth M) (oddProjectRadius M)
          (selectedPairRelativeStepTwoCoordinate n a) q.val‖ +
      ‖explicitSincRadiusFactor M
          (oddProjectWidth M) (oddProjectRadius M)
          (selectedPairRelativeStepTwoCoordinate n (a + 1))
          (pairedDoubleDenominator q) -
        explicitSincRadiusFactor M
          (oddProjectWidth M) (oddProjectRadius M)
          (selectedPairRelativeStepTwoCoordinate n a)
          (pairedDoubleDenominator q)‖ := by
  unfold selectedPairSourceCoordinateSincVariation
  rw [selectedPairSourceCoordinateSincWeight_eq_radius_sum,
    selectedPairSourceCoordinateSincWeight_eq_radius_sum]
  rw [show
      (explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
            (selectedPairRelativeStepTwoCoordinate n (a + 1)) q.val +
          explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
            (selectedPairRelativeStepTwoCoordinate n (a + 1))
              (pairedDoubleDenominator q)) -
        (explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
            (selectedPairRelativeStepTwoCoordinate n a) q.val +
          explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
            (selectedPairRelativeStepTwoCoordinate n a)
              (pairedDoubleDenominator q)) =
        (explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
            (selectedPairRelativeStepTwoCoordinate n (a + 1)) q.val -
          explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
            (selectedPairRelativeStepTwoCoordinate n a) q.val) +
        (explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
            (selectedPairRelativeStepTwoCoordinate n (a + 1))
              (pairedDoubleDenominator q) -
          explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
            (selectedPairRelativeStepTwoCoordinate n a)
              (pairedDoubleDenominator q)) by ring]
  exact norm_add_le _ _

/-- Sharp local edge estimate for the literal two-radius sinc weight.  The
distance is one on either edge incident to the totalized zero notch; all other
edges use the elementary quotient-difference estimate above. -/
theorem selectedPairSourceCoordinateSincVariation_norm_le_edgeDistance
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n a : Nat) :
    ‖selectedPairSourceCoordinateSincVariation M q n a‖ ≤
      6 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real) *
          (selectedPairSourceEdgeDistance n a : Real)) := by
  unfold selectedPairSourceEdgeDistance
  by_cases ha : a < n
  · rw [if_pos ha]
    by_cases hcross : a + 1 = n
    · have hdist : n - a = 1 := by omega
      have hzero : selectedPairSourceCoordinateSincWeight M q n (a + 1) = 0 := by
        rw [hcross]
        simp [selectedPairSourceCoordinateSincWeight,
          selectedPairRelativeTwoRadiusSinc_self_eq_zero]
      unfold selectedPairSourceCoordinateSincVariation
      rw [hzero, zero_sub, norm_neg, hdist]
      norm_num
      exact (selectedPairSourceCoordinateSincWeight_norm_le_small M hM q n a).trans
        (by
          have hden : 0 ≤
              (oddProjectWidth M : Real) /
                ((q.val.val : Real) * (M : Real)) := by positivity
          convert mul_le_mul_of_nonneg_right (by norm_num : (3 : Real) ≤ 6) hden using 1 <;> ring)
    · have hxa : selectedPairRelativeStepTwoCoordinate n (a + 1) ≠ 0 := by
        unfold selectedPairRelativeStepTwoCoordinate
        omega
      have hya : selectedPairRelativeStepTwoCoordinate n a ≠ 0 := by
        unfold selectedPairRelativeStepTwoCoordinate
        omega
      have hstep :
          |(selectedPairRelativeStepTwoCoordinate n a : Real) -
            (selectedPairRelativeStepTwoCoordinate n (a + 1) : Real)| = 2 := by
        rw [abs_sub_comm]
        exact selectedPairRelativeStepTwoCoordinate_step_abs n a
      have hq := explicitSincRadiusFactor_step_norm_le
        (P := oddProjectWidth M) (R := oddProjectRadius M) hM q.val
        (selectedPairRelativeStepTwoCoordinate n (a + 1))
        (selectedPairRelativeStepTwoCoordinate n a) hxa hya hstep
      have hq2 := explicitSincRadiusFactor_step_norm_le
        (P := oddProjectWidth M) (R := oddProjectRadius M) hM
        (pairedDoubleDenominator q)
        (selectedPairRelativeStepTwoCoordinate n (a + 1))
        (selectedPairRelativeStepTwoCoordinate n a) hxa hya hstep
      have hq' :
          ‖explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
              (selectedPairRelativeStepTwoCoordinate n (a + 1)) q.val -
            explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
              (selectedPairRelativeStepTwoCoordinate n a) q.val‖ ≤
            8 * (oddProjectWidth M : Real) /
              ((q.val.val : Real) * (M : Real) *
                |(selectedPairRelativeStepTwoCoordinate n a : Real)|) := by
        simpa only [norm_sub_rev] using hq
      have hq2' :
          ‖explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
              (selectedPairRelativeStepTwoCoordinate n (a + 1))
                (pairedDoubleDenominator q) -
            explicitSincRadiusFactor M (oddProjectWidth M) (oddProjectRadius M)
              (selectedPairRelativeStepTwoCoordinate n a)
                (pairedDoubleDenominator q)‖ ≤
            8 * (oddProjectWidth M : Real) /
              (((pairedDoubleDenominator q).val : Real) * (M : Real) *
                |(selectedPairRelativeStepTwoCoordinate n a : Real)|) := by
        simpa only [norm_sub_rev] using hq2
      calc
        _ ≤
            ‖explicitSincRadiusFactor M
                (oddProjectWidth M) (oddProjectRadius M)
                (selectedPairRelativeStepTwoCoordinate n (a + 1)) q.val -
              explicitSincRadiusFactor M
                (oddProjectWidth M) (oddProjectRadius M)
                (selectedPairRelativeStepTwoCoordinate n a) q.val‖ +
            ‖explicitSincRadiusFactor M
                (oddProjectWidth M) (oddProjectRadius M)
                (selectedPairRelativeStepTwoCoordinate n (a + 1))
                (pairedDoubleDenominator q) -
              explicitSincRadiusFactor M
                (oddProjectWidth M) (oddProjectRadius M)
                (selectedPairRelativeStepTwoCoordinate n a)
                (pairedDoubleDenominator q)‖ :=
          selectedPairSourceCoordinateSincVariation_norm_le_radius_steps M q n a
        _ ≤
            8 * (oddProjectWidth M : Real) /
                ((q.val.val : Real) * (M : Real) *
                  |(selectedPairRelativeStepTwoCoordinate n a : Real)|) +
              8 * (oddProjectWidth M : Real) /
                (((pairedDoubleDenominator q).val : Real) * (M : Real) *
                  |(selectedPairRelativeStepTwoCoordinate n a : Real)|) :=
          add_le_add hq' hq2'
        _ = 6 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real) * ((n - a : Nat) : Real)) := by
          rw [selectedPairRelativeStepTwoCoordinate_abs_of_lt ha,
            pairedDoubleDenominator_val]
          push_cast
          have hq0 : (q.val.val : Real) ≠ 0 := by
            exact_mod_cast (NeZero.ne q.val.val)
          have hM0 : (M : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
          have hdist0 : ((n - a : Nat) : Real) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt ha))
          field_simp
          ring

  · rw [if_neg ha]
    have hna : n ≤ a := Nat.le_of_not_gt ha
    by_cases hcross : a = n
    · subst a
      have hzero : selectedPairSourceCoordinateSincWeight M q n n = 0 := by
        simp [selectedPairSourceCoordinateSincWeight,
          selectedPairRelativeTwoRadiusSinc_self_eq_zero]
      unfold selectedPairSourceCoordinateSincVariation
      rw [hzero, sub_zero]
      norm_num
      exact (selectedPairSourceCoordinateSincWeight_norm_le_small M hM q n (n + 1)).trans
        (by
          have hden : 0 ≤
              (oddProjectWidth M : Real) /
                ((q.val.val : Real) * (M : Real)) := by positivity
          convert mul_le_mul_of_nonneg_right (by norm_num : (3 : Real) ≤ 6) hden using 1 <;> ring)
    · have hxa : selectedPairRelativeStepTwoCoordinate n a ≠ 0 := by
        unfold selectedPairRelativeStepTwoCoordinate
        omega
      have hya : selectedPairRelativeStepTwoCoordinate n (a + 1) ≠ 0 := by
        unfold selectedPairRelativeStepTwoCoordinate
        omega
      have hstep := selectedPairRelativeStepTwoCoordinate_step_abs n a
      have hq := explicitSincRadiusFactor_step_norm_le
        (P := oddProjectWidth M) (R := oddProjectRadius M) hM q.val
        (selectedPairRelativeStepTwoCoordinate n a)
        (selectedPairRelativeStepTwoCoordinate n (a + 1)) hxa hya hstep
      have hq2 := explicitSincRadiusFactor_step_norm_le
        (P := oddProjectWidth M) (R := oddProjectRadius M) hM
        (pairedDoubleDenominator q)
        (selectedPairRelativeStepTwoCoordinate n a)
        (selectedPairRelativeStepTwoCoordinate n (a + 1)) hxa hya hstep
      calc
        _ ≤
            ‖explicitSincRadiusFactor M
                (oddProjectWidth M) (oddProjectRadius M)
                (selectedPairRelativeStepTwoCoordinate n (a + 1)) q.val -
              explicitSincRadiusFactor M
                (oddProjectWidth M) (oddProjectRadius M)
                (selectedPairRelativeStepTwoCoordinate n a) q.val‖ +
            ‖explicitSincRadiusFactor M
                (oddProjectWidth M) (oddProjectRadius M)
                (selectedPairRelativeStepTwoCoordinate n (a + 1))
                (pairedDoubleDenominator q) -
              explicitSincRadiusFactor M
                (oddProjectWidth M) (oddProjectRadius M)
                (selectedPairRelativeStepTwoCoordinate n a)
                (pairedDoubleDenominator q)‖ :=
          selectedPairSourceCoordinateSincVariation_norm_le_radius_steps M q n a
        _ ≤
            8 * (oddProjectWidth M : Real) /
                ((q.val.val : Real) * (M : Real) *
                  |(selectedPairRelativeStepTwoCoordinate n (a + 1) : Real)|) +
              8 * (oddProjectWidth M : Real) /
                (((pairedDoubleDenominator q).val : Real) * (M : Real) *
                  |(selectedPairRelativeStepTwoCoordinate n (a + 1) : Real)|) :=
          add_le_add hq hq2
        _ = 6 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real) * ((a + 1 - n : Nat) : Real)) := by
          rw [selectedPairRelativeStepTwoCoordinate_succ_abs_of_le hna,
            pairedDoubleDenominator_val]
          push_cast
          have hq0 : (q.val.val : Real) ≠ 0 := by
            exact_mod_cast (NeZero.ne q.val.val)
          have hM0 : (M : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
          have hdist0 : ((a + 1 - n : Nat) : Real) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_succ_of_le hna)))
          field_simp
          ring

noncomputable def selectedPairSourceEdgeHarmonic (M n : Nat) : Real :=
  ∑ a ∈ Finset.range M,
    1 / (selectedPairSourceEdgeDistance n a : Real)

theorem sum_range_inv_selectedPairSourceEdgeDistance_left (n : Nat) :
    (∑ a ∈ Finset.range n,
        1 / (selectedPairSourceEdgeDistance n a : Real)) =
      (harmonic n : Real) := by
  rw [show (harmonic n : Real) =
      ∑ a ∈ Finset.range n, 1 / (((a + 1 : Nat) : Real)) by
    simp [harmonic, div_eq_mul_inv]]
  rw [← Finset.sum_range_reflect
    (fun a : Nat => 1 / (((a + 1 : Nat) : Real))) n]
  apply Finset.sum_congr rfl
  intro a ha
  have ha_lt : a < n := Finset.mem_range.mp ha
  simp only [selectedPairSourceEdgeDistance, if_pos ha_lt]
  congr 2
  omega

theorem sum_Ico_inv_selectedPairSourceEdgeDistance_right
    (M n : Nat) :
    (∑ a ∈ Finset.Ico n M,
        1 / (selectedPairSourceEdgeDistance n a : Real)) =
      (harmonic (M - n) : Real) := by
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show (harmonic (M - n) : Real) =
      ∑ a ∈ Finset.range (M - n), 1 / (((a + 1 : Nat) : Real)) by
    simp [harmonic, div_eq_mul_inv]]
  apply Finset.sum_congr rfl
  intro a ha
  have hna : n ≤ n + a := Nat.le_add_right n a
  simp only [selectedPairSourceEdgeDistance, if_neg (Nat.not_lt.mpr hna)]
  congr 2
  omega

theorem selectedPairSourceEdgeHarmonic_eq
    {M n : Nat} (hn : n ≤ M) :
    selectedPairSourceEdgeHarmonic M n =
      (harmonic n : Real) + (harmonic (M - n) : Real) := by
  have hleft :
      (Finset.range M).filter (fun a => a < n) = Finset.range n := by
    ext a
    simp
    omega
  have hright :
      (Finset.range M).filter (fun a => ¬ a < n) = Finset.Ico n M := by
    ext a
    simp
    omega
  unfold selectedPairSourceEdgeHarmonic
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.range M) (fun a => a < n)
      (fun a => 1 / (selectedPairSourceEdgeDistance n a : Real))]
  rw [hleft, hright,
    sum_range_inv_selectedPairSourceEdgeDistance_left,
    sum_Ico_inv_selectedPairSourceEdgeDistance_right]

theorem real_harmonic_eq_sum (n : Nat) :
    (harmonic n : Real) =
      ∑ a ∈ Finset.range n, 1 / (((a + 1 : Nat) : Real)) := by
  simp [harmonic, div_eq_mul_inv]

theorem real_harmonic_mono {m n : Nat} (hmn : m ≤ n) :
    (harmonic m : Real) ≤ (harmonic n : Real) := by
  rw [real_harmonic_eq_sum, real_harmonic_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (by
      intro i hi hnot
      positivity)

theorem selectedPairSourceEdgeHarmonic_le_harmonic
    {M n : Nat} (hn : n ≤ M) :
    selectedPairSourceEdgeHarmonic M n ≤
      2 * (harmonic M : Real) := by
  rw [selectedPairSourceEdgeHarmonic_eq hn]
  calc
    (harmonic n : Real) + (harmonic (M - n) : Real) ≤
        (harmonic M : Real) + (harmonic M : Real) :=
      add_le_add (real_harmonic_mono hn)
        (real_harmonic_mono (Nat.sub_le M n))
    _ = 2 * (harmonic M : Real) := by ring

theorem selectedPairSourceEdgeHarmonic_le_log
    {M n : Nat} (hn : n ≤ M) :
    selectedPairSourceEdgeHarmonic M n ≤
      2 * (1 + Real.log (M : Real)) := by
  exact (selectedPairSourceEdgeHarmonic_le_harmonic hn).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) (by norm_num))

/-- Sharp total-variation ceiling for the literal V1.8.710/V1.8.717 two-radius
sinc weight.  The factor `12` includes both radii and both sides of the moving
totalized zero notch. -/
theorem sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M) :
    (∑ a ∈ Finset.range M,
      ‖selectedPairSourceCoordinateSincVariation M q n a‖) ≤
      (12 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real))) * (harmonic M : Real) := by
  have hq0 : (q.val.val : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne q.val.val)
  have hM0 : (M : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hscale : 0 ≤
      6 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real)) := by positivity
  calc
    (∑ a ∈ Finset.range M,
      ‖selectedPairSourceCoordinateSincVariation M q n a‖) ≤
        ∑ a ∈ Finset.range M,
          6 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real) *
              (selectedPairSourceEdgeDistance n a : Real)) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact selectedPairSourceCoordinateSincVariation_norm_le_edgeDistance
        M hM q n a
    _ =
        (6 * (oddProjectWidth M : Real) /
          ((q.val.val : Real) * (M : Real))) *
            selectedPairSourceEdgeHarmonic M n := by
      unfold selectedPairSourceEdgeHarmonic
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      have hd0 : (selectedPairSourceEdgeDistance n a : Real) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (selectedPairSourceEdgeDistance_pos n a))
      field_simp
    _ ≤
        (6 * (oddProjectWidth M : Real) /
          ((q.val.val : Real) * (M : Real))) *
            (2 * (harmonic M : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (selectedPairSourceEdgeHarmonic_le_harmonic hn) hscale
    _ =
        (12 * (oddProjectWidth M : Real) /
          ((q.val.val : Real) * (M : Real))) * (harmonic M : Real) := by
      field_simp
      ring

theorem sum_selectedPairSourceCoordinateSincVariation_norm_le_log
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M) :
    (∑ a ∈ Finset.range M,
      ‖selectedPairSourceCoordinateSincVariation M q n a‖) ≤
      (12 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real))) *
          (1 + Real.log (M : Real)) := by
  have hscale : 0 ≤
      12 * (oddProjectWidth M : Real) /
        ((q.val.val : Real) * (M : Real)) := by positivity
  exact (sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
    M hM q n hn).trans
      (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) hscale)

/-- Abel ceiling before cancellation of the conductor prefix.  Unlike the
V1.8.718 coarse estimate, the total variation retains `1/M` and grows only by
the finite harmonic factor. -/
theorem sinc_phase_sum_norm_le_denominator_mul_endpoint_add_harmonicVariation
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M)
    (xi : ZMod q.val.val) (hxi : xi ≠ 0) :
    ‖∑ a ∈ Finset.range M.succ,
        selectedPairSourceCoordinateSincWeight M q n a *
          selectedPairRelativeAddCharPhase q.val.val n a xi‖ ≤
      (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          (12 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real))) * (harmonic M : Real)) := by
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
            (12 * (oddProjectWidth M : Real) /
              ((q.val.val : Real) * (M : Real))) * (harmonic M : Real)) := by
      gcongr
      exact sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
        M hM q n hn

theorem sinc_phase_sum_norm_le_denominator_mul_endpoint_add_logVariation
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ≤ M)
    (xi : ZMod q.val.val) (hxi : xi ≠ 0) :
    ‖∑ a ∈ Finset.range M.succ,
        selectedPairSourceCoordinateSincWeight M q n a *
          selectedPairRelativeAddCharPhase q.val.val n a xi‖ ≤
      (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          (12 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real))) *
              (1 + Real.log (M : Real))) := by
  calc
    _ ≤ (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          (12 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real))) * (harmonic M : Real)) :=
      sinc_phase_sum_norm_le_denominator_mul_endpoint_add_harmonicVariation
        M hM q n hn xi hxi
    _ ≤ _ := by
      gcongr
      exact harmonic_le_one_add_log M

/-- The sharp Abel bound on every source index used by V1.8.720.  Target
membership is not assumed globally: a false target makes the unchanged
source-separated kernel definitionally zero; a true target uses the sharp
Abel estimate. -/
theorem sum_selectedPairSourceSeparatedKernel_norm_le_log_allTargets
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ∈ Finset.range M.succ)
    (xi : ZMod q.val.val) (hxi : xi ≠ 0) :
    ‖∑ a ∈ Finset.range M.succ,
        selectedPairSourceSeparatedKernel M q n xi a‖ ≤
      (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          (12 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real))) *
              (1 + Real.log (M : Real))) := by
  have hnM : n ≤ M := by
    have hnLt : n < M.succ := Finset.mem_range.mp hn
    omega
  by_cases hTarget : 2 * n ∈ evenTargetBlock M
  · rw [sum_selectedPairSourceSeparatedKernel_eq_sinc_phase_sum
      M q n xi hTarget]
    exact sinc_phase_sum_norm_le_denominator_mul_endpoint_add_logVariation
      M hM q n hnM xi hxi
  · have hzero :
        (∑ a ∈ Finset.range M.succ,
          selectedPairSourceSeparatedKernel M q n xi a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      simp [selectedPairSourceSeparatedKernel, hTarget]
    rw [hzero, norm_zero]
    have hMOne : (1 : Real) ≤ (M : Real) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hM))
    have hlog : 0 ≤ Real.log (M : Real) := Real.log_nonneg hMOne
    positivity

theorem denominator_mul_endpoint_add_logVariation_eq
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M)) :
    (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          (12 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real))) *
              (1 + Real.log (M : Real))) =
      3 * (oddProjectWidth M : Real) / (M : Real) +
        (12 * (oddProjectWidth M : Real) / (M : Real)) *
          (1 + Real.log (M : Real)) := by
  have hM0 : (M : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hq0 : (q.val.val : Real) ≠ 0 := by
    exact_mod_cast (NeZero.ne q.val.val)
  field_simp

/-- Conductor-cancelled sharp kernel ceiling.  The former `O(P)` variation
term is replaced by `12 (P/M) (1 + log M)` without changing the underlying
kernel or either sinc radius. -/
theorem sum_selectedPairSourceSeparatedKernel_norm_le_logScale_allTargets
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ∈ Finset.range M.succ)
    (xi : ZMod q.val.val) (hxi : xi ≠ 0) :
    ‖∑ a ∈ Finset.range M.succ,
        selectedPairSourceSeparatedKernel M q n xi a‖ ≤
      3 * (oddProjectWidth M : Real) / (M : Real) +
        (12 * (oddProjectWidth M : Real) / (M : Real)) *
          (1 + Real.log (M : Real)) := by
  calc
    _ ≤ (q.val.val : Real) *
        (3 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real)) +
          (12 * (oddProjectWidth M : Real) /
            ((q.val.val : Real) * (M : Real))) *
              (1 + Real.log (M : Real))) :=
      sum_selectedPairSourceSeparatedKernel_norm_le_log_allTargets
        M hM q n hn xi hxi
    _ = _ := denominator_mul_endpoint_add_logVariation_eq M hM q

theorem actualLambdaPairConstantKernelTransform_norm_le_logScale_allTargets
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (hn : n ∈ Finset.range M.succ)
    (xi : ZMod q.val.val) (hxi : xi ≠ 0) :
    ‖actualLambdaPairConstantKernelTransform M
        (selectedPairSourceSeparatedKernel M q n xi)‖ ≤
      ‖(actualLambdaPairSourceMean M : Complex)‖ *
        (3 * (oddProjectWidth M : Real) / (M : Real) +
          (12 * (oddProjectWidth M : Real) / (M : Real)) *
            (1 + Real.log (M : Real))) := by
  rw [actualLambdaPairConstantKernelTransform_eq_mean_mul_sum,
    Complex.norm_mul]
  exact mul_le_mul_of_nonneg_left
    (sum_selectedPairSourceSeparatedKernel_norm_le_logScale_allTargets
      M hM q n hn xi hxi)
    (norm_nonneg _)

end GoldbachCircleMethodSharpSourceSincVariationV18721
