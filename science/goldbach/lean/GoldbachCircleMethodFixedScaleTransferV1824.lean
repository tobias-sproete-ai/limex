import GoldbachCircleMethodHighMinorBudgetV1822

/-!
# Fixed-scale Fourier transfer, V1.8.24

This module proves that padding the finite von Mangoldt exponential sum beyond
the target frequency does not change that target Fourier coefficient. It then
defines a fixed-scale major/minor split in which the same `majorArcs pM` mask
is used for every target frequency `N ≤ pM.N`, and proves its exact partition.

No major-arc margin or minor-arc moment estimate is supplied. In particular,
this module does not transfer any source theorem into a pointwise Goldbach
statement and proves no Goldbach statement.
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodFixedScaleTransferV1824

open GoldbachVonMangoldtDecompositionV16
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodQStarBooleanGeometryV185
open GoldbachCircleMethodHighMinorBudgetV1822

private lemma integrable_const_mul_fourier (c : Complex) (n : Int) :
    MeasureTheory.Integrable
      (fun x : UnitAddCircle => c * fourier n x)
      AddCircle.haarAddCircle := by
  have h : MeasureTheory.Integrable
      (fourier n : UnitAddCircle → Complex) AddCircle.haarAddCircle := by
    simpa only [MeasureTheory.IntegrableOn,
      MeasureTheory.Measure.restrict_univ] using
      (ContinuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle)
        (K := Set.univ) isCompact_univ (fourier n).continuous.continuousOn)
  exact h.const_mul c

private lemma coeff_const_mul_fourier (c : Complex) (n k : Int) :
    fourierCoeff (fun x : UnitAddCircle => c * fourier n x) k =
      if k = n then c else 0 := by
  rw [fourierCoeff.const_mul]
  rw [congrFun (fourierCoeff_fourier n) k]
  by_cases h : k = n
  · subst k
    simp
  · simp [h]

private lemma coeff_finset_fourier_sum
    (s : Finset Nat) (c : Nat → Complex) (frequency : Nat → Int) (k : Int) :
    fourierCoeff
        (fun x : UnitAddCircle =>
          ∑ n ∈ s, c n * fourier (frequency n) x) k =
      ∑ n ∈ s, if k = frequency n then c n else 0 := by
  have hFunction :
      (fun x : UnitAddCircle =>
        ∑ n ∈ s, c n * fourier (frequency n) x) =
        ∑ n ∈ s,
          (fun x : UnitAddCircle => c n * fourier (frequency n) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hFunction, fourierCoeff.sum]
  simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro n hn
    exact coeff_const_mul_fourier _ _ _
  · intro n hn
    exact integrable_const_mul_fourier _ _

private lemma integrable_finset_fourier_sum
    (s : Finset Nat) (c : Nat → Complex) (frequency : Nat → Int) :
    MeasureTheory.Integrable
      (fun x : UnitAddCircle =>
        ∑ n ∈ s, c n * fourier (frequency n) x)
      AddCircle.haarAddCircle := by
  have hFunction :
      (fun x : UnitAddCircle =>
        ∑ n ∈ s, c n * fourier (frequency n) x) =
        ∑ n ∈ s,
          (fun x : UnitAddCircle => c n * fourier (frequency n) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hFunction]
  exact MeasureTheory.integrable_finsetSum' _ fun n hn =>
    integrable_const_mul_fourier _ _

/-- The full square expanded at an ambient cutoff `M`. -/
noncomputable def expandedSquareAt (M : Nat) : UnitAddCircle → Complex :=
  fun x =>
    ∑ n ∈ Finset.range M.succ,
      ∑ m ∈ Finset.range M.succ,
        ((ArithmeticFunction.vonMangoldt n : Complex) *
            ArithmeticFunction.vonMangoldt m) *
          fourier ((n : Int) + (m : Int)) x

private lemma coeff_expandedSquareAt (M N : Nat) :
    fourierCoeff (expandedSquareAt M) (N : Int) =
      ∑ n ∈ Finset.range M.succ,
        ∑ m ∈ Finset.range M.succ,
          if (N : Int) = (n : Int) + (m : Int) then
            (ArithmeticFunction.vonMangoldt n : Complex) *
              ArithmeticFunction.vonMangoldt m
          else 0 := by
  unfold expandedSquareAt
  have hOuter :
      (fun x : UnitAddCircle =>
        ∑ n ∈ Finset.range M.succ,
          ∑ m ∈ Finset.range M.succ,
            ((ArithmeticFunction.vonMangoldt n : Complex) *
                ArithmeticFunction.vonMangoldt m) *
              fourier ((n : Int) + (m : Int)) x) =
        ∑ n ∈ Finset.range M.succ,
          (fun x : UnitAddCircle =>
            ∑ m ∈ Finset.range M.succ,
              ((ArithmeticFunction.vonMangoldt n : Complex) *
                  ArithmeticFunction.vonMangoldt m) *
                fourier ((n : Int) + (m : Int)) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hOuter, fourierCoeff.sum]
  simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro n hn
    exact coeff_finset_fourier_sum
      (Finset.range M.succ)
      (fun m => (ArithmeticFunction.vonMangoldt n : Complex) *
        ArithmeticFunction.vonMangoldt m)
      (fun m => (n : Int) + (m : Int))
      (N : Int)
  · intro n hn
    exact integrable_finset_fourier_sum
      (Finset.range M.succ)
      (fun m => (ArithmeticFunction.vonMangoldt n : Complex) *
        ArithmeticFunction.vonMangoldt m)
      (fun m => (n : Int) + (m : Int))

private lemma exponentialSum_sq_eq_expandedSquareAt
    (M : Nat) (x : UnitAddCircle) :
    exponentialSum M.succ x * exponentialSum M.succ x =
      expandedSquareAt M x := by
  have hExponential : exponentialSum M.succ x =
      ∑ n ∈ Finset.range M.succ,
        (ArithmeticFunction.vonMangoldt n : Complex) * fourier (n : Int) x := by
    simp [exponentialSum]
  rw [hExponential]
  unfold expandedSquareAt
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [fourier_add]
  ring

private lemma inner_frequency_sum_of_le
    (M N n : Nat) (hNM : N ≤ M) (hnN : n ≤ N) :
    (∑ m ∈ Finset.range M.succ,
      if (N : Int) = (n : Int) + (m : Int) then
        (ArithmeticFunction.vonMangoldt n : Complex) *
          ArithmeticFunction.vonMangoldt m
      else 0) =
      (ArithmeticFunction.vonMangoldt n : Complex) *
        ArithmeticFunction.vonMangoldt (N - n) := by
  calc
    _ = if (N : Int) = (n : Int) + ((N - n : Nat) : Int) then
          (ArithmeticFunction.vonMangoldt n : Complex) *
            ArithmeticFunction.vonMangoldt (N - n)
        else 0 := by
      apply Finset.sum_eq_single (N - n)
      · intro m hm hne
        rw [if_neg]
        intro heq
        norm_cast at heq
        apply hne
        omega
      · intro hnotmem
        exfalso
        apply hnotmem
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.sub_le N n).trans hNM))
    _ = _ := by
      rw [if_pos]
      norm_cast
      omega

private lemma inner_frequency_sum_of_gt
    (M N n : Nat) (hnN : N < n) :
    (∑ m ∈ Finset.range M.succ,
      if (N : Int) = (n : Int) + (m : Int) then
        (ArithmeticFunction.vonMangoldt n : Complex) *
          ArithmeticFunction.vonMangoldt m
      else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  rw [if_neg]
  intro heq
  norm_cast at heq
  omega

private lemma vonMangoldt_zero : ArithmeticFunction.vonMangoldt 0 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  exact not_isPrimePow_zero

private lemma complex_vonMangoldt_pair_sum_range_succ (N : Nat) :
    (∑ n ∈ Finset.range N.succ,
      (ArithmeticFunction.vonMangoldt n : Complex) *
        ArithmeticFunction.vonMangoldt (N - n)) =
      (vonMangoldtPairSum N : Complex) := by
  rw [Finset.sum_range_succ]
  rw [show N - N = 0 by omega, vonMangoldt_zero]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [vonMangoldtPairSum]
  norm_cast

/--
Padding the finite exponential sum from the native cutoff `N` to any ambient
cutoff `M ≥ N` leaves its `N`-th squared Fourier coefficient unchanged.
-/
theorem fourierCoeff_padded_exponentialSum_sq_eq_vonMangoldtPairSum
    (M N : Nat) (hNM : N ≤ M) :
    fourierCoeff
        (fun x : UnitAddCircle =>
          exponentialSum M.succ x * exponentialSum M.succ x)
        (N : Int) =
      (vonMangoldtPairSum N : Complex) := by
  have hFunction :
      (fun x : UnitAddCircle =>
        exponentialSum M.succ x * exponentialSum M.succ x) =
        expandedSquareAt M := by
    funext x
    exact exponentialSum_sq_eq_expandedSquareAt M x
  rw [hFunction, coeff_expandedSquareAt]
  have hSubset : Finset.range N.succ ⊆ Finset.range M.succ :=
    Finset.range_mono (Nat.succ_le_succ hNM)
  have hSumSubset :
      (∑ n ∈ Finset.range N.succ,
        ∑ m ∈ Finset.range M.succ,
          if (N : Int) = (n : Int) + (m : Int) then
            (ArithmeticFunction.vonMangoldt n : Complex) *
              ArithmeticFunction.vonMangoldt m
          else 0) =
      ∑ n ∈ Finset.range M.succ,
        ∑ m ∈ Finset.range M.succ,
          if (N : Int) = (n : Int) + (m : Int) then
            (ArithmeticFunction.vonMangoldt n : Complex) *
              ArithmeticFunction.vonMangoldt m
          else 0 := by
    apply Finset.sum_subset hSubset
    intro n hnM hnN
    exact inner_frequency_sum_of_gt M N n (by
      have hnNot : ¬ n < N.succ := by
        simpa only [Finset.mem_range] using hnN
      omega)
  rw [← hSumSubset]
  calc
    _ = ∑ n ∈ Finset.range N.succ,
        (ArithmeticFunction.vonMangoldt n : Complex) *
          ArithmeticFunction.vonMangoldt (N - n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact inner_frequency_sum_of_le M N n hNM
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
    _ = (vonMangoldtPairSum N : Complex) :=
      complex_vonMangoldt_pair_sum_range_succ N

/-- The `N`-frequency circle-method integrand at a common ambient scale `M`. -/
noncomputable def fixedScalePairFourierIntegrand
    (M N : Nat) (x : UnitAddCircle) : Complex :=
  fourier (-(N : Int)) x *
    (exponentialSum M.succ x * exponentialSum M.succ x)

theorem fixedScalePairFourierIntegrand_integrable (M N : Nat) :
    MeasureTheory.Integrable (fixedScalePairFourierIntegrand M N)
      AddCircle.haarAddCircle := by
  have hContinuous : Continuous (fixedScalePairFourierIntegrand M N) :=
    (fourier (-(N : Int))).continuous.mul
      ((exponentialSum M.succ).continuous.mul (exponentialSum M.succ).continuous)
  simpa only [MeasureTheory.IntegrableOn,
    MeasureTheory.Measure.restrict_univ] using
    (ContinuousOn.integrableOn_compact
      (μ := AddCircle.haarAddCircle)
      (K := Set.univ) isCompact_univ hContinuous.continuousOn)

theorem integral_fixedScalePairFourierIntegrand_eq_vonMangoldtPairSum
    (M N : Nat) (hNM : N ≤ M) :
    (∫ x : UnitAddCircle, fixedScalePairFourierIntegrand M N x
        ∂AddCircle.haarAddCircle) =
      (vonMangoldtPairSum N : Complex) := by
  rw [← fourierCoeff_padded_exponentialSum_sq_eq_vonMangoldtPairSum M N hNM]
  rfl

/-- Fixed-ambient-scale real part over the same concrete denominator cover. -/
noncomputable def fixedScaleLowerIntegralReal
    (p : ArcParameters) (M Q U : Nat) : Real :=
  Complex.re
    (∫ x in denominatorCover p Q U,
      fixedScalePairFourierIntegrand M p.N x ∂AddCircle.haarAddCircle)

/-- Fixed-ambient-scale real part over the complementary high region. -/
noncomputable def fixedScaleHighIntegralReal
    (p : ArcParameters) (M Q U : Nat) : Real :=
  Complex.re
    (∫ x in (denominatorCover p Q U)ᶜ,
      fixedScalePairFourierIntegrand M p.N x ∂AddCircle.haarAddCircle)

/-- Exact fixed-scale real-part partition at target frequency `p.N`. -/
theorem fixedScaleLower_add_high_eq_vonMangoldtPairSum
    (p : ArcParameters) (M Q U : Nat) (hNM : p.N ≤ M) :
    fixedScaleLowerIntegralReal p M Q U +
        fixedScaleHighIntegralReal p M Q U =
      vonMangoldtPairSum p.N := by
  have hSplit :
      (∫ x in denominatorCover p Q U,
          fixedScalePairFourierIntegrand M p.N x ∂AddCircle.haarAddCircle) +
        (∫ x in (denominatorCover p Q U)ᶜ,
          fixedScalePairFourierIntegrand M p.N x ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle,
          fixedScalePairFourierIntegrand M p.N x ∂AddCircle.haarAddCircle := by
    exact MeasureTheory.integral_add_compl
      (denominatorCover_measurable p Q U)
      (fixedScalePairFourierIntegrand_integrable M p.N)
  have hFull :=
    integral_fixedScalePairFourierIntegrand_eq_vonMangoldtPairSum M p.N hNM
  have hComplex := hSplit.trans hFull
  calc
    fixedScaleLowerIntegralReal p M Q U +
        fixedScaleHighIntegralReal p M Q U =
        Complex.re
          ((∫ x in denominatorCover p Q U,
              fixedScalePairFourierIntegrand M p.N x ∂AddCircle.haarAddCircle) +
            (∫ x in (denominatorCover p Q U)ᶜ,
              fixedScalePairFourierIntegrand M p.N x ∂AddCircle.haarAddCircle)) := by
          simp [fixedScaleLowerIntegralReal, fixedScaleHighIntegralReal]
    _ = Complex.re (vonMangoldtPairSum p.N : Complex) :=
      congrArg Complex.re hComplex
    _ = vonMangoldtPairSum p.N := by simp

/--
The native/fixed lower discrepancy is exactly cancelled by the corresponding
high discrepancy. This is an identity only, not a discrepancy estimate.
-/
theorem fixed_native_mask_discrepancy_identity
    (p : ArcParameters) (M Q U : Nat) (hNM : p.N ≤ M) :
    fixedScaleLowerIntegralReal p M Q U - lowerIntegralReal p Q U =
      -(fixedScaleHighIntegralReal p M Q U - highIntegralReal p Q U) := by
  have hFixed := fixedScaleLower_add_high_eq_vonMangoldtPairSum p M Q U hNM
  have hNative := lower_add_high_eq_vonMangoldtPairSum p Q U
  linarith

/-
Fixed-ambient-scale real part over the single major-arc mask `majorArcs pM`.
The mask and ambient cutoff are independent of the target frequency `N`.
-/
noncomputable def fixedScaleMajorIntegralReal
    (pM : ArcParameters) (N : Nat) : Real :=
  Complex.re
    (∫ x in majorArcs pM,
      fixedScalePairFourierIntegrand pM.N N x ∂AddCircle.haarAddCircle)

/-- Fixed-ambient-scale real part over the complementary minor-arc mask. -/
noncomputable def fixedScaleMinorIntegralReal
    (pM : ArcParameters) (N : Nat) : Real :=
  Complex.re
    (∫ x in minorArcs pM,
      fixedScalePairFourierIntegrand pM.N N x ∂AddCircle.haarAddCircle)

/-
Exact fixed-scale real-part partition at every protected frequency `N ≤ pM.N`.
This is a coefficient identity and contains no estimate on either arc region.
-/
theorem fixedScaleMajor_add_minor_eq_vonMangoldtPairSum
    (pM : ArcParameters) (N : Nat) (hNM : N ≤ pM.N) :
    fixedScaleMajorIntegralReal pM N +
        fixedScaleMinorIntegralReal pM N =
      vonMangoldtPairSum N := by
  have hSplit :
      (∫ x in majorArcs pM,
          fixedScalePairFourierIntegrand pM.N N x ∂AddCircle.haarAddCircle) +
        (∫ x in minorArcs pM,
          fixedScalePairFourierIntegrand pM.N N x ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle,
          fixedScalePairFourierIntegrand pM.N N x ∂AddCircle.haarAddCircle := by
    rw [minorArcs]
    exact MeasureTheory.integral_add_compl
      (majorArcs_measurable pM)
      (fixedScalePairFourierIntegrand_integrable pM.N N)
  have hFull :=
    integral_fixedScalePairFourierIntegrand_eq_vonMangoldtPairSum pM.N N hNM
  have hComplex := hSplit.trans hFull
  calc
    fixedScaleMajorIntegralReal pM N +
        fixedScaleMinorIntegralReal pM N =
        Complex.re
          ((∫ x in majorArcs pM,
              fixedScalePairFourierIntegrand pM.N N x ∂AddCircle.haarAddCircle) +
            (∫ x in minorArcs pM,
              fixedScalePairFourierIntegrand pM.N N x ∂AddCircle.haarAddCircle)) := by
          simp [fixedScaleMajorIntegralReal, fixedScaleMinorIntegralReal]
    _ = Complex.re (vonMangoldtPairSum N : Complex) :=
      congrArg Complex.re hComplex
    _ = vonMangoldtPairSum N := by simp

end GoldbachCircleMethodFixedScaleTransferV1824
