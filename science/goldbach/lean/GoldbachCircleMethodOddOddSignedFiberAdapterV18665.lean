import GoldbachCircleMethodOddOddSignedGapContractV18664
import GoldbachCircleMethodEvenEvenChannelCompositionV18661

/-!
# V1.8.665: exact signed-fiber adapter for the dense odd-odd channel

V1.8.663--664 isolate the remaining dense odd-odd one-sided moment and its
equivalent signed-magnitude gap.  This append-only module now rewrites the
literal odd-odd deficit without taking absolute values: pairs are grouped by
their exact sum `t = a + b`, and the signed real Ramanujan--sinc kernel is
retained at the exact shift `N - t`.

For an even target, every retained odd-odd pair sum and hence every resulting
integer shift is even.  The finite denominator kernel is also split exactly
into the nonoscillatory Ramanujan levels `q <= 2` and the levels `q > 2`.

No periodic cancellation, incomplete-block estimate, sinc-variation estimate,
signed-correlation estimate, or Goldbach conclusion is asserted here.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodOddOddSignedFiberAdapterV18665

open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodExactKernelJordanBalanceV18650
open GoldbachCircleMethodEvenSubchannelSplitV18660
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodSignedFullPrefixV1850

/-- Literal odd-odd pair carrier in the unchanged closed box `0 <= a,b <= M`. -/
private def oddOddPairCarrier (M : Nat) : Finset (Nat × Nat) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => Odd ab.1 ∧ Odd ab.2)

/-- The same carrier with the convolution diagonal `a+b=N` removed. -/
private def oddOddOffDiagonalPairCarrier (M N : Nat) : Finset (Nat × Nat) :=
  (((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => ab.1 + ab.2 ≠ N)).filter
      (fun ab => Odd ab.1 ∧ Odd ab.2)

/-- Every sum of two coordinates in the odd-odd box is even and at most `2*M`. -/
def oddOddSumCarrier (M : Nat) : Finset Nat :=
  (Finset.range (2 * M + 1)).filter Even

/-- The retained pair sums for target `N`; the missing value `t=N` records the
exact off-diagonal notch instead of hiding it in an endpoint estimate. -/
def oddOddOffDiagonalSumCarrier (M N : Nat) : Finset Nat :=
  (oddOddSumCarrier M).filter (fun t => t ≠ N)

theorem mem_oddOddOffDiagonalSumCarrier_iff (M N t : Nat) :
    t ∈ oddOddOffDiagonalSumCarrier M N ↔
      t ≤ 2 * M ∧ Even t ∧ t ≠ N := by
  simp [oddOddOffDiagonalSumCarrier, oddOddSumCarrier, and_assoc]

theorem oddOddOffDiagonalPairCarrier_maps_to_sumCarrier (M N : Nat) :
    ∀ ab ∈ oddOddOffDiagonalPairCarrier M N,
      ab.1 + ab.2 ∈ oddOddOffDiagonalSumCarrier M N := by
  intro ab hab
  rcases Finset.mem_filter.mp hab with ⟨habOff, haOdd, hbOdd⟩
  rcases Finset.mem_filter.mp habOff with ⟨habBox, hoff⟩
  rcases Finset.mem_product.mp habBox with ⟨ha, hb⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      rw [Finset.mem_range] at ha hb
      omega
    · exact haOdd.add_odd hbOdd
  · exact hoff

/-- Exact nonnegative Lambda-pair mass on one odd-odd pair-sum fiber. -/
noncomputable def oddOddPairFiberMass (M t : Nat) : Real :=
  ∑ ab ∈ oddOddPairCarrier M with ab.1 + ab.2 = t, lambdaPairWeight ab

theorem oddOddPairFiberMass_nonneg (M t : Nat) :
    0 ≤ oddOddPairFiberMass M t := by
  unfold oddOddPairFiberMass
  exact Finset.sum_nonneg fun ab _ => lambdaPairWeight_nonneg ab

/-- The literal signed odd-odd kernel sum before grouping by the pair sum. -/
noncomputable def explicitOddOddSignedKernelMass
    (M P R N : Nat) : Real :=
  ∑ ab ∈ oddOddOffDiagonalPairCarrier M N,
    lambdaPairWeight ab *
      (explicitMajorMaskSincKernel M P R
        ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re

/-- The V1.8.660 odd-odd deficit is exactly the signed real kernel sum.  This
restores the sign discarded by either positive-part mass separately. -/
theorem explicitOddOddSubchannelDeficit_eq_signedKernelMass
    (M P R N : Nat) :
    explicitOddOddSubchannelDeficit M P R N =
      explicitOddOddSignedKernelMass M P R N := by
  classical
  unfold explicitOddOddSubchannelDeficit
    explicitNegativeOddOddMass explicitPositiveOddOddMass
    explicitOddOddSignedKernelMass oddOddOffDiagonalPairCarrier
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ab _hab
  rw [← mul_sub, ← real_eq_positivePart_sub_negativePart]

/-- Exact finite fiberwise reindexing of the dense odd-odd deficit.  The
kernel remains signed and the omitted diagonal remains visible as `t != N`. -/
theorem explicitOddOddSignedKernelMass_eq_sum_fibers
    (M P R N : Nat) :
    explicitOddOddSignedKernelMass M P R N =
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        oddOddPairFiberMass M t *
          (explicitMajorMaskSincKernel M P R
            ((N : Int) - (t : Int))).re := by
  classical
  let f := fun ab : Nat × Nat =>
    lambdaPairWeight ab *
      (explicitMajorMaskSincKernel M P R
        ((N : Int) - (ab.1 : Int) - (ab.2 : Int))).re
  have hFiber :
      (∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        ∑ ab ∈ oddOddOffDiagonalPairCarrier M N with ab.1 + ab.2 = t,
          f ab) =
        ∑ ab ∈ oddOddOffDiagonalPairCarrier M N, f ab :=
    Finset.sum_fiberwise_of_maps_to
      (oddOddOffDiagonalPairCarrier_maps_to_sumCarrier M N) f
  unfold explicitOddOddSignedKernelMass
  rw [← hFiber]
  apply Finset.sum_congr rfl
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨_htEvenCarrier, htNe⟩
  unfold oddOddPairFiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr
  · ext ab
    unfold oddOddOffDiagonalPairCarrier oddOddPairCarrier
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨habBox, habNe⟩, habOdd⟩, habt⟩
      exact ⟨⟨habBox, habOdd⟩, habt⟩
    · rintro ⟨⟨habBox, habOdd⟩, habt⟩
      refine ⟨⟨⟨habBox, ?_⟩, habOdd⟩, habt⟩
      intro habN
      exact htNe (habt ▸ habN)
  · intro ab hab
    have habt : ab.1 + ab.2 = t := (Finset.mem_filter.mp hab).2
    have hshift :
        (N : Int) - (ab.1 : Int) - (ab.2 : Int) =
          (N : Int) - (t : Int) := by
      have habtInt : (ab.1 : Int) + (ab.2 : Int) = (t : Int) := by
        exact_mod_cast habt
      omega
    simp only [f]
    rw [hshift]

/-- Main exact V1.8.665 adapter from the V1.8.663 deficit to its signed
one-dimensional pair-sum fibers. -/
theorem explicitOddOddSubchannelDeficit_eq_signed_fibers
    (M P R N : Nat) :
    explicitOddOddSubchannelDeficit M P R N =
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        oddOddPairFiberMass M t *
          (explicitMajorMaskSincKernel M P R
            ((N : Int) - (t : Int))).re := by
  rw [explicitOddOddSubchannelDeficit_eq_signedKernelMass]
  exact explicitOddOddSignedKernelMass_eq_sum_fibers M P R N

/-- On an even target, every retained odd-odd fiber produces an even integer
shift.  No division by two or endpoint replacement is performed here. -/
theorem retained_oddOdd_shift_even
    {M N t : Nat} (hN : Even N)
    (ht : t ∈ oddOddOffDiagonalSumCarrier M N) :
    Even ((N : Int) - (t : Int)) := by
  have htEven : Even t :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
  have hNInt : Even (N : Int) := by exact_mod_cast hN
  have htInt : Even (t : Int) := by exact_mod_cast htEven
  exact hNInt.sub htInt

/-- One literal denominator summand in the exact V1.8.649 kernel. -/
noncomputable def explicitDenominatorSincTerm
    (M P R : Nat) (k : Int)
    (q : Denominator R) : Complex :=
  integerFourierRamanujan q.val (-k) (NeZero.ne q.val) *
    (((Real.sin
        (2 * Real.pi * (k : Real) *
          ((P : Real) / ((q.val : Real) * (M : Real)))) /
        (Real.pi * (k : Real))) : Real) : Complex)

/-- Exact `q=1,2` part of the kernel.  Positivity is not asserted. -/
noncomputable def explicitSmallDenominatorSincKernel
    (M P R : Nat) (k : Int) : Complex :=
  ∑ q ∈ (Finset.univ.filter (fun q : Denominator R => q.val ≤ 2)),
    explicitDenominatorSincTerm M P R k q

theorem smallDenominator_eq_one_or_two
    {R : Nat} {q : Denominator R} (hq : q.val ≤ 2) :
    q.val = 1 ∨ q.val = 2 := by
  have hqOne : 1 ≤ q.val := (Finset.mem_Icc.mp q.property).1
  omega

/-- Exact `q>2` part of the kernel.  No cancellation is asserted. -/
noncomputable def explicitLargeDenominatorSincKernel
    (M P R : Nat) (k : Int) : Complex :=
  ∑ q ∈ (Finset.univ.filter (fun q : Denominator R => 2 < q.val)),
    explicitDenominatorSincTerm M P R k q

theorem explicitMajorMaskSincKernel_eq_small_add_large
    (M P R : Nat) (k : Int) :
    explicitMajorMaskSincKernel M P R k =
      explicitSmallDenominatorSincKernel M P R k +
        explicitLargeDenominatorSincKernel M P R k := by
  classical
  unfold explicitMajorMaskSincKernel explicitSmallDenominatorSincKernel
    explicitLargeDenominatorSincKernel explicitDenominatorSincTerm
  simpa only [Nat.not_le] using
    (Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun q : Denominator R => q.val ≤ 2)
        (fun q : Denominator R =>
          integerFourierRamanujan q.val (-k) (NeZero.ne q.val) *
            (((Real.sin
                (2 * Real.pi * (k : Real) *
                  ((P : Real) / ((q.val : Real) * (M : Real)))) /
                (Real.pi * (k : Real))) : Real) : Complex))).symm

/-- The exact denominator split transported through the signed odd-odd fiber
adapter.  This is algebra only; neither summand receives a sign or size claim. -/
theorem explicitOddOddSubchannelDeficit_eq_small_add_large_fibers
    (M P R N : Nat) :
    explicitOddOddSubchannelDeficit M P R N =
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        oddOddPairFiberMass M t *
          ((explicitSmallDenominatorSincKernel M P R
              ((N : Int) - (t : Int))).re +
            (explicitLargeDenominatorSincKernel M P R
              ((N : Int) - (t : Int))).re) := by
  rw [explicitOddOddSubchannelDeficit_eq_signed_fibers]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [explicitMajorMaskSincKernel_eq_small_add_large]
  rfl

end GoldbachCircleMethodOddOddSignedFiberAdapterV18665
