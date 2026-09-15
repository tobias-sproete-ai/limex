import GoldbachCircleMethodOddOddSignedFiberAdapterV18665
import GoldbachCircleMethodFullSquarefreeCoefficientV1847

/-!
# V1.8.666: exact small-denominator split and a literal sign obstruction

V1.8.665 preserves the signed odd-odd pair-sum fibers and splits the exact
Ramanujan--sinc kernel at `q = 2`.  This append-only module resolves the small
part further into the literal `q = 1` and `q = 2` summands whenever `R >= 2`.

It also tests the tempting but invalid shortcut that the nonoscillatory
small-denominator contribution should be nonnegative on every retained even
shift.  At the actual parameter point

`M = 16, P = 1, R = 2, N = 8, t = 20, k = N-t = -12`,

the odd-odd fiber has positive von-Mangoldt mass, while its exact `q <= 2`
real kernel coefficient is strictly negative.  This is a typed negative
witness against pointwise small-denominator positivity; it is not a bound on
the full `q <= R` kernel and not a Goldbach theorem.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodOddOddSmallDenominatorNegativeWitnessV18666

open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodFullSquarefreeCoefficientV1847
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648

/-- The unique denominator-one point in `Denominator R`. -/
def denominatorOne (R : Nat) (hR : 1 <= R) : Denominator R :=
  ⟨1, Finset.mem_Icc.mpr ⟨by omega, hR⟩⟩

/-- The unique denominator-two point in `Denominator R`. -/
def denominatorTwo (R : Nat) (hR : 2 <= R) : Denominator R :=
  ⟨2, Finset.mem_Icc.mpr ⟨by omega, hR⟩⟩

theorem smallDenominatorCarrier_eq_pair
    (R : Nat) (hR : 2 <= R) :
    (Finset.univ.filter (fun q : Denominator R => q.val <= 2)) =
      {denominatorOne R (by omega), denominatorTwo R hR} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hq
    have hqOne : 1 <= q.val := (Finset.mem_Icc.mp q.property).1
    rcases show q.val = 1 ∨ q.val = 2 by omega with h | h
    · left
      exact Subtype.ext h
    · right
      exact Subtype.ext h
  · rintro (h | h)
    · rw [h]
      norm_num [denominatorOne]
    · rw [h]
      norm_num [denominatorTwo]

/-- Exact refinement of the V1.8.665 small-denominator kernel into its two
literal summands. -/
theorem explicitSmallDenominatorSincKernel_eq_one_add_two
    (M P R : Nat) (k : Int) (hR : 2 <= R) :
    explicitSmallDenominatorSincKernel M P R k =
      explicitDenominatorSincTerm M P R k (denominatorOne R (by omega)) +
        explicitDenominatorSincTerm M P R k (denominatorTwo R hR) := by
  unfold explicitSmallDenominatorSincKernel
  rw [smallDenominatorCarrier_eq_pair R hR]
  simp [denominatorOne, denominatorTwo]

/-- Exact three-way split: `q=1`, `q=2`, and `q>2`. -/
theorem explicitMajorMaskSincKernel_eq_one_add_two_add_large
    (M P R : Nat) (k : Int) (hR : 2 <= R) :
    GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649.explicitMajorMaskSincKernel
        M P R k =
      explicitDenominatorSincTerm M P R k (denominatorOne R (by omega)) +
        explicitDenominatorSincTerm M P R k (denominatorTwo R hR) +
          explicitLargeDenominatorSincKernel M P R k := by
  rw [explicitMajorMaskSincKernel_eq_small_add_large]
  rw [explicitSmallDenominatorSincKernel_eq_one_add_two M P R k hR]

/-- The same exact split at every retained odd-odd fiber of an even target.
The parity hypothesis is consumed to certify the literal shift as even. -/
theorem retained_even_shift_kernel_eq_one_add_two_add_large
    {M P R N t : Nat} (hN : Even N)
    (ht : t ∈ oddOddOffDiagonalSumCarrier M N) (hR : 2 <= R) :
    GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649.explicitMajorMaskSincKernel
        M P R ((N : Int) - (t : Int)) =
      explicitDenominatorSincTerm M P R ((N : Int) - (t : Int))
          (denominatorOne R (by omega)) +
        explicitDenominatorSincTerm M P R ((N : Int) - (t : Int))
          (denominatorTwo R hR) +
        explicitLargeDenominatorSincKernel M P R ((N : Int) - (t : Int)) := by
  have _hEven : Even ((N : Int) - (t : Int)) :=
    retained_oddOdd_shift_even hN ht
  exact explicitMajorMaskSincKernel_eq_one_add_two_add_large
    M P R ((N : Int) - (t : Int)) hR

/-- The three-way split transported through the complete signed odd-odd
fiber sum.  The target parity is retained in the signature and checked at
every summand; no sign or triangle inequality is introduced. -/
theorem explicitOddOddSubchannelDeficit_eq_one_add_two_add_large_fibers
    (M P R N : Nat) (hN : Even N) (hR : 2 <= R) :
    GoldbachCircleMethodEvenSubchannelSplitV18660.explicitOddOddSubchannelDeficit
        M P R N =
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        oddOddPairFiberMass M t *
          ((explicitDenominatorSincTerm M P R ((N : Int) - (t : Int))
              (denominatorOne R (by omega))).re +
            (explicitDenominatorSincTerm M P R ((N : Int) - (t : Int))
              (denominatorTwo R hR)).re +
            (explicitLargeDenominatorSincKernel M P R
              ((N : Int) - (t : Int))).re) := by
  rw [explicitOddOddSubchannelDeficit_eq_signed_fibers]
  apply Finset.sum_congr rfl
  intro t ht
  rw [retained_even_shift_kernel_eq_one_add_two_add_large hN ht hR]
  rfl

/-- The denominator-one character is exactly one at the witness frequency. -/
theorem integerFourierRamanujan_one_twelve :
    integerFourierRamanujan 1 12 one_ne_zero = 1 := by
  calc
    integerFourierRamanujan 1 12 one_ne_zero =
        finiteFourierRamanujan 1 12 one_ne_zero :=
      integerFourierRamanujan_natCast 1 12 one_ne_zero
    _ = 1 := by rw [finiteFourierRamanujan_one]; norm_num

/-- The denominator-two character is exactly one at the witness frequency. -/
theorem integerFourierRamanujan_two_twelve :
    integerFourierRamanujan 2 12 (by norm_num) = 1 := by
  calc
    integerFourierRamanujan 2 12 (by norm_num) =
        finiteFourierRamanujan 2 12 (by norm_num) :=
      integerFourierRamanujan_natCast 2 12 (by norm_num)
    _ = (Nat.totient 2 : Complex) :=
      finiteFourierRamanujan_eq_totient_of_dvd (by norm_num) (by norm_num)
    _ = 1 := by norm_num

/-- The concrete retained odd-odd fiber used by the negative witness. -/
theorem twenty_mem_oddOddOffDiagonalSumCarrier_sixteen_eight :
    20 ∈ oddOddOffDiagonalSumCarrier 16 8 := by
  rw [mem_oddOddOffDiagonalSumCarrier_iff]
  norm_num

/-- The concrete pair `(7,13)` supplies strictly positive mass on the actual
odd-odd fiber `t=20`. -/
theorem oddOddPairFiberMass_sixteen_twenty_pos :
    0 < oddOddPairFiberMass 16 20 := by
  unfold oddOddPairFiberMass
  have hmem : (7, 13) ∈
      ((Finset.range 17).product (Finset.range 17)).filter
        (fun ab => Odd ab.1 ∧ Odd ab.2) := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨by norm_num, by norm_num⟩
    · exact ⟨⟨3, rfl⟩, ⟨6, rfl⟩⟩
  have hterm : 0 < lambdaPairWeight (7, 13) := by
    unfold lambdaPairWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 7),
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 13)]
    exact mul_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  have hle : lambdaPairWeight (7, 13) <=
      ∑ ab ∈
        (((Finset.range 17).product (Finset.range 17)).filter
          (fun ab => Odd ab.1 ∧ Odd ab.2)) with ab.1 + ab.2 = 20,
        lambdaPairWeight ab := by
    apply Finset.single_le_sum
    · intro ab hab
      exact lambdaPairWeight_nonneg ab
    · apply Finset.mem_filter.mpr
      exact ⟨hmem, by norm_num⟩
  exact lt_of_lt_of_le hterm hle

/-- Exact closed form of the actual `q <= 2` coefficient at the retained
shift `k=-12`. -/
theorem smallKernel_sixteen_one_two_neg_twelve_exact :
    (explicitSmallDenominatorSincKernel 16 1 2 (-12)).re =
      (Real.sqrt 2 / 2 - 1) / (12 * Real.pi) := by
  rw [explicitSmallDenominatorSincKernel_eq_one_add_two 16 1 2 (-12)
    (by norm_num)]
  unfold explicitDenominatorSincTerm
  simp only [denominatorOne, denominatorTwo]
  simp only [neg_neg]
  rw [integerFourierRamanujan_one_twelve,
    integerFourierRamanujan_two_twelve]
  simp only [one_mul, Complex.add_re, Complex.ofReal_re]
  norm_num only [Int.cast_ofNat, Nat.cast_ofNat]
  rw [show (2 * Real.pi * (-12) * (1 / 16)) =
      -(3 * Real.pi / 2) by ring,
    show (2 * Real.pi * (-12) * (1 / 32)) =
      -(3 * Real.pi / 4) by ring]
  rw [Real.sin_neg, Real.sin_neg]
  rw [show Real.sin (3 * Real.pi / 2) = -1 by
    rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
      Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two]
    ring]
  rw [show Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_four]]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- Kernel-checked negative witness: the literal `q=1,2` real kernel on this
retained even shift is strictly negative. -/
theorem smallKernel_sixteen_one_two_neg_twelve_neg :
    (explicitSmallDenominatorSincKernel 16 1 2 (-12)).re < 0 := by
  rw [smallKernel_sixteen_one_two_neg_twelve_exact]
  have hsqrt : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]
  have hnum : Real.sqrt 2 / 2 - 1 < 0 := by linarith
  have hden : 0 < 12 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  exact div_neg_of_neg_of_pos hnum hden

/-- The negative coefficient is attached to a genuinely positive actual
odd-odd von-Mangoldt fiber, not to an empty or abstract carrier. -/
theorem actual_positive_oddOdd_fiber_with_negative_small_kernel :
    0 < oddOddPairFiberMass 16 20 ∧
      (explicitSmallDenominatorSincKernel 16 1 2
        ((8 : Int) - (20 : Int))).re < 0 := by
  constructor
  · exact oddOddPairFiberMass_sixteen_twenty_pos
  · norm_num
    exact smallKernel_sixteen_one_two_neg_twelve_neg

/-- Strong form of the same witness: the actual positive fiber mass times
the exact small-denominator real kernel coefficient is strictly negative. -/
theorem actual_oddOdd_fiber_small_denominator_contribution_neg :
    oddOddPairFiberMass 16 20 *
      (explicitSmallDenominatorSincKernel 16 1 2
        ((8 : Int) - (20 : Int))).re < 0 := by
  apply mul_neg_of_pos_of_neg oddOddPairFiberMass_sixteen_twenty_pos
  norm_num
  exact smallKernel_sixteen_one_two_neg_twelve_neg

end GoldbachCircleMethodOddOddSmallDenominatorNegativeWitnessV18666
