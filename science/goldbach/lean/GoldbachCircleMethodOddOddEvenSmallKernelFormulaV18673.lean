import GoldbachCircleMethodOddOddSmallCoreEnergyCeilingV18672

/-!
# V1.8.673: exact even-shift formula for the literal small kernel

The V1.8.666 negative witness shows that the literal `q <= 2` sinc kernel is
not termwise nonnegative.  This append-only successor removes the two remaining
Ramanujan atoms on every even integer shift and exposes the real kernel as the
sum of two explicit sine quotients.

The formula is transported, without absolute values or estimates, through the
actual Odd-Odd pair-fiber sum and into the compensated small core from
V1.8.670.  A final theorem substitutes the project width
`P = 8 * R^2`, leaving the exact phases `16*pi*k*R^2/M` and
`8*pi*k*R^2/M` visible.

No sign, moment estimate, asymptotic decay, or Goldbach conclusion is proved.
The analytic small-core budget from V1.8.672 remains open.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodOddOddEvenSmallKernelFormulaV18673

open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodFullSquarefreeCoefficientV1847
open GoldbachCircleMethodOddOddSmallDenominatorNegativeWitnessV18666
open GoldbachCircleMethodOddOddSmallCoreLargePerturbationV18670
open GoldbachCircleMethodDiagonalCompensatedEvenSubchannelsV18667
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639

/-- The explicit real two-sine expression carried by the `q=1,2` kernel on
an even shift.  It is defined separately so the fiber transport below has no
hidden complex coercions. -/
noncomputable def explicitEvenSmallKernelReal
    (M P : Nat) (k : Int) : Real :=
  Real.sin
      (2 * Real.pi * (k : Real) * ((P : Real) / (M : Real))) /
      (Real.pi * (k : Real)) +
    Real.sin
      (Real.pi * (k : Real) * ((P : Real) / (M : Real))) /
      (Real.pi * (k : Real))

/-- At denominator one the integer Ramanujan character is exactly one for
every signed integer frequency. -/
theorem integerFourierRamanujan_one_eq_one (k : Int) :
    integerFourierRamanujan 1 k one_ne_zero = 1 := by
  have hsign : k = (k.natAbs : Int) ∨ k = -(k.natAbs : Int) :=
    (Int.natAbs_eq_iff (a := k) (n := k.natAbs)).mp rfl
  rcases hsign with hpos | hneg
  · rw [hpos, integerFourierRamanujan_natCast,
      finiteFourierRamanujan_eq_totient_of_dvd one_ne_zero (one_dvd _)]
    norm_num
  · rw [hneg, integerFourierRamanujan_neg_natCast,
      finiteFourierRamanujan_eq_totient_of_dvd one_ne_zero (one_dvd _)]
    norm_num

/-- At denominator two the integer Ramanujan character is exactly one on
every even signed integer frequency. -/
theorem integerFourierRamanujan_two_eq_one_of_even
    {k : Int} (hk : Even k) :
    integerFourierRamanujan 2 k (by norm_num) = 1 := by
  have hkabs : 2 ∣ k.natAbs := by
    rcases hk with ⟨j, hj⟩
    rw [hj, ← two_mul, Int.natAbs_mul]
    refine ⟨j.natAbs, ?_⟩
    norm_num
  have hsign : k = (k.natAbs : Int) ∨ k = -(k.natAbs : Int) :=
    (Int.natAbs_eq_iff (a := k) (n := k.natAbs)).mp rfl
  rcases hsign with hpos | hneg
  · rw [hpos, integerFourierRamanujan_natCast,
      finiteFourierRamanujan_eq_totient_of_dvd (by norm_num) hkabs]
    norm_num
  · rw [hneg, integerFourierRamanujan_neg_natCast,
      finiteFourierRamanujan_eq_totient_of_dvd (by norm_num) hkabs]
    norm_num

/-- Exact real-part formula for the literal `q <= 2` kernel on any even
integer shift.  No sign is inferred from the formula. -/
theorem explicitSmallDenominatorSincKernel_even_formula
    (M P R : Nat) (k : Int) (hR : 2 <= R) (hk : Even k) :
    (explicitSmallDenominatorSincKernel M P R k).re =
      explicitEvenSmallKernelReal M P k := by
  unfold explicitEvenSmallKernelReal
  rw [explicitSmallDenominatorSincKernel_eq_one_add_two M P R k hR]
  unfold explicitDenominatorSincTerm
  simp only [denominatorOne, denominatorTwo]
  rw [integerFourierRamanujan_one_eq_one,
    integerFourierRamanujan_two_eq_one_of_even (hk.neg)]
  simp only [one_mul, Complex.add_re, Complex.ofReal_re]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  have hangle :
      2 * Real.pi * (k : Real) *
          ((P : Real) / ((2 : Real) * (M : Real))) =
        Real.pi * (k : Real) * ((P : Real) / (M : Real)) := by
    ring
  rw [hangle]

/-- Every shift occurring in the off-diagonal fiber transport is nonzero.
Thus the two quotients below are never used as a surrogate for a zero-mode
sinc limit. -/
theorem retained_oddOdd_shift_ne_zero
    {M N t : Nat} (ht : t ∈ oddOddOffDiagonalSumCarrier M N) :
    (N : Int) - (t : Int) ≠ 0 := by
  have hne : t ≠ N := (mem_oddOddOffDiagonalSumCarrier_iff M N t).mp ht |>.2.2
  intro hzero
  have : t = N := by omega
  exact hne this

/-- The exact even-shift formula transported through the actual signed Odd-Odd
pair-fiber sum. -/
theorem smallDenominatorOddOddDeficit_eq_explicitEvenKernelSum
    (M P R N : Nat) (hN : Even N) (hR : 2 <= R) :
    smallDenominatorOddOddDeficit M P R N =
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        oddOddPairFiberMass M t *
          explicitEvenSmallKernelReal M P ((N : Int) - (t : Int)) := by
  unfold smallDenominatorOddOddDeficit
  apply Finset.sum_congr rfl
  intro t ht
  rw [explicitSmallDenominatorSincKernel_even_formula M P R
    ((N : Int) - (t : Int)) hR (retained_oddOdd_shift_even hN ht)]

/-- The compensated small core is definitionally the nonnegative diagonal
reserve minus the exact two-sine fiber sum.  This is an identity, not a lower
bound for the core. -/
theorem compensatedSmallDenominatorCore_eq_diagonal_sub_explicitEvenKernelSum
    (M P R N : Nat) (hN : Even N) (hR : 2 <= R) :
    compensatedSmallDenominatorCore M P R N =
      explicitDiagonalOddOddReserve M P R N -
        ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
          oddOddPairFiberMass M t *
            explicitEvenSmallKernelReal M P ((N : Int) - (t : Int)) := by
  unfold compensatedSmallDenominatorCore
  rw [smallDenominatorOddOddDeficit_eq_explicitEvenKernelSum M P R N hN hR]

/-- Exact project-width normalization.  Since `cubicModelScale R = 8*R^2`,
the two phases are displayed with the literal coefficients `16` and `8`. -/
theorem explicitEvenSmallKernelReal_projectWidth
    (M R : Nat) (k : Int) :
    explicitEvenSmallKernelReal M (cubicModelScale R) k =
      Real.sin
          (16 * Real.pi * (k : Real) * (R : Real) ^ 2 /
            (M : Real)) /
          (Real.pi * (k : Real)) +
        Real.sin
          (8 * Real.pi * (k : Real) * (R : Real) ^ 2 /
            (M : Real)) /
          (Real.pi * (k : Real)) := by
  unfold explicitEvenSmallKernelReal cubicModelScale
  push_cast
  have hfirst :
      2 * Real.pi * (k : Real) *
          ((8 * (R : Real) ^ 2) / (M : Real)) =
        16 * Real.pi * (k : Real) * (R : Real) ^ 2 / (M : Real) := by
    ring
  have hsecond :
      Real.pi * (k : Real) *
          ((8 * (R : Real) ^ 2) / (M : Real)) =
        8 * Real.pi * (k : Real) * (R : Real) ^ 2 / (M : Real) := by
    ring
  rw [hfirst, hsecond]

/-- Full actual project normalization of the signed `q <= 2` Odd-Odd deficit
on an even target.  The remaining task is to estimate this literal finite
weighted sine sum together with its diagonal reserve. -/
theorem project_smallDenominatorOddOddDeficit_eq_explicitSineSum
    (M N : Nat) (hN : Even N) (hR : 2 <= oddProjectRadius M) :
    smallDenominatorOddOddDeficit M
        (oddProjectWidth M) (oddProjectRadius M) N =
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        oddOddPairFiberMass M t *
          (Real.sin
              (16 * Real.pi * (((N : Int) - (t : Int)) : Real) *
                (oddProjectRadius M : Real) ^ 2 / (M : Real)) /
              (Real.pi * (((N : Int) - (t : Int)) : Real)) +
            Real.sin
              (8 * Real.pi * (((N : Int) - (t : Int)) : Real) *
                (oddProjectRadius M : Real) ^ 2 / (M : Real)) /
              (Real.pi * (((N : Int) - (t : Int)) : Real))) := by
  rw [smallDenominatorOddOddDeficit_eq_explicitEvenKernelSum M
    (oddProjectWidth M) (oddProjectRadius M) N hN hR]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [show oddProjectWidth M = cubicModelScale (oddProjectRadius M) by rfl,
    explicitEvenSmallKernelReal_projectWidth]
  simp only [Int.cast_sub, Int.cast_natCast]

end GoldbachCircleMethodOddOddEvenSmallKernelFormulaV18673
