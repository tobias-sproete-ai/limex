import GoldbachCircleMethodActualQ3ZeroClassThreePowerSupportV18786

/-!
# V1.8.787: exact logarithmic mass of the q=3 zero class

V1.8.786 identifies every contributing zero-class term with a positive power
of three.  This module completes the finite counting step: the literal
zero-class residue mass is exactly the number of admissible exponents times
`log 3`, hence grows only logarithmically in the effective cutoff.

No estimate for the full-prefix selector convolution is supplied, and no
Goldbach conclusion is claimed.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3ZeroClassExactLogMassV18787

open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3ZeroClassThreePowerSupportV18786

/-- Restricting the literal residue sum to its actual nonzero support changes
nothing. -/
theorem oddLambdaQ3ResidueMass_zero_eq_support_sum (M B : Nat) :
    oddLambdaQ3ResidueMass M B (0 : ZMod 3) =
      ∑ a ∈ oddLambdaQ3ZeroSupport M B,
        (ArithmeticFunction.vonMangoldt a : Complex) := by
  unfold oddLambdaQ3ResidueMass oddLambdaQ3ZeroSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hbase : a < B ∧ (a : ZMod 3) = 0
  · rw [if_pos hbase]
    by_cases hpp : IsPrimePow a
    · rw [if_pos ⟨hbase.1, hbase.2, hpp⟩]
    · rw [if_neg (by tauto)]
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
      norm_num
  · rw [if_neg hbase]
    rw [if_neg (by tauto)]

/-- Every term on the actual zero support has the same exact weight. -/
theorem zeroSupport_vonMangoldt_eq_log_three
    {M B a : Nat} (ha : a ∈ oddLambdaQ3ZeroSupport M B) :
    ArithmeticFunction.vonMangoldt a = Real.log 3 := by
  rw [oddLambdaQ3ZeroSupport, Finset.mem_filter] at ha
  rcases ha with ⟨_haCarrier, _haB, haMod, haPP⟩
  have hLam : ArithmeticFunction.vonMangoldt a ≠ 0 :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr haPP
  exact (vonMangoldt_eq_log_three_of_q3_zero haMod hLam).choose_spec.2.2

/-- Cardinality of the zero support is exactly the base-three logarithm of
the effective integer cutoff. -/
theorem card_oddLambdaQ3ZeroSupport (M B : Nat) :
    (oddLambdaQ3ZeroSupport M B).card =
      Nat.log 3 (min M (B - 1)) := by
  rw [zeroSupport_eq_image_exponents]
  rw [Finset.card_image_of_injective _
    (Nat.pow_right_injective (by norm_num : 2 ≤ 3))]
  unfold oddLambdaQ3ZeroExponentCarrier
  rw [Nat.card_Icc]
  omega

/-- Exact closed form of the literal q=3 zero-class mass. -/
theorem oddLambdaQ3ResidueMass_zero_eq_log_count (M B : Nat) :
    oddLambdaQ3ResidueMass M B (0 : ZMod 3) =
      (Nat.log 3 (min M (B - 1))) • (Real.log 3 : Complex) := by
  rw [oddLambdaQ3ResidueMass_zero_eq_support_sum]
  calc
    (∑ a ∈ oddLambdaQ3ZeroSupport M B,
        (ArithmeticFunction.vonMangoldt a : Complex)) =
      ∑ _a ∈ oddLambdaQ3ZeroSupport M B, (Real.log 3 : Complex) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [zeroSupport_vonMangoldt_eq_log_three ha]
    _ = (oddLambdaQ3ZeroSupport M B).card • (Real.log 3 : Complex) := by
      rw [Finset.sum_const]
    _ = (Nat.log 3 (min M (B - 1))) • (Real.log 3 : Complex) := by
      rw [card_oddLambdaQ3ZeroSupport]

/-- Corresponding exact norm formula. -/
theorem norm_oddLambdaQ3ResidueMass_zero_eq (M B : Nat) :
    ‖oddLambdaQ3ResidueMass M B (0 : ZMod 3)‖ =
      Nat.log 3 (min M (B - 1)) * Real.log 3 := by
  rw [oddLambdaQ3ResidueMass_zero_eq_log_count]
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hnorm : ‖(Real.log (3 : Real) : Complex)‖ = Real.log 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  rw [nsmul_eq_mul, norm_mul, hnorm]
  norm_num

end GoldbachCircleMethodActualQ3ZeroClassExactLogMassV18787
