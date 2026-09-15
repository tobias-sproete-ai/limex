import GoldbachPurePrimeAdequacyV15
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Von Mangoldt to pure-prime decomposition, V1.6

This module proves only the exact finite decomposition and nonnegativity of the
complementary defect. It does not prove a quantitative defect bound, main-term
dominance, or binary Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace GoldbachVonMangoldtDecompositionV16

open GoldbachPurePrimeAdequacyV15

/-- The ordered finite von Mangoldt convolution at `N`. -/
noncomputable def vonMangoldtPairSum (N : Nat) : Real :=
  ∑ n ∈ Finset.range N,
    ArithmeticFunction.vonMangoldt n *
      ArithmeticFunction.vonMangoldt (N - n)

/-- The complementary part of the von Mangoldt convolution after removing
the exact pure-prime support. Nonzero terms on this support necessarily
involve at least one higher prime power, but that support characterization is
kept as a separate future theorem. -/
noncomputable def primePowerDefect (N : Nat) : Real :=
  ∑ n ∈ (Finset.range N).filter
      (fun n => ¬ (Nat.Prime n ∧ Nat.Prime (N - n))),
    ArithmeticFunction.vonMangoldt n *
      ArithmeticFunction.vonMangoldt (N - n)

/-- On the exact pure-prime support, the von Mangoldt weight equals the
logarithmic weight used by the Stage 1 fibre. -/
theorem vonMangoldtWeight_eq_purePrimeWeight
    {N n : Nat} (hn : n ∈ goldbachPairs N) :
    ArithmeticFunction.vonMangoldt n *
        ArithmeticFunction.vonMangoldt (N - n) =
      purePrimeWeight N n := by
  have hData := mem_goldbachPairs_iff.mp hn
  rw [ArithmeticFunction.vonMangoldt_apply_prime hData.2.1,
    ArithmeticFunction.vonMangoldt_apply_prime hData.2.2]
  rfl

/-- The prime-prime part of the von Mangoldt convolution is definitionally
the Stage 1 pure-prime fibre. -/
theorem primePart_eq_purePrimeSum (N : Nat) :
    (∑ n ∈ (Finset.range N).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (N - n)),
      ArithmeticFunction.vonMangoldt n *
        ArithmeticFunction.vonMangoldt (N - n)) =
      purePrimeSum N := by
  classical
  rw [purePrimeSum, goldbachPairs]
  apply Finset.sum_congr rfl
  intro n hn
  exact vonMangoldtWeight_eq_purePrimeWeight hn

/-- Exact finite partition: the von Mangoldt convolution is the pure-prime
fibre plus the complementary prime-power defect. -/
theorem vonMangoldtPairSum_eq_purePrimeSum_add_primePowerDefect (N : Nat) :
    vonMangoldtPairSum N = purePrimeSum N + primePowerDefect N := by
  classical
  rw [vonMangoldtPairSum, primePowerDefect]
  rw [← primePart_eq_purePrimeSum N]
  exact (Finset.sum_filter_add_sum_filter_not
    (Finset.range N)
    (fun n => Nat.Prime n ∧ Nat.Prime (N - n))
    (fun n => ArithmeticFunction.vonMangoldt n *
      ArithmeticFunction.vonMangoldt (N - n))).symm

/-- Every term of the complementary defect is nonnegative. -/
theorem primePowerDefect_nonneg (N : Nat) :
    0 ≤ primePowerDefect N := by
  classical
  simp only [primePowerDefect]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      ArithmeticFunction.vonMangoldt_nonneg

/-- A nonzero summand in the complementary defect has von Mangoldt support on
both coordinates and is not a pure-prime pair. This is the exact formal
support statement proved at this stage; extracting explicit exponents is a
separate obligation. -/
theorem nonzero_defect_term_has_nonpure_primePower_support
    {N n : Nat}
    (hn : n ∈ (Finset.range N).filter
      (fun n => ¬ (Nat.Prime n ∧ Nat.Prime (N - n))))
    (hWeight : ArithmeticFunction.vonMangoldt n *
      ArithmeticFunction.vonMangoldt (N - n) ≠ 0) :
    IsPrimePow n ∧ IsPrimePow (N - n) ∧
      ¬ (Nat.Prime n ∧ Nat.Prime (N - n)) := by
  have hNotPure := (Finset.mem_filter.mp hn).2
  have hLeft : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro hZero
    apply hWeight
    rw [hZero, zero_mul]
  have hRight : ArithmeticFunction.vonMangoldt (N - n) ≠ 0 := by
    intro hZero
    apply hWeight
    rw [hZero, mul_zero]
  exact ⟨ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLeft,
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hRight,
    hNotPure⟩

/-- The pure-prime fibre is bounded above by the full von Mangoldt
convolution. -/
theorem purePrimeSum_le_vonMangoldtPairSum (N : Nat) :
    purePrimeSum N ≤ vonMangoldtPairSum N := by
  rw [vonMangoldtPairSum_eq_purePrimeSum_add_primePowerDefect]
  exact le_add_of_nonneg_right (primePowerDefect_nonneg N)

end GoldbachVonMangoldtDecompositionV16

