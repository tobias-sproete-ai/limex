import GoldbachCircleMethodActualQ3ExplicitPsiSourceMatchV18761
import GoldbachCircleMethodActualQ3ZeroClassExactLogMassV18787
import GoldbachCircleMethodActualQ3OddPrefixExactPsiSplitV18791

/-!
# V1.8.794: exact transfer from the q=3 source to the full psi error

The two reduced residue-class estimates in the cited explicit prime-number
theorem do not by themselves equal the full Chebyshev fluctuation.  The
missing zero residue class is proved here to be exactly the positive powers
of three.  Consequently the full error `psi(x) - x` is bounded by the two
source errors plus one explicit logarithmic prime-power correction.

The published estimate remains an explicit hypothesis.  No source theorem
is imported as an axiom, and no Goldbach conclusion is claimed.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3FullPsiSourceTransferV18794

open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752
open GoldbachCircleMethodActualQ3ExplicitPsiSourceMatchV18761
open GoldbachCircleMethodActualQ3ZeroClassThreePowerSupportV18786
open GoldbachCircleMethodActualQ3ZeroClassExactLogMassV18787
open GoldbachCircleMethodActualQ3OddPrefixExactPsiSplitV18791
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719

/-- The full zero residue class contains no even contribution: every
nonzero von-Mangoldt term divisible by three is a positive odd power of
three. -/
theorem fullLambdaQ3ResidueMass_zero_eq_oddMass
    (x : Nat) :
    fullLambdaQ3ResidueMass x (0 : ZMod 3) =
      oddLambdaQ3ResidueMass x x.succ (0 : ZMod 3) := by
  unfold fullLambdaQ3ResidueMass oddLambdaQ3ResidueMass oddCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hmod : (a : ZMod 3) = 0
  · by_cases hodd : Odd a
    · simp [hmod, hodd, Finset.mem_range.mp ha]
    · have heven : Even a := Nat.not_odd_iff_even.mp hodd
      have hlam : ArithmeticFunction.vonMangoldt a = 0 := by
        by_contra hne
        obtain ⟨k, hk, hak, _hweight⟩ :=
          vonMangoldt_eq_log_three_of_q3_zero hmod hne
        have hpowOdd : Odd (3 ^ k) := Odd.pow ⟨1, by norm_num⟩
        exact hodd (hak.symm ▸ hpowOdd)
      simp [hmod, hodd, hlam]
  · simp [hmod]

/-- Exact closed form of the zero residue mass in the full source
convention. -/
theorem fullLambdaQ3ResidueMass_zero_eq_log_count
    (x : Nat) :
    fullLambdaQ3ResidueMass x (0 : ZMod 3) =
      (Nat.log 3 x) • (Real.log 3 : Complex) := by
  rw [fullLambdaQ3ResidueMass_zero_eq_oddMass]
  rw [oddLambdaQ3ResidueMass_zero_eq_log_count]
  congr 2
  omega

/-- Exact partition of the full Chebyshev mass into the three residue
classes modulo three. -/
theorem psi_eq_sum_fullLambdaQ3ResidueMass
    (x : Nat) :
    (Chebyshev.psi (x : Real) : Complex) =
      fullLambdaQ3ResidueMass x 0 +
        fullLambdaQ3ResidueMass x 1 +
        fullLambdaQ3ResidueMass x 2 := by
  have hpsi := lambdaSum_range_succ_eq_psi x
  calc
    (Chebyshev.psi (x : Real) : Complex) =
        ((∑ a ∈ Finset.range x.succ,
          ArithmeticFunction.vonMangoldt a : Real) : Complex) := by
            rw [hpsi]
    _ = ∑ a ∈ Finset.range x.succ,
          (ArithmeticFunction.vonMangoldt a : Complex) := by
            rw [Complex.ofReal_sum]
    _ = fullLambdaQ3ResidueMass x 0 +
          fullLambdaQ3ResidueMass x 1 +
          fullLambdaQ3ResidueMass x 2 := by
      unfold fullLambdaQ3ResidueMass
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      have hcases : (a : ZMod 3) = 0 ∨
          (a : ZMod 3) = 1 ∨ (a : ZMod 3) = 2 := by
        have hall (z : ZMod 3) : z = 0 ∨ z = 1 ∨ z = 2 := by
          fin_cases z
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        exact hall (a : ZMod 3)
      rcases hcases with h0 | h1 | h2
      · have h01 : (a : ZMod 3) ≠ 1 := by
          intro h
          exact (by decide : (0 : ZMod 3) ≠ 1) (h0.symm.trans h)
        have h02 : (a : ZMod 3) ≠ 2 := by
          intro h
          exact (by decide : (0 : ZMod 3) ≠ 2) (h0.symm.trans h)
        rw [if_pos h0, if_neg h01, if_neg h02]
        ring
      · have h10 : (a : ZMod 3) ≠ 0 := by
          intro h
          exact (by decide : (1 : ZMod 3) ≠ 0) (h1.symm.trans h)
        have h12 : (a : ZMod 3) ≠ 2 := by
          intro h
          exact (by decide : (1 : ZMod 3) ≠ 2) (h1.symm.trans h)
        rw [if_neg h10, if_pos h1, if_neg h12]
        ring
      · have h20 : (a : ZMod 3) ≠ 0 := by
          intro h
          exact (by decide : (2 : ZMod 3) ≠ 0) (h2.symm.trans h)
        have h21 : (a : ZMod 3) ≠ 1 := by
          intro h
          exact (by decide : (2 : ZMod 3) ≠ 1) (h2.symm.trans h)
        rw [if_neg h20, if_neg h21, if_pos h2]
        ring

/-- Exact decomposition of the full Chebyshev fluctuation into the two
reduced-class source errors and the explicit powers-of-three correction. -/
theorem psi_sub_linear_eq_sourceErrors_add_threePowers
    (x : Nat) :
    ((Chebyshev.psi (x : Real) - (x : Real) : Real) : Complex) =
      (fullLambdaQ3ResidueMass x 1 - ((x : Real) / 2 : Complex)) +
      (fullLambdaQ3ResidueMass x 2 - ((x : Real) / 2 : Complex)) +
      (Nat.log 3 x) • (Real.log 3 : Complex) := by
  rw [Complex.ofReal_sub]
  rw [psi_eq_sum_fullLambdaQ3ResidueMass,
    fullLambdaQ3ResidueMass_zero_eq_log_count]
  push_cast
  ring

/-- Source-valid full-psi envelope.  The price of passing from two reduced
classes to the full Chebyshev function is exactly the logarithmic zero-class
term. -/
theorem norm_psi_sub_linear_lt_sourceEnvelope
    (x : Nat) (C : Real)
    (hSource : ExplicitPsiQ3ResidueBoundAt x C) :
    ‖((Chebyshev.psi (x : Real) - (x : Real) : Real) : Complex)‖ <
      2 * (C * (x : Real) / Real.log (x : Real)) +
        Nat.log 3 x * Real.log 3 := by
  rw [psi_sub_linear_eq_sourceErrors_add_threePowers]
  have h1 := hSource (1 : ZMod 3) (Or.inl rfl)
  have h2 := hSource (2 : ZMod 3) (Or.inr rfl)
  have h3 :
      ‖(Nat.log 3 x) • (Real.log 3 : Complex)‖ =
        Nat.log 3 x * Real.log 3 := by
    have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    rw [nsmul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog]
    norm_num
  calc
    ‖(fullLambdaQ3ResidueMass x 1 - ((x : Real) / 2 : Complex)) +
        (fullLambdaQ3ResidueMass x 2 - ((x : Real) / 2 : Complex)) +
        (Nat.log 3 x) • (Real.log 3 : Complex)‖ ≤
      ‖fullLambdaQ3ResidueMass x 1 - ((x : Real) / 2 : Complex)‖ +
      ‖fullLambdaQ3ResidueMass x 2 - ((x : Real) / 2 : Complex)‖ +
      ‖(Nat.log 3 x) • (Real.log 3 : Complex)‖ := by
        exact (norm_add_le _ _).trans
          (by gcongr; exact norm_add_le _ _)
    _ < 2 * (C * (x : Real) / Real.log (x : Real)) +
        Nat.log 3 x * Real.log 3 := by
      rw [h3]
      linarith

end GoldbachCircleMethodActualQ3FullPsiSourceTransferV18794
