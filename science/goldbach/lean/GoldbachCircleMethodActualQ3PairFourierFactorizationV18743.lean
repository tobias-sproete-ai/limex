import GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742

/-!
# V1.8.743: exact one-variable Fourier factorization of the actual q=3 endpoint

V1.8.742 pulls the complete raw q=3 half-target transform back to the literal
odd--odd Lambda-pair box.  This append-only successor factors that rectangular
pair transform exactly into one-variable additive Fourier modes modulo three.

The factorization is finite and sign-sensitive.  It replaces the rejected
absolute-mass route by the actual arithmetic mode that a fixed-modulus prime
distribution estimate may control.  It does not assume or prove that this
mode is small.

No prime number theorem in progressions, incomplete-prefix estimate,
minor-arc absorption, exceptional-set result, or Goldbach conclusion is
proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3PairFourierFactorizationV18743

open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742

/-- One genuine one-coordinate additive Fourier mode of the odd von-Mangoldt
mass modulo three. -/
noncomputable def oddLambdaQ3Mode (M : Nat) (xi : ZMod 3) : Complex :=
  ∑ a ∈ oddCarrier M,
    (ArithmeticFunction.vonMangoldt a : Complex) *
      ZMod.stdAddChar ((a : ZMod 3) * xi)

/-- One pair-box Fourier mode before the sum over unit frequencies. -/
noncomputable def actualQ3PairMode
    (M n : Nat) (xi : ZMod 3) : Complex :=
  ∑ ab ∈ actualOddOddPairCarrier M,
    (lambdaPairWeight ab : Complex) *
      ZMod.stdAddChar
        (((((ab.1 + ab.2 : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3) * xi)

/-- The pair phase splits exactly into the target phase and two coordinate
phases. -/
theorem q3PairPhase_factor (n a b : Nat) (xi : ZMod 3) :
    ZMod.stdAddChar
        (((((a + b : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3) * xi) =
      ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * xi) *
        ZMod.stdAddChar ((a : ZMod 3) * xi) *
        ZMod.stdAddChar ((b : ZMod 3) * xi) := by
  have harg :
      (((((a + b : Nat) : Int) - 2 * (n : Int) : Int) : ZMod 3) * xi) =
        (((-2 * (n : Int) : Int) : ZMod 3) * xi) +
          ((a : ZMod 3) * xi) + ((b : ZMod 3) * xi) := by
    push_cast
    ring
  rw [harg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

/-- Each rectangular pair mode is the target phase times the square of one
actual odd-Lambda mode. -/
theorem actualQ3PairMode_eq_targetPhase_mul_mode_sq
    (M n : Nat) (xi : ZMod 3) :
    actualQ3PairMode M n xi =
      ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * xi) *
        (oddLambdaQ3Mode M xi) ^ 2 := by
  unfold actualQ3PairMode actualOddOddPairCarrier lambdaPairWeight
    oddLambdaQ3Mode
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simp_rw [Complex.ofReal_mul, q3PairPhase_factor]
  rw [pow_two]
  calc
    (∑ a ∈ oddCarrier M, ∑ b ∈ oddCarrier M,
        ((ArithmeticFunction.vonMangoldt a : Complex) *
          (ArithmeticFunction.vonMangoldt b : Complex)) *
          (ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * xi) *
            ZMod.stdAddChar ((a : ZMod 3) * xi) *
            ZMod.stdAddChar ((b : ZMod 3) * xi))) =
      ∑ a ∈ oddCarrier M,
        ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * xi) *
          ((ArithmeticFunction.vonMangoldt a : Complex) *
            ZMod.stdAddChar ((a : ZMod 3) * xi)) *
          (∑ b ∈ oddCarrier M,
            (ArithmeticFunction.vonMangoldt b : Complex) *
              ZMod.stdAddChar ((b : ZMod 3) * xi)) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        ring
    _ = ZMod.stdAddChar
          (((-2 * (n : Int) : Int) : ZMod 3) * xi) *
      ((∑ a ∈ oddCarrier M,
            (ArithmeticFunction.vonMangoldt a : Complex) *
              ZMod.stdAddChar ((a : ZMod 3) * xi)) *
          (∑ b ∈ oddCarrier M,
            (ArithmeticFunction.vonMangoldt b : Complex) *
              ZMod.stdAddChar ((b : ZMod 3) * xi))) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring

/-- The raw Ramanujan pair transform is exactly the sum of the two unit
frequency pair modes. -/
theorem actualQ3RawPairTransform_eq_sum_unit_pairModes (M n : Nat) :
    actualQ3RawPairTransform M n =
      ∑ xi : ZMod 3,
        if IsUnit xi then actualQ3PairMode M n xi else 0 := by
  unfold actualQ3RawPairTransform actualQ3PairMode unitCharacterSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xi _hxi
  by_cases hunit : IsUnit xi
  · simp only [hunit, if_true]
  · simp only [hunit, if_false, mul_zero, Finset.sum_const_zero]

/-- Final exact source-bound q=3 factorization.  The only nonconstant
arithmetic objects are the genuine one-variable odd-Lambda modes. -/
theorem actualQ3RawPairTransform_eq_sum_unit_modeSquares (M n : Nat) :
    actualQ3RawPairTransform M n =
      ∑ xi : ZMod 3,
        if IsUnit xi then
          ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * xi) *
            (oddLambdaQ3Mode M xi) ^ 2
        else 0 := by
  rw [actualQ3RawPairTransform_eq_sum_unit_pairModes]
  apply Finset.sum_congr rfl
  intro xi _hxi
  by_cases hunit : IsUnit xi
  · simp only [hunit, if_true]
    rw [actualQ3PairMode_eq_targetPhase_mul_mode_sq]
  · simp only [hunit, if_false]

end GoldbachCircleMethodActualQ3PairFourierFactorizationV18743
