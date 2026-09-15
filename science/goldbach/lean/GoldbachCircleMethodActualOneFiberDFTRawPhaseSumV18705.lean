import GoldbachCircleMethodActualOneFiberKernelCrossSpectralIdentityV18704

/-!
# V1.8.705: raw phase-sum exposure of the actual one-fiber DFT

This append-only module removes the residue-bucket opacity from V1.8.704.
The DFT of the actual signed residue aggregation is exactly the finite phase
sum of the literal V1.8.698 half-weight over its original range.

No weight replacement, absolute value, triangle inequality, LCM lift,
smallness estimate, asymptotic claim, moment bound, or Goldbach conclusion is
introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodActualOneFiberDFTRawPhaseSumV18705

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698
open GoldbachCircleMethodActualOneFiberKernelCrossSpectralIdentityV18704

/-- Literal finite phase sum of the unchanged actual one-fiber half-weight. -/
noncomputable def selectedPairOneFiberRawPhaseSum
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (ξ : ZMod q.val.val) : Complex :=
  ∑ a ∈ Finset.range M.succ,
    ZMod.stdAddChar (-((a : ZMod q.val.val) * ξ)) *
      (selectedPairOneFiberHalfWeight M q n a : Complex)

/-- Exact bucket removal: the actual residue DFT equals the raw weighted
phase sum, with the inherited DFT sign convention unchanged. -/
theorem selectedPairOneFiberResidueDFT_eq_rawPhaseSum
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (ξ : ZMod q.val.val) :
    selectedPairOneFiberResidueDFT M q n ξ =
      selectedPairOneFiberRawPhaseSum M q n ξ := by
  unfold selectedPairOneFiberResidueDFT selectedPairOneFiberRawPhaseSum
    selectedPairOneFiberSignedResidueWeight
  simp only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero]
  change
    ZMod.dft (fun x : ZMod q.val.val =>
      ∑ a ∈ Finset.range M.succ,
        if (a : ZMod q.val.val) = x then
          (selectedPairOneFiberHalfWeight M q n a : Complex)
        else 0) ξ = _
  rw [show ZMod.dft (fun x : ZMod q.val.val =>
      ∑ a ∈ Finset.range M.succ,
        if (a : ZMod q.val.val) = x then
          (selectedPairOneFiberHalfWeight M q n a : Complex)
        else 0) ξ =
    ∑ x : ZMod q.val.val,
      ZMod.stdAddChar (-(x * ξ)) *
        (∑ a ∈ Finset.range M.succ,
          if (a : ZMod q.val.val) = x then
            (selectedPairOneFiberHalfWeight M q n a : Complex)
          else 0) by rfl]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  simp

/-- V1.8.704 cross-spectrum rewritten entirely in the literal raw phase
sums. -/
theorem sum_star_rawPhaseSum_mul_eq_modulus_mul_kernel
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n m : Nat) :
    (∑ ξ : ZMod q.val.val,
      star (selectedPairOneFiberRawPhaseSum M q n ξ) *
        selectedPairOneFiberRawPhaseSum M q m ξ) =
      (q.val.val : Complex) *
        (GoldbachCircleMethodOneDimensionalAutocorrelationContractionV18700.selectedPairOneFiberResidueKernel
          M q n m : Complex) := by
  simpa only [← selectedPairOneFiberResidueDFT_eq_rawPhaseSum] using
    GoldbachCircleMethodActualOneFiberKernelCrossSpectralIdentityV18704.sum_star_residueDFT_mul_eq_modulus_mul_kernel
      M q n m

end GoldbachCircleMethodActualOneFiberDFTRawPhaseSumV18705
