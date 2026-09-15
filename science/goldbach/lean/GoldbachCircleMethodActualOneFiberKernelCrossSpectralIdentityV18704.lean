import GoldbachCircleMethodActualOneFiberKernelWeightedLagExpansionV18703
import GoldbachCircleMethodSameDenominatorHermitianPlancherelV18579

/-!
# V1.8.704: exact cross-spectral identity for the actual one-fiber kernel

This append-only module applies the already kernelised finite Hermitian
Plancherel theorem to the literal V1.8.698 signed residue weight.  It gives an
exact frequency-space representation of one V1.8.700 residue kernel.

The weight is not replaced by an unweighted von-Mangoldt exponential sum.
No absolute value, triangle inequality, global LCM, decay estimate, spectral
smallness, moment bound, or Goldbach conclusion is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodActualOneFiberKernelCrossSpectralIdentityV18704

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698
open GoldbachCircleMethodOneDimensionalAutocorrelationContractionV18700
open GoldbachCircleMethodActualOneFiberKernelWeightedLagExpansionV18703
open GoldbachCircleMethodSameDenominatorHermitianPlancherelV18579

/-- Unnormalised DFT of the actual signed one-fiber residue weight. -/
noncomputable def selectedPairOneFiberResidueDFT
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (ξ : ZMod q.val.val) : Complex :=
  ZMod.dft (fun x : ZMod q.val.val =>
    (selectedPairOneFiberSignedResidueWeight M q n x : Complex)) ξ

/-- Exact cross-spectral Plancherel identity for the unchanged project
weight.  The normalising factor is kept multiplicatively, so no division or
nonzero side condition is hidden in the statement. -/
theorem sum_star_residueDFT_mul_eq_modulus_mul_kernel
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n m : Nat) :
    (∑ ξ : ZMod q.val.val,
      star (selectedPairOneFiberResidueDFT M q n ξ) *
        selectedPairOneFiberResidueDFT M q m ξ) =
      (q.val.val : Complex) *
        (selectedPairOneFiberResidueKernel M q n m : Complex) := by
  unfold selectedPairOneFiberResidueDFT
  rw [dft_hermitian_plancherel]
  unfold selectedPairOneFiberResidueKernel
  congr 1
  simp

/-- Diagonal specialization: the Hermitian spectral square is exactly the
modulus times the actual spatial square energy. -/
theorem sum_star_residueDFT_mul_self_eq_modulus_mul_diagonalKernel
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    (∑ ξ : ZMod q.val.val,
      star (selectedPairOneFiberResidueDFT M q n ξ) *
        selectedPairOneFiberResidueDFT M q n ξ) =
      (q.val.val : Complex) *
        (selectedPairOneFiberResidueKernel M q n n : Complex) :=
  sum_star_residueDFT_mul_eq_modulus_mul_kernel M q n n

end GoldbachCircleMethodActualOneFiberKernelCrossSpectralIdentityV18704
