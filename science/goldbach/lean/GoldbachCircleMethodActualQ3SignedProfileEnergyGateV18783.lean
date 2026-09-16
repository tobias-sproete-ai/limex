import GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777
import GoldbachCircleMethodFullDenominatorFourClassPartitionV18688

/-!
# V1.8.783: actual q=3 signed-profile energy gate

The exact signed correlation isolated in V1.8.777 is now controlled without a
pointwise profile supremum.  Finite Cauchy--Schwarz exposes two literal
actual-source energies: the project Sinc-variation energy and the centered
q=3 residue-selector profile energy.

This is a genuine alternative sufficient condition.  If their product is
strictly smaller than the square of the exact positive base reserve, the
actual composite reserve is positive.  No estimate of either energy is
asserted here, and no Goldbach conclusion follows from the interface alone.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3SignedProfileEnergyGateV18783

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
open GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777

/-- Exact finite energy of the real project Sinc variation. -/
noncomputable def actualQ3SignedSincVariationEnergy
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Real :=
  ∑ t ∈ Finset.range M,
    actualQ3SignedSincVariation M q n t ^ 2

/-- Exact finite energy of the centered real q=3 profile on the same Abel
carrier. -/
noncomputable def actualQ3CenteredResidueSelectorRealProfileEnergy
    (M n : Nat) : Real :=
  ∑ t ∈ Finset.range M,
    actualQ3CenteredResidueSelectorRealProfile M n (t + 1) ^ 2

theorem actualQ3SignedSincVariationEnergy_nonneg
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    0 ≤ actualQ3SignedSincVariationEnergy M q n := by
  unfold actualQ3SignedSincVariationEnergy
  positivity

theorem actualQ3CenteredResidueSelectorRealProfileEnergy_nonneg
    (M n : Nat) :
    0 ≤ actualQ3CenteredResidueSelectorRealProfileEnergy M n := by
  unfold actualQ3CenteredResidueSelectorRealProfileEnergy
  positivity

/-- Finite real Cauchy--Schwarz on the exact actual-source correlation. -/
theorem actualQ3SignedProfileVariationCorrelation_sq_le_energy_product
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    actualQ3SignedProfileVariationCorrelation M q n ^ 2 ≤
      actualQ3SignedSincVariationEnergy M q n *
        actualQ3CenteredResidueSelectorRealProfileEnergy M n := by
  unfold actualQ3SignedProfileVariationCorrelation
    actualQ3SignedSincVariationEnergy
    actualQ3CenteredResidueSelectorRealProfileEnergy
  exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M)
    (fun t => actualQ3SignedSincVariation M q n t)
    (fun t => actualQ3CenteredResidueSelectorRealProfile M n (t + 1))

/-- A strict energy product below the square of a positive exact base reserve
forces positivity of the complete actual q=3 composite reserve. -/
theorem actualModelQ3CompositeReserve_pos_of_energy_product_lt_base_sq
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M))
    (hBase : 0 < actualQ3ResidueSelectorBaseReserve M R n P q)
    (hEnergy :
      actualQ3SignedSincVariationEnergy M q n *
          actualQ3CenteredResidueSelectorRealProfileEnergy M n <
        actualQ3ResidueSelectorBaseReserve M R n P q ^ 2) :
    0 < actualModelQ3PreLoweringCompositeReserve M R n P q := by
  have hCS :=
    actualQ3SignedProfileVariationCorrelation_sq_le_energy_product M q n
  have hCorrSq :
      actualQ3SignedProfileVariationCorrelation M q n ^ 2 <
        actualQ3ResidueSelectorBaseReserve M R n P q ^ 2 :=
    lt_of_le_of_lt hCS hEnergy
  have hCorr :
      actualQ3SignedProfileVariationCorrelation M q n <
        actualQ3ResidueSelectorBaseReserve M R n P q := by
    nlinarith
  rw [actualModelQ3CompositeReserve_eq_base_sub_signedCorrelation]
  linarith

end GoldbachCircleMethodActualQ3SignedProfileEnergyGateV18783
