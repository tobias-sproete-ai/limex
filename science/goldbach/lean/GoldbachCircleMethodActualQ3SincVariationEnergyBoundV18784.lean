import GoldbachCircleMethodActualQ3SignedProfileEnergyGateV18783
import GoldbachCircleMethodSharpSourceSincVariationV18721
import GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
import GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717

/-!
# V1.8.784: actual q=3 Sinc-variation energy bound

The first factor in the V1.8.783 energy product is discharged using the
already kernel-checked sharp total variation of the literal two-radius Sinc
weight.  The real-coordinate square energy is at most the square of that
total variation and hence at most `actualQ3VariationScale ^ 2`.

The only remaining quantitative input in the resulting positivity criterion
is the actual centered q=3 profile energy.  No bound for that arithmetic
energy is asserted here.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualQ3SincVariationEnergyBoundV18784

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSharpSourceSincVariationV18721
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
open GoldbachCircleMethodActualQ3SignedProfileVariationCorrelationV18777
open GoldbachCircleMethodActualQ3SignedProfileEnergyGateV18783

/-- For a finite nonnegative family, its square energy is bounded by the
square of its L1 mass. -/
theorem sum_sq_le_sq_sum_of_nonneg
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → Real)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i ^ 2) ≤ (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, f i := by
        exact Finset.sum_nonneg hfs
      have hih := ih hfs
      nlinarith

/-- The exact real Sinc-variation energy is bounded by the square of the
project's sharp harmonic total-variation scale. -/
theorem actualQ3SignedSincVariationEnergy_le_variationScale_sq
    {M n : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M) :
    actualQ3SignedSincVariationEnergy M q n ≤
      actualQ3VariationScale M q ^ 2 := by
  have hReNorm :
      actualQ3SignedSincVariationEnergy M q n ≤
        ∑ t ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n t‖ ^ 2 := by
    unfold actualQ3SignedSincVariationEnergy actualQ3SignedSincVariation
    apply Finset.sum_le_sum
    intro t _ht
    have habs :
        |(selectedPairSourceCoordinateSincVariation M q n t).re| ≤
          ‖selectedPairSourceCoordinateSincVariation M q n t‖ :=
      Complex.abs_re_le_norm _
    have hlower :
        -‖selectedPairSourceCoordinateSincVariation M q n t‖ ≤
          (selectedPairSourceCoordinateSincVariation M q n t).re :=
      (abs_le.mp habs).1
    have hupper :
        (selectedPairSourceCoordinateSincVariation M q n t).re ≤
          ‖selectedPairSourceCoordinateSincVariation M q n t‖ :=
      (abs_le.mp habs).2
    have hleft : 0 ≤
        ‖selectedPairSourceCoordinateSincVariation M q n t‖ -
          (selectedPairSourceCoordinateSincVariation M q n t).re := by
      linarith
    have hright : 0 ≤
        ‖selectedPairSourceCoordinateSincVariation M q n t‖ +
          (selectedPairSourceCoordinateSincVariation M q n t).re := by
      linarith
    nlinarith [mul_nonneg hleft hright]
  have hNormSq :
      (∑ t ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n t‖ ^ 2) ≤
        (∑ t ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n t‖) ^ 2 := by
    exact sum_sq_le_sq_sum_of_nonneg (Finset.range M)
      (fun t => ‖selectedPairSourceCoordinateSincVariation M q n t‖)
      (by intro t _ht; positivity)
  have hVar :=
    sum_selectedPairSourceCoordinateSincVariation_norm_le_harmonic
      M hM q n hn
  have hsumNonneg : 0 ≤
      ∑ t ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n t‖ := by
    positivity
  have hVar' :
      (∑ t ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n t‖) ≤
          actualQ3VariationScale M q := by
    simpa [actualQ3VariationScale] using hVar
  have hscaleNonneg : 0 ≤ actualQ3VariationScale M q :=
    hsumNonneg.trans hVar'
  calc
    actualQ3SignedSincVariationEnergy M q n ≤
        ∑ t ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n t‖ ^ 2 := hReNorm
    _ ≤ (∑ t ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n t‖) ^ 2 := hNormSq
    _ ≤ actualQ3VariationScale M q ^ 2 := by
      nlinarith

/-- After discharging the Sinc energy, strict domination of the actual
profile energy alone implies positivity of the complete actual reserve. -/
theorem actualModelQ3CompositeReserve_pos_of_profileEnergy
    {M R n : Nat} {P : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M)
    (hBase : 0 < actualQ3ResidueSelectorBaseReserve M R n P q)
    (hProfileEnergy :
      actualQ3VariationScale M q ^ 2 *
          actualQ3CenteredResidueSelectorRealProfileEnergy M n <
        actualQ3ResidueSelectorBaseReserve M R n P q ^ 2) :
    0 < actualModelQ3PreLoweringCompositeReserve M R n P q := by
  have hSinc := actualQ3SignedSincVariationEnergy_le_variationScale_sq
    hM q hn
  have hProfileNonneg :=
    actualQ3CenteredResidueSelectorRealProfileEnergy_nonneg M n
  have hProduct :
      actualQ3SignedSincVariationEnergy M q n *
          actualQ3CenteredResidueSelectorRealProfileEnergy M n <
        actualQ3ResidueSelectorBaseReserve M R n P q ^ 2 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hSinc hProfileNonneg) hProfileEnergy
  exact actualModelQ3CompositeReserve_pos_of_energy_product_lt_base_sq
    M R n P q hBase hProduct

end GoldbachCircleMethodActualQ3SincVariationEnergyBoundV18784
