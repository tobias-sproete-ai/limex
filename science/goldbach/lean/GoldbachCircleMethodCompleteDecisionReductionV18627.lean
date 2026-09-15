import GoldbachCircleMethodNegativePartSubunitGateV18626

/-!
# V1.8.627: complete conditional decision reduction

This module combines the exact sign-sensitive block gate with an explicit finite
base verification. It proves the whole frozen strong Goldbach target if, and only
if as hypotheses here, every sufficiently large doubled block has the Major
reserve and a negative-part moment below `M^2/784`.

The analytic hypotheses and the finite base verification are not supplied.
`proof_status = NO_PROOF`.
-/
set_option autoImplicit false
open scoped Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodExceptionalTransferV1823
open GoldbachCircleMethodNegativePartSubunitGateV18626
open GoldbachCircleMethodSubunitDecisionGateV18624

namespace GoldbachCircleMethodCompleteDecisionReductionV18627

/-- Exact end-to-end conditional reduction. The choice `M = 2*N` puts every
target `N` into the unchanged closed even block `[M/2,M]`. -/
theorem strongGoldbach_of_large_block_negativePart_subunit_and_finite_base
    (M₀ P R₀ : ℕ)
    (hLarge₀ : defectScaleThreshold ≤ M₀)
    (hMajor : ∀ M ≥ M₀, ∀ N ∈ evenTargetBlock M,
      (M : ℝ) / 14 ≤ twoScaleMajorIntegralReal M P R₀ N)
    (hMoment : ∀ M ≥ M₀,
      negativePartSquaredMoment (evenTargetBlock M)
        (twoScaleMinorIntegralReal M P R₀) < (M : ℝ)^2 / 784)
    (hFinite : ∀ N : ℕ, 4 ≤ N → Even N → 2 * N < M₀ → GoldbachAt N) :
    StrongGoldbach := by
  intro N hN4 hEven
  by_cases hLargeN : M₀ ≤ 2 * N
  · have hEmpty := evenBlock_goldbachExceptions_empty_of_negativePartMoment
      (2 * N) P R₀ (hLarge₀.trans hLargeN)
        (hMajor (2 * N) hLargeN) (hMoment (2 * N) hLargeN)
    by_contra hNot
    have hBlock : N ∈ evenTargetBlock (2 * N) :=
      (mem_evenTargetBlock_iff (2 * N) N).mpr ⟨hN4, by omega, hEven, by omega⟩
    have hMem : N ∈ (evenTargetBlock (2 * N)).filter (fun n => ¬ GoldbachAt n) :=
      Finset.mem_filter.mpr ⟨hBlock, hNot⟩
    rw [hEmpty] at hMem
    simp at hMem
  · exact hFinite N hN4 hEven (by omega)

end GoldbachCircleMethodCompleteDecisionReductionV18627
