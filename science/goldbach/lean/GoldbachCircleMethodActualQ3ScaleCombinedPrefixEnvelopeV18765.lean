import GoldbachCircleMethodActualQ3ScaleEstimateBridgeV18764

/-!
# V1.8.765: one genuine q=3 prefix ceiling from small and large regimes

Small prefixes are bounded directly by Mathlib's Chebyshev estimate.  Large
prefixes use the source-matched reduced-class estimate from V1.8.764.  The two
regimes are joined without changing the actual Dirichlet-character carrier.

The external `ScaleReducedClassEstimate` remains an explicit hypothesis.
No distribution theorem or Goldbach conclusion is asserted.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology
open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3ScaleCombinedPrefixEnvelopeV18765

open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformMajorPrefixReductionV1865
open GoldbachCircleMethodUniformResidueInputBridgeV1869
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757
open GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760
open GoldbachCircleMethodActualQ3ScaleEstimateBridgeV18764

/-- The literal q=3 character prefix is bounded by the full nonnegative
von-Mangoldt mass, hence by Mathlib's explicit Chebyshev linear estimate. -/
theorem fullLambdaQ3DirichletCharacterPartialSum_succ_norm_le_chebyshev
    (x : Nat) :
    ‖fullLambdaQ3DirichletCharacterPartialSum x.succ‖ ≤
      chebyshevConstant * (x : Real) := by
  unfold fullLambdaQ3DirichletCharacterPartialSum
  calc
    ‖∑ a ∈ Finset.range x.succ,
        (ArithmeticFunction.vonMangoldt a : Complex) *
          q3QuadraticDirichletCharacter (a : ZMod 3)‖ ≤
        ∑ a ∈ Finset.range x.succ,
          ‖(ArithmeticFunction.vonMangoldt a : Complex) *
            q3QuadraticDirichletCharacter (a : ZMod 3)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.range x.succ,
          ArithmeticFunction.vonMangoldt a := by
      apply Finset.sum_le_sum
      intro a _ha
      have hchar :
          ‖q3QuadraticDirichletCharacter (a : ZMod 3)‖ ≤ 1 := by
        rw [q3QuadraticDirichletCharacter_eq_table]
        unfold q3UnitDifferenceCharacterTable
        split_ifs <;> norm_num
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg hchar
    _ = Chebyshev.psi (x : Real) :=
      lambdaSum_range_succ_eq_psi x
    _ ≤ chebyshevConstant * (x : Real) :=
      Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg x)

/-- Direct small-prefix specialization at the project square-root split. -/
theorem fullLambdaQ3DirichletCharacterPartialSum_succ_norm_le_smallPrefix
    (M x : Nat)
    (hsmall : (x : Real) ≤ Real.sqrt (M : Real)) :
    ‖fullLambdaQ3DirichletCharacterPartialSum x.succ‖ ≤
      chebyshevConstant * Real.sqrt (M : Real) := by
  exact (fullLambdaQ3DirichletCharacterPartialSum_succ_norm_le_chebyshev x).trans
    (mul_le_mul_of_nonneg_left hsmall chebyshevConstant_pos.le)

/-- Conservative common ceiling for both prefix regimes. -/
noncomputable def actualQ3ScaleCombinedPrefixEnvelope
    (M : Nat) (C c : Real) : Real :=
  chebyshevConstant * Real.sqrt (M : Real) +
    2 * prefixEnvelope M C (c / 2)

/-- The source-matched scale estimate and the elementary small-prefix bound
produce one genuine-character ceiling over every `X <= M+1`. -/
theorem actualQ3DirichletCharacterPartialSumCeiling_of_scaleEstimate
    (M k₀ : Nat) (C c : Real)
    (hM : 0 < M) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hlog : (2 : Real) ^ 12 ≤ Real.log (M : Real))
    (hstart : (k₀ : Real) ≤ Real.sqrt (M : Real))
    (hscale : ScaleReducedClassEstimate 11 k₀ C c)
    (hthree : 3 ≤ logRadius 10 M) :
    ActualQ3DirichletCharacterPartialSumCeiling M
      (actualQ3ScaleCombinedPrefixEnvelope M C c) := by
  have hsmall0 :
      0 ≤ chebyshevConstant * Real.sqrt (M : Real) :=
    mul_nonneg chebyshevConstant_pos.le (Real.sqrt_nonneg _)
  have hlarge0 :
      0 ≤ 2 * prefixEnvelope M C (c / 2) := by
    unfold prefixEnvelope
    positivity
  refine ⟨add_nonneg hsmall0 hlarge0, ?_⟩
  intro X hXM
  rcases X with _ | x
  · simpa [fullLambdaQ3DirichletCharacterPartialSum,
      actualQ3ScaleCombinedPrefixEnvelope] using add_nonneg hsmall0 hlarge0
  · have hxM : x ≤ M := by omega
    by_cases hlarge : Real.sqrt (M : Real) ≤ x
    · exact (dirichletCharacterPartialSum_norm_le_largePrefixScaleEstimate
        M x k₀ C c hM hC hc hlog hstart hscale hthree hxM hlarge).trans
          (le_add_of_nonneg_left hsmall0)
    · exact (fullLambdaQ3DirichletCharacterPartialSum_succ_norm_le_smallPrefix
        M x (le_of_not_ge hlarge)).trans
          (le_add_of_nonneg_right hlarge0)

end GoldbachCircleMethodActualQ3ScaleCombinedPrefixEnvelopeV18765
