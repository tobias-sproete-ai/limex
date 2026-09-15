import GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752

/-!
# V1.8.753: actual q=3 prefix local-density extraction

The literal q=3 residue transform of V1.8.752 contains a large deterministic
local bias: von Mangoldt mass is not equidistributed among all three residue
classes because the zero class contains only powers of three.  Consequently,
the full three-class discrepancy must not be declared a small error.

This append-only module extracts, at every finite prefix, the exact zero-class
mass and the common mean of the two unit classes.  Only the imbalance between
the unit classes remains in the residual mode.  The extraction is then lifted
through the triangular pair factorization and the Abel remainder.

No estimate for the unit-class imbalance is asserted or inhabited.  No prime
number theorem in progressions, absorption theorem, exceptional-set estimate,
or Goldbach conclusion is proved.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddFourierBesselBridgeV18668
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualLambdaPairSourceMeanV710AdapterV18717
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3WeightedFiberPullbackV18742
open GoldbachCircleMethodActualQ3UnitModeSquareBudgetV18744
open GoldbachCircleMethodActualQ3PairResidueSignedTriangularGateV18748
open GoldbachCircleMethodActualQ3TriangularPairCarrierPullbackV18750
open GoldbachCircleMethodActualQ3TriangularOneDimensionalModeReductionV18751
open GoldbachCircleMethodActualOddLambdaQ3ResidueDiscrepancyV18752

/-- Exact finite-prefix mean of the two prime-compatible residue classes. -/
noncomputable def oddLambdaQ3UnitMean (M B : Nat) : Complex :=
  (oddLambdaQ3ResidueMass M B (1 : ZMod 3) +
      oddLambdaQ3ResidueMass M B (2 : ZMod 3)) / 2

/-- Local-density reference: preserve the literal zero-class mass and replace
the two unit-class masses by their exact common mean. -/
noncomputable def oddLambdaQ3LocalDensityReferenceMass
    (M B : Nat) (r : ZMod 3) : Complex :=
  if r = 0 then oddLambdaQ3ResidueMass M B r
  else oddLambdaQ3UnitMean M B

/-- Fourier mode of the exact finite-prefix local-density reference. -/
noncomputable def oddLambdaQ3LocalDensityMode
    (M B : Nat) (xi : ZMod 3) : Complex :=
  ∑ r : ZMod 3,
    oddLambdaQ3LocalDensityReferenceMass M B r *
      ZMod.stdAddChar (r * xi)

/-- Fourier residual after the local-density reference has been removed. -/
noncomputable def oddLambdaQ3UnitBalanceResidualMode
    (M B : Nat) (xi : ZMod 3) : Complex :=
  ∑ r : ZMod 3,
    (oddLambdaQ3ResidueMass M B r -
        oddLambdaQ3LocalDensityReferenceMass M B r) *
      ZMod.stdAddChar (r * xi)

/-- Literal L1 budget of the finite residual.  Its zero-class term is
definitionally zero; only the imbalance of the two unit classes remains. -/
noncomputable def oddLambdaQ3UnitBalanceL1
    (M B : Nat) : Real :=
  ∑ r : ZMod 3,
    ‖oddLambdaQ3ResidueMass M B r -
      oddLambdaQ3LocalDensityReferenceMass M B r‖

theorem localDensityReferenceMass_zero
    (M B : Nat) :
    oddLambdaQ3LocalDensityReferenceMass M B (0 : ZMod 3) =
      oddLambdaQ3ResidueMass M B (0 : ZMod 3) := by
  simp [oddLambdaQ3LocalDensityReferenceMass]

theorem localDensityReferenceMass_unit
    (M B : Nat) (r : ZMod 3) (hr : r ≠ 0) :
    oddLambdaQ3LocalDensityReferenceMass M B r =
      oddLambdaQ3UnitMean M B := by
  simp [oddLambdaQ3LocalDensityReferenceMass, hr]

/-- Exact split of every actual incomplete q=3 Lambda mode into its local
density component and its unit-class balance residual. -/
theorem oddLambdaQ3Prefix_eq_localDensity_add_unitBalanceResidual
    (M B : Nat) (xi : ZMod 3) :
    oddLambdaQ3Prefix M B xi =
      oddLambdaQ3LocalDensityMode M B xi +
        oddLambdaQ3UnitBalanceResidualMode M B xi := by
  rw [oddLambdaQ3Prefix_eq_residue_transform]
  unfold oddLambdaQ3LocalDensityMode oddLambdaQ3UnitBalanceResidualMode
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

theorem oddLambdaQ3UnitBalanceL1_nonneg
    (M B : Nat) :
    0 ≤ oddLambdaQ3UnitBalanceL1 M B := by
  unfold oddLambdaQ3UnitBalanceL1
  positivity

/-- The residual mode is bounded only by the post-extraction unit-balance
budget; the large local q=3 bias is absent from this inequality. -/
theorem oddLambdaQ3UnitBalanceResidualMode_norm_le
    (M B : Nat) (xi : ZMod 3) :
    ‖oddLambdaQ3UnitBalanceResidualMode M B xi‖ ≤
      oddLambdaQ3UnitBalanceL1 M B := by
  unfold oddLambdaQ3UnitBalanceResidualMode oddLambdaQ3UnitBalanceL1
  calc
    _ ≤ ∑ r : ZMod 3,
        ‖(oddLambdaQ3ResidueMass M B r -
            oddLambdaQ3LocalDensityReferenceMass M B r) *
          ZMod.stdAddChar (r * xi)‖ := norm_sum_le _ _
    _ = ∑ r : ZMod 3,
        ‖oddLambdaQ3ResidueMass M B r -
          oddLambdaQ3LocalDensityReferenceMass M B r‖ := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [norm_mul]
      have hchar : ‖ZMod.stdAddChar (r * xi)‖ = 1 := by simp
      rw [hchar, mul_one]

/-- Open arithmetic contract after correct local-density extraction. -/
def ActualOddLambdaQ3UnitBalanceCeiling (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧ ∀ B : Nat, oddLambdaQ3UnitBalanceL1 M B ≤ D

/-- The local-density component lifted through the literal triangular pair
factorization. -/
noncomputable def actualQ3TriangularPairLocalDensityMode
    (M n k : Nat) (xi : ZMod 3) : Complex :=
  ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * xi) *
    (∑ a ∈ oddCarrier M,
      ((ArithmeticFunction.vonMangoldt a : Complex) *
          ZMod.stdAddChar ((a : ZMod 3) * xi)) *
        oddLambdaQ3LocalDensityMode M (2 * k - a) xi)

/-- The post-extraction balance residual lifted through the same pair
factorization. -/
noncomputable def actualQ3TriangularPairUnitBalanceResidualMode
    (M n k : Nat) (xi : ZMod 3) : Complex :=
  ZMod.stdAddChar (((-2 * (n : Int) : Int) : ZMod 3) * xi) *
    (∑ a ∈ oddCarrier M,
      ((ArithmeticFunction.vonMangoldt a : Complex) *
          ZMod.stdAddChar ((a : ZMod 3) * xi)) *
        oddLambdaQ3UnitBalanceResidualMode M (2 * k - a) xi)

theorem actualQ3TriangularPairMode_eq_localDensity_add_unitBalanceResidual
    (M n k : Nat) (xi : ZMod 3) :
    actualQ3TriangularPairMode M n k xi =
      actualQ3TriangularPairLocalDensityMode M n k xi +
        actualQ3TriangularPairUnitBalanceResidualMode M n k xi := by
  rw [actualQ3TriangularPairMode_eq_outer_prefix]
  unfold actualQ3TriangularPairLocalDensityMode
    actualQ3TriangularPairUnitBalanceResidualMode
  simp_rw [oddLambdaQ3Prefix_eq_localDensity_add_unitBalanceResidual]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, mul_add]

/-- One post-extraction triangular residual mode costs at most total odd
Lambda mass times the supplied unit-balance ceiling. -/
theorem actualQ3TriangularPairUnitBalanceResidualMode_norm_le
    (M n k : Nat) (xi : ZMod 3) (D : Real)
    (hD : ActualOddLambdaQ3UnitBalanceCeiling M D) :
    ‖actualQ3TriangularPairUnitBalanceResidualMode M n k xi‖ ≤
      oddLambdaSum M * D := by
  unfold actualQ3TriangularPairUnitBalanceResidualMode
  rw [norm_mul, norm_q3_targetPhase_eq_one, one_mul]
  calc
    _ ≤ ∑ a ∈ oddCarrier M,
        ‖((ArithmeticFunction.vonMangoldt a : Complex) *
              ZMod.stdAddChar ((a : ZMod 3) * xi)) *
            oddLambdaQ3UnitBalanceResidualMode M (2 * k - a) xi‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ oddCarrier M,
        ArithmeticFunction.vonMangoldt a * D := by
      apply Finset.sum_le_sum
      intro a _ha
      rw [norm_mul, norm_mul]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hchar : ‖ZMod.stdAddChar ((a : ZMod 3) * xi)‖ = 1 := by simp
      rw [hchar, mul_one]
      exact mul_le_mul_of_nonneg_left
        ((oddLambdaQ3UnitBalanceResidualMode_norm_le
          M (2 * k - a) xi).trans (hD.2 (2 * k - a)))
        ArithmeticFunction.vonMangoldt_nonneg
    _ = oddLambdaSum M * D := by
      unfold oddLambdaSum
      rw [Finset.sum_mul]

noncomputable def actualQ3RawTriangularPairLocalDensity
    (M n k : Nat) : Complex :=
  actualQ3TriangularPairLocalDensityMode M n k (1 : ZMod 3) +
    actualQ3TriangularPairLocalDensityMode M n k (2 : ZMod 3)

noncomputable def actualQ3RawTriangularPairUnitBalanceResidual
    (M n k : Nat) : Complex :=
  actualQ3TriangularPairUnitBalanceResidualMode M n k (1 : ZMod 3) +
    actualQ3TriangularPairUnitBalanceResidualMode M n k (2 : ZMod 3)

/-- Exact raw-triangle split. -/
theorem actualQ3RawTriangularPairPrefix_eq_localDensity_add_unitBalanceResidual
    (M n k : Nat) :
    actualQ3RawTriangularPairPrefix M n k =
      actualQ3RawTriangularPairLocalDensity M n k +
        actualQ3RawTriangularPairUnitBalanceResidual M n k := by
  rw [actualQ3RawTriangularPairPrefix_eq_two_modes]
  rw [actualQ3TriangularPairMode_eq_localDensity_add_unitBalanceResidual]
  rw [actualQ3TriangularPairMode_eq_localDensity_add_unitBalanceResidual]
  unfold actualQ3RawTriangularPairLocalDensity
    actualQ3RawTriangularPairUnitBalanceResidual
  ring

theorem actualQ3RawTriangularPairUnitBalanceResidual_norm_le
    (M n k : Nat) (D : Real)
    (hD : ActualOddLambdaQ3UnitBalanceCeiling M D) :
    ‖actualQ3RawTriangularPairUnitBalanceResidual M n k‖ ≤
      2 * oddLambdaSum M * D := by
  unfold actualQ3RawTriangularPairUnitBalanceResidual
  calc
    _ ≤ ‖actualQ3TriangularPairUnitBalanceResidualMode
          M n k (1 : ZMod 3)‖ +
        ‖actualQ3TriangularPairUnitBalanceResidualMode
          M n k (2 : ZMod 3)‖ := norm_add_le _ _
    _ ≤ oddLambdaSum M * D + oddLambdaSum M * D :=
      add_le_add
        (actualQ3TriangularPairUnitBalanceResidualMode_norm_le
          M n k (1 : ZMod 3) D hD)
        (actualQ3TriangularPairUnitBalanceResidualMode_norm_le
          M n k (2 : ZMod 3) D hD)
    _ = 2 * oddLambdaSum M * D := by ring

/-- The previously centered triangle now has an exact local-density main
piece.  The old constant-centering term remains in that main piece. -/
noncomputable def actualQ3CenteredTriangularLocalDensityMain
    (M n k : Nat) : Complex :=
  actualQ3RawTriangularPairLocalDensity M n k -
    (actualLambdaPairSourceMean M : Complex) * q3ConstantPrefix n k

theorem actualQ3CenteredTriangularPairPrefix_eq_localDensityMain_add_residual
    (M n k : Nat) :
    actualQ3CenteredTriangularPairPrefix M n k =
      actualQ3CenteredTriangularLocalDensityMain M n k +
        actualQ3RawTriangularPairUnitBalanceResidual M n k := by
  unfold actualQ3CenteredTriangularPairPrefix
    actualQ3CenteredTriangularLocalDensityMain
  rw [actualQ3RawTriangularPairPrefix_eq_localDensity_add_unitBalanceResidual]
  ring

/-- Local-density contribution to the q=3 Abel remainder. -/
noncomputable def actualQ3LocalDensityTriangularRemainder
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) : Complex :=
  -∑ a ∈ Finset.range M,
    selectedPairSourceCoordinateSincVariation M q n a *
      actualQ3CenteredTriangularLocalDensityMain M n (a + 1)

/-- Post-extraction unit-balance contribution to the q=3 Abel remainder. -/
noncomputable def actualQ3UnitBalanceTriangularRemainder
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) : Complex :=
  -∑ a ∈ Finset.range M,
    selectedPairSourceCoordinateSincVariation M q n a *
      actualQ3RawTriangularPairUnitBalanceResidual M n (a + 1)

/-- Exact split of the source-specific q=3 triangular Abel remainder. -/
theorem actualQ3TriangularPrefixRemainder_eq_localDensity_add_unitBalance
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    actualQ3TriangularPrefixRemainder M q n =
      actualQ3LocalDensityTriangularRemainder M q n +
        actualQ3UnitBalanceTriangularRemainder M q n := by
  rw [actualQ3TriangularPrefixRemainder_eq_pairPrefixes M q n hq]
  unfold actualQ3LocalDensityTriangularRemainder
    actualQ3UnitBalanceTriangularRemainder
  simp_rw [actualQ3CenteredTriangularPairPrefix_eq_localDensityMain_add_residual]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- Only the true unit-class imbalance is charged to the residual budget. -/
theorem actualQ3UnitBalanceTriangularRemainder_norm_le
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (D : Real)
    (hD : ActualOddLambdaQ3UnitBalanceCeiling M D) :
    ‖actualQ3UnitBalanceTriangularRemainder M q n‖ ≤
      (∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖) *
        (2 * oddLambdaSum M * D) := by
  unfold actualQ3UnitBalanceTriangularRemainder
  rw [norm_neg]
  calc
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a *
          actualQ3RawTriangularPairUnitBalanceResidual M n (a + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.range M,
        ‖selectedPairSourceCoordinateSincVariation M q n a‖ *
          (2 * oddLambdaSum M * D) := by
      apply Finset.sum_le_sum
      intro a _ha
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (actualQ3RawTriangularPairUnitBalanceResidual_norm_le
          M n (a + 1) D hD)
        (norm_nonneg _)
    _ = (∑ a ∈ Finset.range M,
          ‖selectedPairSourceCoordinateSincVariation M q n a‖) *
        (2 * oddLambdaSum M * D) := by
      rw [Finset.sum_mul]

end GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
