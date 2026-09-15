import GoldbachCircleMethodHybridTwoChannelNecessaryMarginV18516
import GoldbachCircleMethodNonprincipalPrimitiveConductorDecompositionV18507

/-!
# Goldbach V1.8.517: exact augmented nonprincipal conductor target

The sole remaining nonprincipal block budget is expanded without estimates.
Its primitive-source factor is reindexed by conductor and the uniform `9/4`
term is separated exactly.  This identifies the finite double sum on which a
future large-sieve or dispersion estimate must act.  No such estimate is
asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridAugmentedConductorTargetV18517

open GoldbachCircleMethodActualPrimitiveSourceNormalizationV18470
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodHybridAugmentedNonprincipalChannelV18514
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalPrimitiveConductorDecompositionV18507
open GoldbachCircleMethodPrincipalWindowBoundaryV18121

/-- The conductor-reindexed primitive source kernel at one target. -/
noncomputable def nonprincipalConductorSourceKernel
    (Q B N : ℕ) (H : ℝ) : ℝ :=
  ∑ q : PositiveLevel Q,
    if q.val = 1 then 0 else rawPrimitiveSourceEnergy q.val B N H

/-- Exact source reindexing, with conductor one removed by a literal zero. -/
theorem nonprincipalConductorSourceKernel_eq_sourceEnergy
    (Q B N : ℕ) (H : ℝ) :
    nonprincipalConductorSourceKernel Q B N H =
      nonprincipalPrimitiveSourceEnergy Q B N H := by
  exact (nonprincipalPrimitiveSourceEnergy_eq_sum_raw_except_one Q B N H).symm

/-- The true finite target/conductor double sum. -/
noncomputable def hybridNonprincipalConductorDoubleSum
    (B : ℕ) (rho : ℝ) : ℝ :=
  let Q := GoldbachCircleMethodCenteredPrincipalNetExponentV18504.centeredPrincipalCutoff B rho
  let H := centeredPrincipalScale B rho
  let w := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  ∑ n ∈ blockCarrier B,
    ∑ q : PositiveLevel Q,
      nonprincipalCoefficientEnergy Q n w *
        (if q.val = 1 then 0 else rawPrimitiveSourceEnergy q.val B n H)

/-- Coefficient mass multiplying the uniform selected-exceptional constant. -/
noncomputable def hybridNonprincipalCoefficientMass
    (B : ℕ) (rho : ℝ) : ℝ :=
  let Q := GoldbachCircleMethodCenteredPrincipalNetExponentV18504.centeredPrincipalCutoff B rho
  let w := logWeight ((B : ℝ) ^ rho) canonicalLogBump
  ∑ n ∈ blockCarrier B,
    nonprincipalCoefficientEnergy Q n w

/-- Exact decomposition of the augmented channel into its conductor double
sum and its explicit coefficient-mass correction. -/
theorem hybridAugmentedNonprincipalBlockBudget_eq_conductorDoubleSum
    (B : ℕ) (rho : ℝ) :
    hybridAugmentedNonprincipalBlockBudget B rho =
      hybridNonprincipalConductorDoubleSum B rho +
        (9 / 4 : ℝ) * hybridNonprincipalCoefficientMass B rho := by
  unfold hybridAugmentedNonprincipalBlockBudget
    hybridNonprincipalConductorDoubleSum hybridNonprincipalCoefficientMass
  simp_rw [← nonprincipalConductorSourceKernel_eq_sourceEnergy]
  unfold nonprincipalConductorSourceKernel
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Both pieces of the exact target are nonnegative. -/
theorem hybridNonprincipalConductorDoubleSum_nonneg
    (B : ℕ) (rho : ℝ) :
    0 ≤ hybridNonprincipalConductorDoubleSum B rho := by
  unfold hybridNonprincipalConductorDoubleSum
  apply Finset.sum_nonneg
  intro n _hn
  apply Finset.sum_nonneg
  intro q _hq
  by_cases hq : q.val = 1
  · simp [hq]
  · simp only [hq, if_false]
    apply mul_nonneg
    · unfold nonprincipalCoefficientEnergy
      apply Finset.sum_nonneg
      intro t _ht
      split_ifs <;> positivity
    · unfold rawPrimitiveSourceEnergy
      apply Finset.sum_nonneg
      intro chi _hchi
      positivity

theorem hybridNonprincipalCoefficientMass_nonneg
    (B : ℕ) (rho : ℝ) :
    0 ≤ hybridNonprincipalCoefficientMass B rho := by
  unfold hybridNonprincipalCoefficientMass nonprincipalCoefficientEnergy
  apply Finset.sum_nonneg
  intro n _hn
  apply Finset.sum_nonneg
  intro t _ht
  split_ifs <;> positivity

end GoldbachCircleMethodHybridAugmentedConductorTargetV18517
