import GoldbachCircleMethodHybridCenteredDecayingSourceBudgetV18525
import GoldbachCircleMethodSelectedExceptionalIntervalEnergyV18522
import GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263

/-!
# Goldbach V1.8.526: decaying exceptional channel split

The decay-preserving V1.8.525 budget is split into the existing principal and
nonprincipal primitive channels plus one explicitly selected exceptional
channel.  The latter is connected to the one-conductor interval-energy bound
of V1.8.522.  Active exceptional-zero attestation yields a strict improvement
of the scalar source factor for every fixed block `B ≥ 3`; no block-uniform
positive lower bound on the zero gap is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodDecayingExceptionalChannelSplitV18526

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodCenteredPrincipalNetExponentV18504
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodHybridCenteredDecayingSourceBudgetV18525
open GoldbachCircleMethodFiniteIntervalRemainderReserveV18229
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodSelectedExceptionalIntervalEnergyV18522
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

noncomputable def exceptionalDecayFactor (B : ℕ) (b : ℝ) : ℝ :=
  (9 / 4 : ℝ) * ((B : ℝ) / 2) ^ (-2 * b)

noncomputable def decayingExceptionalBlockBudget
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) : ℝ :=
  exceptionalDecayFactor B b *
    selectedCoefficientBlockMass (centeredPrincipalCutoff B rho) B
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump) e

/-- Exact three-channel identity with the exceptional decay retained. -/
theorem hybridCenteredDecayingSourceBudget_eq_channel_sum
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) :
    hybridCenteredDecayingSourceBudget B rho b e =
      hybridPrincipalBlockBudget B rho +
        hybridNonprincipalBlockBudget B rho +
          decayingExceptionalBlockBudget B rho b e := by
  unfold hybridCenteredDecayingSourceBudget hybridPrincipalBlockBudget
    hybridNonprincipalBlockBudget decayingExceptionalBlockBudget
    exceptionalDecayFactor selectedCoefficientBlockMass
    centeredPrincipalCutoff centeredPrincipalScale
  rw [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- The decaying exceptional channel is bounded by one conductor interval,
not by the full nonprincipal character family. -/
theorem decayingExceptionalBlockBudget_le_selected_interval_energy
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) :
    decayingExceptionalBlockBudget B rho b e ≤
      exceptionalDecayFactor B b *
        ((((e.1.val : ℝ) / (e.1.val.totient : ℝ)) ^ 2) *
          (((B + 1 : ℕ) : ℝ) *
              (∑ q : PositiveLevel (centeredPrincipalCutoff B rho),
                ‖literalCoefficient e.1 q
                  (logWeight ((B : ℝ) ^ rho) canonicalLogBump)‖ ^ 2 *
                    (q.val.totient : ℝ)) +
            2 * (centeredPrincipalCutoff B rho : ℝ) ^ 4)) := by
  unfold decayingExceptionalBlockBudget exceptionalDecayFactor
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [mul_one] using
    selectedCoefficientBlockMass_le_interval_energy
      (centeredPrincipalCutoff B rho) B
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump) e
      (by intro n; simp [logWeight]) 1 zero_le_one
      (by
        intro q _hq
        exact norm_logWeight_canonical_le_one ((B : ℝ) ^ rho) _)

/-- The refined exceptional block never exceeds the old uniform `9/4`
envelope when `B ≥ 2` and `b ≥ 0`. -/
theorem decayingExceptionalBlockBudget_le_uniform
    (B : ℕ) (rho b : ℝ) (hB : 2 ≤ B) (hb : 0 ≤ b)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) :
    decayingExceptionalBlockBudget B rho b e ≤
      hybridExceptionalBlockBudget B rho e := by
  have hbase : (1 : ℝ) ≤ (B : ℝ) / 2 := by
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by exact_mod_cast hB)
  have hdecay : ((B : ℝ) / 2) ^ (-2 * b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hmass : 0 ≤ selectedCoefficientBlockMass
      (centeredPrincipalCutoff B rho) B
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump) e := by
    unfold selectedCoefficientBlockMass
    positivity
  rw [hybridExceptionalBlockBudget_eq_selectedMass]
  unfold decayingExceptionalBlockBudget exceptionalDecayFactor
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 9 / 4) hdecay) hmass

/-- For proof-carrying active exceptional-zero data, the scalar source cost is
strictly below `9/4` on every fixed block `B ≥ 3`.  This is pointwise in the
attested gap and is not a uniform power-saving theorem. -/
theorem exceptionalDecayFactor_lt_nine_fourths_of_attested
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (B : ℕ) (hB : 3 ≤ B) :
    exceptionalDecayFactor B d.zeroGap < (9 / 4 : ℝ) := by
  have hbase : (1 : ℝ) < (B : ℝ) / 2 := by
    have hB' : (3 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hexp : -2 * d.zeroGap < 0 := by
    nlinarith [zeroGap_pos d]
  have hdecay : ((B : ℝ) / 2) ^ (-2 * d.zeroGap) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hbase hexp
  unfold exceptionalDecayFactor
  nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (B : ℝ) / 2)
    (-2 * d.zeroGap)]

end GoldbachCircleMethodDecayingExceptionalChannelSplitV18526
