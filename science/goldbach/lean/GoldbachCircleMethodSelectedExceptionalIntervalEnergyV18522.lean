import GoldbachCircleMethodNonprincipalConductorSumEnvelopeV18521
import GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510

/-!
# Goldbach V1.8.522: selected exceptional coefficient interval energy

The exceptional correction is returned to its true one-slot support.  Its
coefficient moment is bounded by one conductor's incomplete companion energy,
without paying for every nonprincipal primitive character.  This is the sharp
three-channel alternative to the lossy V1.8.514 augmentation.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodSelectedExceptionalIntervalEnergyV18522

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCenteredPrincipalNetExponentV18504
open GoldbachCircleMethodCompanionIntervalEnergyBoundV18496
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteIntervalRemainderReserveV18229
open GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodRemovedConvolutionNormV18123

noncomputable def selectedCoefficientBlockMass
    (Q B : ℕ) (w : ℕ → ℂ) (e : CharacterSlot Q) : ℝ :=
  ∑ n ∈ blockCarrier B, ‖windowCoefficient e.1 n w e.2‖ ^ 2

/-- One selected character slot costs only its own conductor normalization
and companion interval energy. -/
theorem selectedCoefficientBlockMass_le_interval_energy
    (Q B : ℕ) (w : ℕ → ℂ) (e : CharacterSlot Q)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ q : PositiveLevel Q,
      e.1.val * q.val ≤ Q ∧ Nat.Coprime e.1.val q.val →
        ‖w (e.1.val * q.val)‖ ≤ V) :
    selectedCoefficientBlockMass Q B w e ≤
      (((e.1.val : ℝ) / (e.1.val.totient : ℝ)) ^ 2) *
        (((B + 1 : ℕ) : ℝ) * (∑ q : PositiveLevel Q,
          ‖literalCoefficient e.1 q w‖ ^ 2 *
            (q.val.totient : ℝ)) +
          2 * (Q : ℝ) ^ 4 * V * V) := by
  have hscale :
      0 ≤ ((e.1.val : ℝ) / (e.1.val.totient : ℝ)) ^ 2 := sq_nonneg _
  have hsubset : blockCarrier B ⊆ Finset.range (B + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (by
      have hnB : n ≤ B := (Finset.mem_Ioc.mp hn).2
      omega)
  unfold selectedCoefficientBlockMass
  calc
    (∑ n ∈ blockCarrier B, ‖windowCoefficient e.1 n w e.2‖ ^ 2) ≤
        ∑ n ∈ blockCarrier B,
          (((e.1.val : ℝ) / (e.1.val.totient : ℝ)) ^ 2) *
            ‖finiteCompanion e.1 n w‖ ^ 2 := by
      exact Finset.sum_le_sum
        (fun n _hn => windowCoefficient_sq_le_companion_sq e.1 n w e.2)
    _ = (((e.1.val : ℝ) / (e.1.val.totient : ℝ)) ^ 2) *
          (∑ n ∈ blockCarrier B, ‖finiteCompanion e.1 n w‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (((e.1.val : ℝ) / (e.1.val.totient : ℝ)) ^ 2) *
          (∑ n ∈ Finset.range (B + 1),
            ‖finiteCompanion e.1 n w‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _hn _hnot => sq_nonneg ‖finiteCompanion e.1 n w‖)
    _ = (((e.1.val : ℝ) / (e.1.val.totient : ℝ)) ^ 2) *
          (∑ i ∈ Finset.range (B + 1),
            ‖finiteCompanion e.1 (0 + i) w‖ ^ 2) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hscale
      exact finiteCompanion_interval_energy_le
        e.1 w hwReal 0 (B + 1) V hV hwBound

/-- Exact identification of the old exceptional block with the selected
one-slot coefficient mass. -/
theorem hybridExceptionalBlockBudget_eq_selectedMass
    (B : ℕ) (rho : ℝ)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) :
    hybridExceptionalBlockBudget B rho e =
      (9 / 4 : ℝ) *
        selectedCoefficientBlockMass (centeredPrincipalCutoff B rho) B
          (logWeight ((B : ℝ) ^ rho) canonicalLogBump) e := by
  unfold hybridExceptionalBlockBudget selectedCoefficientBlockMass
  rw [Finset.mul_sum]

/-- Canonical selected-slot envelope.  The factor `9/4` is retained, but no
full nonprincipal-family coefficient mass is introduced. -/
theorem hybridExceptionalBlockBudget_le_selected_interval_energy
    (B : ℕ) (rho : ℝ)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) :
    hybridExceptionalBlockBudget B rho e ≤
      (9 / 4 : ℝ) *
        ((((e.1.val : ℝ) / (e.1.val.totient : ℝ)) ^ 2) *
          (((B + 1 : ℕ) : ℝ) *
              (∑ q : PositiveLevel (centeredPrincipalCutoff B rho),
                ‖literalCoefficient e.1 q
                  (logWeight ((B : ℝ) ^ rho) canonicalLogBump)‖ ^ 2 *
                    (q.val.totient : ℝ)) +
            2 * (centeredPrincipalCutoff B rho : ℝ) ^ 4)) := by
  rw [hybridExceptionalBlockBudget_eq_selectedMass]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hwReal : ∀ n : ℕ,
      star (logWeight ((B : ℝ) ^ rho) canonicalLogBump n) =
        logWeight ((B : ℝ) ^ rho) canonicalLogBump n := by
    intro n
    simp [logWeight]
  have hbound : ∀ q : PositiveLevel (centeredPrincipalCutoff B rho),
      e.1.val * q.val ≤ centeredPrincipalCutoff B rho ∧
          Nat.Coprime e.1.val q.val →
        ‖logWeight ((B : ℝ) ^ rho) canonicalLogBump
          (e.1.val * q.val)‖ ≤ (1 : ℝ) := by
    intro q _hq
    exact norm_logWeight_canonical_le_one ((B : ℝ) ^ rho) _
  simpa only [mul_one] using
    selectedCoefficientBlockMass_le_interval_energy
      (centeredPrincipalCutoff B rho) B
      (logWeight ((B : ℝ) ^ rho) canonicalLogBump) e
      hwReal 1 zero_le_one hbound

end GoldbachCircleMethodSelectedExceptionalIntervalEnergyV18522
