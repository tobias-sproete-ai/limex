import GoldbachCircleMethodOffDivisorPairNormEnvelopeV18313

/-!
# Goldbach V1.8.314: off-divisor pair L2 adapter

The pointwise envelope of V1.8.313 is replaced by an exact finite energy
interface.  Each of the three channels containing an off-divisor factor is
controlled by a Cauchy--Schwarz product of literal left and reflected-right
energies on the unchanged pair carrier.

No smallness, cancellation, or absorption hypothesis is manufactured here.
The remaining analytic burden is exposed as three explicit energy-product
bounds.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodOffDivisorPairL2AdapterV18314

open GoldbachCircleMethodActiveConductorDivisorLocalizationV18290
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodOffDivisorPairNormEnvelopeV18313

/-- Finite real energy on an unchanged carrier. -/
noncomputable def finiteEnergy (J : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ J, (f n) ^ 2

/-- Finite real correlation on an unchanged carrier. -/
noncomputable def finiteCorrelation (J : Finset ℕ)
    (f g : ℕ → ℝ) : ℝ :=
  ∑ n ∈ J, f n * g n

/-- Finite Cauchy--Schwarz in the exact squared form required by the
off-divisor channels. -/
theorem finiteCorrelation_sq_le_energy_mul_energy
    (J : Finset ℕ) (f g : ℕ → ℝ) :
    (finiteCorrelation J f g) ^ 2 ≤
      finiteEnergy J f * finiteEnergy J g := by
  exact Finset.sum_mul_sq_le_sq_mul_sq J f g

/-- A nonnegative energy-product budget converts the squared
Cauchy--Schwarz estimate into a linear correlation budget. -/
theorem finiteCorrelation_le_of_energy_mul_le_sq
    (J : Finset ℕ) (f g : ℕ → ℝ) (C : ℝ)
    (hf : ∀ n ∈ J, 0 ≤ f n) (hg : ∀ n ∈ J, 0 ≤ g n)
    (hC : 0 ≤ C)
    (henergy : finiteEnergy J f * finiteEnergy J g ≤ C ^ 2) :
    finiteCorrelation J f g ≤ C := by
  have hcorr : 0 ≤ finiteCorrelation J f g := by
    unfold finiteCorrelation
    exact Finset.sum_nonneg (fun n hn => mul_nonneg (hf n hn) (hg n hn))
  have hsq : (finiteCorrelation J f g) ^ 2 ≤ C ^ 2 :=
    (finiteCorrelation_sq_le_energy_mul_energy J f g).trans henergy
  exact (sq_le_sq₀ hcorr hC).mp hsq

/-- Norm of the divisor-localized factor at one argument. -/
noncomputable def localizedFactorNorm {Q : ℕ} (hQ : 1 ≤ Q)
    (e : CharacterSlot Q) (b : ℝ) (w : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖divisorLocalizedAdjustedFactor hQ e.1 e.2 n b w‖

/-- Norm of the off-divisor factor at one argument. -/
noncomputable def offDivisorFactorNorm {Q : ℕ} (hQ : 1 ≤ Q)
    (e : CharacterSlot Q) (b : ℝ) (w : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖offDivisorAdjustedFactor hQ e.1 e.2 n b w‖

/-- Localized-left/off-divisor-right norm correlation. -/
noncomputable def localizedOffCorrelation {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℝ :=
  finiteCorrelation (pairFirstCarrier J N)
    (localizedFactorNorm hQ e b w)
    (fun n => offDivisorFactorNorm hQ e b w (N - n))

/-- Off-divisor-left/localized-right norm correlation. -/
noncomputable def offLocalizedCorrelation {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℝ :=
  finiteCorrelation (pairFirstCarrier J N)
    (offDivisorFactorNorm hQ e b w)
    (fun n => localizedFactorNorm hQ e b w (N - n))

/-- Off-divisor-left/off-divisor-right norm correlation. -/
noncomputable def offOffCorrelation {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) : ℝ :=
  finiteCorrelation (pairFirstCarrier J N)
    (offDivisorFactorNorm hQ e b w)
    (fun n => offDivisorFactorNorm hQ e b w (N - n))

/-- The V1.8.313 triangle envelope is exactly the sum of the three finite
norm correlations. -/
theorem offDivisorPairNormEnvelope_eq_correlations
    {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) :
    offDivisorPairNormEnvelope hQ J e N b w =
      localizedOffCorrelation hQ J e N b w +
      offLocalizedCorrelation hQ J e N b w +
      offOffCorrelation hQ J e N b w := by
  unfold offDivisorPairNormEnvelope localizedOffCorrelation
    offLocalizedCorrelation offOffCorrelation finiteCorrelation
    localizedFactorNorm offDivisorFactorNorm
  simp only [Finset.sum_add_distrib]

/-- The complete off-divisor remainder is bounded by the three exact finite
norm correlations. -/
theorem offDivisorPairRemainder_norm_le_correlations
    {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) :
    ‖offDivisorPairRemainder hQ J e N b w‖ ≤
      localizedOffCorrelation hQ J e N b w +
      offLocalizedCorrelation hQ J e N b w +
      offOffCorrelation hQ J e N b w := by
  rw [← offDivisorPairNormEnvelope_eq_correlations]
  exact offDivisorPairRemainder_norm_le_envelope hQ J e N b w

/-- Squared Cauchy--Schwarz bound for the localized/off-divisor channel. -/
theorem localizedOffCorrelation_sq_le
    {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) :
    (localizedOffCorrelation hQ J e N b w) ^ 2 ≤
      finiteEnergy (pairFirstCarrier J N) (localizedFactorNorm hQ e b w) *
      finiteEnergy (pairFirstCarrier J N)
        (fun n => offDivisorFactorNorm hQ e b w (N - n)) := by
  exact finiteCorrelation_sq_le_energy_mul_energy _ _ _

/-- Squared Cauchy--Schwarz bound for the off-divisor/localized channel. -/
theorem offLocalizedCorrelation_sq_le
    {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) :
    (offLocalizedCorrelation hQ J e N b w) ^ 2 ≤
      finiteEnergy (pairFirstCarrier J N) (offDivisorFactorNorm hQ e b w) *
      finiteEnergy (pairFirstCarrier J N)
        (fun n => localizedFactorNorm hQ e b w (N - n)) := by
  exact finiteCorrelation_sq_le_energy_mul_energy _ _ _

/-- Squared Cauchy--Schwarz bound for the off-divisor/off-divisor channel. -/
theorem offOffCorrelation_sq_le
    {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) :
    (offOffCorrelation hQ J e N b w) ^ 2 ≤
      finiteEnergy (pairFirstCarrier J N) (offDivisorFactorNorm hQ e b w) *
      finiteEnergy (pairFirstCarrier J N)
        (fun n => offDivisorFactorNorm hQ e b w (N - n)) := by
  exact finiteCorrelation_sq_le_energy_mul_energy _ _ _

/-- Three explicit energy-product budgets bound the entire off-divisor
remainder.  This is the fail-closed analytic interface replacing any hidden
pointwise-smallness assumption. -/
theorem offDivisorPairRemainder_norm_le_of_energy_budgets
    {Q : ℕ} (hQ : 1 ≤ Q)
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ)
    (b : ℝ) (w : ℕ → ℂ) (C₁ C₂ C₃ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (h₁ : finiteEnergy (pairFirstCarrier J N)
          (localizedFactorNorm hQ e b w) *
        finiteEnergy (pairFirstCarrier J N)
          (fun n => offDivisorFactorNorm hQ e b w (N - n)) ≤ C₁ ^ 2)
    (h₂ : finiteEnergy (pairFirstCarrier J N)
          (offDivisorFactorNorm hQ e b w) *
        finiteEnergy (pairFirstCarrier J N)
          (fun n => localizedFactorNorm hQ e b w (N - n)) ≤ C₂ ^ 2)
    (h₃ : finiteEnergy (pairFirstCarrier J N)
          (offDivisorFactorNorm hQ e b w) *
        finiteEnergy (pairFirstCarrier J N)
          (fun n => offDivisorFactorNorm hQ e b w (N - n)) ≤ C₃ ^ 2) :
    ‖offDivisorPairRemainder hQ J e N b w‖ ≤ C₁ + C₂ + C₃ := by
  have hnL (n : ℕ) : 0 ≤ localizedFactorNorm hQ e b w n := norm_nonneg _
  have hnO (n : ℕ) : 0 ≤ offDivisorFactorNorm hQ e b w n := norm_nonneg _
  have hcorr₁ : localizedOffCorrelation hQ J e N b w ≤ C₁ :=
    finiteCorrelation_le_of_energy_mul_le_sq _ _ _ C₁
      (fun n _hn => hnL n) (fun n _hn => hnO (N - n)) hC₁ h₁
  have hcorr₂ : offLocalizedCorrelation hQ J e N b w ≤ C₂ :=
    finiteCorrelation_le_of_energy_mul_le_sq _ _ _ C₂
      (fun n _hn => hnO n) (fun n _hn => hnL (N - n)) hC₂ h₂
  have hcorr₃ : offOffCorrelation hQ J e N b w ≤ C₃ :=
    finiteCorrelation_le_of_energy_mul_le_sq _ _ _ C₃
      (fun n _hn => hnO n) (fun n _hn => hnO (N - n)) hC₃ h₃
  exact (offDivisorPairRemainder_norm_le_correlations hQ J e N b w).trans
    (by linarith)

end GoldbachCircleMethodOffDivisorPairL2AdapterV18314
