import GoldbachCircleMethodSupportedCompanionEnergyV18192

/-!
# Actual principal and active residual moments, V1.8.193

This module composes the literal V138 Fourier residuals, V190 finite Parseval
transfer and V192 actual supported companion energies at `R = B^rho`.
It does not estimate a reserve, an exceptional set or a Goldbach count.
-/

set_option autoImplicit false

open scoped BigOperators Classical ContDiff
open MeasureTheory
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodActualInputModelResidualV18138
open GoldbachCircleMethodAuxiliaryMinorGlobalErrorV18137
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodSupportedCompanionEnergyV18192

namespace GoldbachCircleMethodActualResidualMomentCompositionV18193

/-- The exact exponent conversion used after taking `eps = rho/48` in the
energy estimate. -/
theorem residual_energy_power_identity (B : ℕ) (hB : 1 ≤ B) (rho : ℝ) :
    ((B : ℝ)^rho)^(-(2 : ℝ) / 3) * ((B : ℝ)^(rho / 48))^2 =
      ((B : ℝ)^rho)^(-(5 : ℝ) / 8) := by
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  rw [← Real.rpow_mul_natCast hB0]
  norm_num only [Nat.cast_ofNat]
  rw [show rho / 48 * (2 : ℝ) = rho * ((1 : ℝ) / 24) by ring]
  rw [Real.rpow_mul hB0]
  rw [← Real.rpow_add (Real.rpow_pos_of_pos hBpos rho)]
  congr 1
  norm_num

/-- Literal active analogue of V190's principal residual Parseval theorem.
The same `b` and `CharacterSlot` occur in the residual and supported model. -/
theorem active_residual_convolution_parseval_bound
    (B : ℕ) (hB : 6 ≤ B) (R C : ℝ) (hR : 1 < R) (hC : 0 ≤ C)
    (hV : RealVaughanEstimate C)
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ R)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ) / 10000))
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hG : ∀ u : ℝ, |G u| ≤ M)
    (hplateau : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → G u = 1)
    (e : CharacterSlot ⌊R^2⌋₊) :
    let Cv :=
      9 * ((1 + M) / 2 + 3 * Real.pi) +
        (8 * (48 : ℝ)^8 * C) * (1 + 2 * M) + 46 * M
    let companion := fun N : ℕ =>
      blockInput B N + supportedAdjustedModel B N R b G e
    (∑ k ∈ Finset.Icc (0 : ℤ) (2 * B : ℕ),
      ‖integerPairConvolution (blockCarrier B)
        (fun N => inputActiveResidual B N R hR b G e) companion k‖ ^ 2) ≤
      Cv^2 * (B : ℝ)^2 * R^(-(2 : ℝ) / 3) *
        ∑ N ∈ blockCarrier B, ‖companion N‖ ^ 2 := by
  dsimp only
  have hbase := finite_supported_convolution_parseval_bound
    (blockCarrier B) (fun N => inputActiveResidual B N R hR b G e)
    (fun N => blockInput B N + supportedAdjustedModel B N R b G e)
    (Finset.Icc (0 : ℤ) (2 * B : ℕ))
    ((9 * ((1 + M) / 2 + 3 * Real.pi) +
      8 * 48^8 * C * (1 + 2 * M) + 46 * M) *
      (B : ℝ) * R^(-(1 : ℝ) / 3)) (by positivity) (by
        intro x
        rw [supportedFourierPolynomial_apply]
        exact input_active_fourier_bound B hB R C hR hC hV hlower hupper
          b hb hb1 G M hM hG hplateau e x)
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR.le
  rw [residual_scale_square _ R B hR0] at hbase
  exact hbase

/-- Actual principal residual moment at the genuine power scale. The constant
is fixed after `rho` but before the block size and moving frequency. -/
theorem actual_principal_residual_moment_power_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hGsupport : ∀ t : ℝ, 2 < t → G t = 0)
    (C MG rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hMG : 0 ≤ MG) (hG : ∀ u : ℝ, |G u| ≤ MG)
    (hplateau : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → G u = 1)
    (hrho : 0 < rho) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (B : ℕ) (_hB : 6 ≤ B),
      ∀ (_hR2 : 2 ≤ (B : ℝ)^rho),
      Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ (B : ℝ)^rho →
      (B : ℝ)^rho ≤ (B : ℝ)^((1 : ℝ) / 10000) →
      (∑ k ∈ Finset.Icc (0 : ℤ) (2 * B : ℕ),
        ‖integerPairConvolution (blockCarrier B)
          (fun N => inputPrincipalResidual B N ((B : ℝ)^rho) (by linarith) G)
          (fun N => blockInput B N + supportedPrincipalModel B N ((B : ℝ)^rho) G) k‖^2) ≤
        Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
          (Real.log (B : ℝ))^2 := by
  obtain ⟨CB,hCB,henergy⟩ := actual_supported_principal_energy_bound hc hd hGsupport
  obtain ⟨K,hK,henergyK⟩ := henergy (rho / 48) (by positivity)
  let Cv := 9 * ((1 + MG) / 2 + 3 * Real.pi) +
    (8 * (48 : ℝ)^8 * C) * (1 + 2 * MG) + (81 / 2) * MG
  let Crho := Cv^2 * (1 + CB * (∫ ξ : ℝ, tenthDecay ξ) * K)^2
  refine ⟨Crho, by dsimp [Crho]; positivity, ?_⟩
  intro B hB hR2 hlower hupper
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hR1 : 1 < (B : ℝ)^rho := by linarith
  have hRB : (B : ℝ)^rho ≤ (B : ℝ) :=
    upper_range_implies_R_le_B (B : ℝ) ((B : ℝ)^rho) hB1 hupper
  have hp := principal_residual_convolution_parseval_bound B hB
    ((B : ℝ)^rho) C hR1 hC hV hlower hupper G MG hMG hG hplateau
  dsimp only at hp
  have he := henergyK B (by omega) ((B : ℝ)^rho) hR2 hRB
  calc
    _ ≤ Cv^2 * (B : ℝ)^2 * ((B : ℝ)^rho)^(-(2 : ℝ) / 3) *
        ∑ N ∈ blockCarrier B,
          ‖blockInput B N + supportedPrincipalModel B N ((B : ℝ)^rho) G‖^2 := by
            simpa only [Cv] using hp
    _ ≤ Cv^2 * (B : ℝ)^2 * ((B : ℝ)^rho)^(-(2 : ℝ) / 3) *
        ((B : ℝ) *
          ((1 + CB * (∫ ξ : ℝ, tenthDecay ξ) * K) *
            (B : ℝ)^(rho / 48) * Real.log (B : ℝ))^2) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
        (Real.log (B : ℝ))^2 := by
      dsimp [Crho]
      calc
        _ = Cv^2 * (1 + CB * (∫ ξ : ℝ, tenthDecay ξ) * K)^2 *
            (B : ℝ)^3 *
            (((B : ℝ)^rho)^(-(2 : ℝ) / 3) *
              ((B : ℝ)^(rho / 48))^2) *
            (Real.log (B : ℝ))^2 := by ring
        _ = _ := by
          rw [residual_energy_power_identity B (by omega) rho]

/-- Separate active residual moment.  Its constant is uniform in the retained
`b` and character slot, and no active reserve is inferred. -/
theorem actual_active_residual_moment_power_bound {G : ℝ → ℝ}
    (hc : HasCompactSupport G) (hd : ContDiff ℝ ∞ G)
    (hGsupport : ∀ t : ℝ, 2 < t → G t = 0)
    (C MG rho : ℝ) (hC : 0 ≤ C) (hV : RealVaughanEstimate C)
    (hMG : 0 ≤ MG) (hG : ∀ u : ℝ, |G u| ≤ MG)
    (hplateau : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → G u = 1)
    (hrho : 0 < rho) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ ∀ (B : ℕ) (_hB : 6 ≤ B),
      ∀ (_hR2 : 2 ≤ (B : ℝ)^rho),
      Real.exp (Real.sqrt (Real.log (B : ℝ))) ≤ (B : ℝ)^rho →
      (B : ℝ)^rho ≤ (B : ℝ)^((1 : ℝ) / 10000) →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      ∀ e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊,
      (∑ k ∈ Finset.Icc (0 : ℤ) (2 * B : ℕ),
        ‖integerPairConvolution (blockCarrier B)
          (fun N => inputActiveResidual B N ((B : ℝ)^rho) (by linarith) b G e)
          (fun N => blockInput B N +
            supportedAdjustedModel B N ((B : ℝ)^rho) b G e) k‖^2) ≤
        Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
          (Real.log (B : ℝ))^2 := by
  obtain ⟨CB,hCB,henergy⟩ := actual_supported_adjusted_energy_bound hc hd hGsupport
  obtain ⟨K,hK,henergyK⟩ := henergy (rho / 48) (by positivity)
  let Cv := 9 * ((1 + MG) / 2 + 3 * Real.pi) +
    (8 * (48 : ℝ)^8 * C) * (1 + 2 * MG) + 46 * MG
  let Crho := Cv^2 * (1 + CB * (∫ ξ : ℝ, tenthDecay ξ) * K)^2
  refine ⟨Crho, by dsimp [Crho]; positivity, ?_⟩
  intro B hB hR2 hlower hupper b hb hb1 e
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hR1 : 1 < (B : ℝ)^rho := by linarith
  have hRB : (B : ℝ)^rho ≤ (B : ℝ) :=
    upper_range_implies_R_le_B (B : ℝ) ((B : ℝ)^rho) hB1 hupper
  have hp := active_residual_convolution_parseval_bound B hB
    ((B : ℝ)^rho) C hR1 hC hV hlower hupper b hb hb1
    G MG hMG hG hplateau e
  dsimp only at hp
  have he := henergyK B (by omega) ((B : ℝ)^rho) hR2 hRB b hb e
  calc
    _ ≤ Cv^2 * (B : ℝ)^2 * ((B : ℝ)^rho)^(-(2 : ℝ) / 3) *
        ∑ N ∈ blockCarrier B,
          ‖blockInput B N + supportedAdjustedModel B N ((B : ℝ)^rho) b G e‖^2 := by
            simpa only [Cv] using hp
    _ ≤ Cv^2 * (B : ℝ)^2 * ((B : ℝ)^rho)^(-(2 : ℝ) / 3) *
        ((B : ℝ) *
          ((1 + CB * (∫ ξ : ℝ, tenthDecay ξ) * K) *
            (B : ℝ)^(rho / 48) * Real.log (B : ℝ))^2) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = Crho * (B : ℝ)^3 * ((B : ℝ)^rho)^(-(5 : ℝ) / 8) *
        (Real.log (B : ℝ))^2 := by
      dsimp [Crho]
      calc
        _ = Cv^2 * (1 + CB * (∫ ξ : ℝ, tenthDecay ξ) * K)^2 *
            (B : ℝ)^3 *
            (((B : ℝ)^rho)^(-(2 : ℝ) / 3) *
              ((B : ℝ)^(rho / 48))^2) *
            (Real.log (B : ℝ))^2 := by ring
        _ = _ := by
          rw [residual_energy_power_identity B (by omega) rho]

end GoldbachCircleMethodActualResidualMomentCompositionV18193
