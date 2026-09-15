import GoldbachCircleMethodCentralPartnerUniformEnergyV18456
import GoldbachCircleMethodSupportedCompanionEnergyV18192
import GoldbachCircleMethodCanonicalBumpResidualMomentsV18222

/-!
# Goldbach V1.8.457: actual central partner amplitude

The uniform amplitude left open in V1.8.456 is now supplied from the actual
canonical bump, the proved radical majorant, and the standard finite divisor
subpower theorem already kernelized in V1.8.191.

The resulting central partner energy has the expected quadratic block census
times a subpower/logarithmic amplitude.  This does not estimate the independent
adjusted source energy and therefore does not prove Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical ContDiff
open MeasureTheory

namespace GoldbachCircleMethodCentralPartnerActualAmplitudeV18457

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalBumpResidualMomentsV18222
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodCentralPartnerUniformEnergyV18456
open GoldbachCircleMethodDivisorSubpowerExistenceV18191
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodSupportedCompanionEnergyV18192
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The actual pointwise amplitude inherited from the proved divisor/radical
envelope for the fixed canonical bump. -/
noncomputable def canonicalPartnerAmplitude
    (B : ℕ) (eps K CB : ℝ) : ℝ :=
  (1 + CB * (∫ ξ : ℝ, tenthDecay ξ) * K) *
    (B : ℝ) ^ eps * Real.log (B : ℝ)

theorem canonicalPartnerAmplitude_nonneg
    (B : ℕ) (eps K CB : ℝ) (hK : 0 ≤ K) (hCB : 0 ≤ CB) :
    0 ≤ canonicalPartnerAmplitude B eps K CB := by
  unfold canonicalPartnerAmplitude
  have hI : 0 ≤ ∫ ξ : ℝ, tenthDecay ξ :=
    integral_nonneg tenthDecay_nonneg
  positivity

/-- Pointwise actual partner-amplitude bound, including the zero branch when
the reflected argument leaves the supported block. -/
theorem adjusted_partner_norm_le_canonical_amplitude_of_divisor_bound
    (B N n : ℕ) (hB : 2 ≤ B) (rho eps K CB b : ℝ)
    (hR : 2 ≤ (B : ℝ) ^ rho) (hRB : (B : ℝ) ^ rho ≤ (B : ℝ))
    (heps : 0 < eps) (hK : 1 ≤ K) (hCB : 0 ≤ CB)
    (hdiv : ∀ u : ℕ, 0 < u →
      (u.divisors.card : ℝ) ≤ K * (u : ℝ) ^ eps)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (hmodel : ∀ u : ℕ,
      ‖supportedAdjustedModel B u ((B : ℝ) ^ rho) b canonicalLogBump e‖ ≤
        CB * radicalMajorant ((B : ℝ) ^ rho) u) :
    adjustedCorrectionPartnerNorm B N n rho b e ≤
      canonicalPartnerAmplitude B eps K CB := by
  let u : ℕ := N - n
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hR1 : 1 < (B : ℝ) ^ rho := by linarith
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by linarith)
  have hlogR : 0 ≤ Real.log ((B : ℝ) ^ rho) := (Real.log_pos hR1).le
  have hlogRB : Real.log ((B : ℝ) ^ rho) ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by linarith) hRB
  have hI : 0 ≤ ∫ ξ : ℝ, tenthDecay ξ :=
    integral_nonneg tenthDecay_nonneg
  have hpow : 1 ≤ (B : ℝ) ^ eps :=
    Real.one_le_rpow (by linarith) heps.le
  have hKn : 0 ≤ K := by linarith
  by_cases hu : u ∈ blockCarrier B
  · have hu' : B / 2 < u ∧ u ≤ B := by
      simpa only [blockCarrier, Finset.mem_Ioc] using hu
    have hup : 0 < u := by omega
    have hur : (0 : ℝ) < u := by exact_mod_cast hup
    have huB : (u : ℝ) ≤ B := by exact_mod_cast hu'.2
    have htau : (u.divisors.card : ℝ) ≤ K * (B : ℝ) ^ eps :=
      (hdiv u hup).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hur.le huB heps.le) hKn)
    have hr := radicalMajorant_le_divisor_mass hR1 u
    have hr' : radicalMajorant ((B : ℝ) ^ rho) u ≤
        K * (B : ℝ) ^ eps * Real.log (B : ℝ) *
          (∫ ξ : ℝ, tenthDecay ξ) := by
      apply hr.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul htau hlogRB hlogR (by positivity)) hI
    have ha : ‖blockInput B u‖ ≤ Real.log (B : ℝ) :=
      (blockInput_norm_le_vonMangoldt B u).trans
        (ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log hur huB))
    have hm : ‖supportedAdjustedModel B u ((B : ℝ) ^ rho) b canonicalLogBump e‖ ≤
        CB * (K * (B : ℝ) ^ eps * Real.log (B : ℝ) *
          (∫ ξ : ℝ, tenthDecay ξ)) :=
      (hmodel u).trans (mul_le_mul_of_nonneg_left hr' hCB)
    unfold adjustedCorrectionPartnerNorm
    change ‖blockInput B u‖ +
        ‖supportedAdjustedModel B u ((B : ℝ) ^ rho) b canonicalLogBump e‖ ≤ _
    calc
      _ ≤ Real.log (B : ℝ) +
          CB * (K * (B : ℝ) ^ eps * Real.log (B : ℝ) *
            (∫ ξ : ℝ, tenthDecay ξ)) := add_le_add ha hm
      _ ≤ canonicalPartnerAmplitude B eps K CB := by
        unfold canonicalPartnerAmplitude
        nlinarith [mul_le_mul_of_nonneg_right hpow hlogB]
  · have hinput : blockInput B u = 0 := by
      unfold blockInput
      rw [if_neg hu]
    have huIoc : u ∉ Finset.Ioc (B / 2) B := by
      simpa only [blockCarrier] using hu
    have hmodelZero :
        supportedAdjustedModel B u ((B : ℝ) ^ rho) b canonicalLogBump e = 0 := by
      unfold supportedAdjustedModel
      rw [dif_pos hR1, if_neg huIoc]
    unfold adjustedCorrectionPartnerNorm
    change ‖blockInput B u‖ +
        ‖supportedAdjustedModel B u ((B : ℝ) ^ rho) b canonicalLogBump e‖ ≤ _
    rw [hinput, hmodelZero, norm_zero, zero_add]
    exact canonicalPartnerAmplitude_nonneg B eps K CB hKn hCB

/-- Fully instantiated actual partner-energy bound for the fixed canonical
bump.  The constants are chosen before the block, target and active slot. -/
theorem actual_central_partner_energy_bound :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ eps : ℝ, 0 < eps →
      ∃ K : ℝ, 1 ≤ K ∧ ∀ (m : ℕ), 1 ≤ m →
        ∀ (rho b : ℝ), 2 ≤ ((8 * m : ℕ) : ℝ) ^ rho →
        ((8 * m : ℕ) : ℝ) ^ rho ≤ ((8 * m : ℕ) : ℝ) →
        0 ≤ b →
        ∀ (e : StructurallyAdmissibleActiveSlot
          ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊),
        centralAdjustedPartnerEnergy m rho b e ≤
          ((8 * m : ℕ) : ℝ) ^ 2 *
            (canonicalPartnerAmplitude (8 * m) eps K CB) ^ 2 := by
  obtain ⟨CB, hCB, hmodel⟩ := supported_adjustedModel_radical_bound
    canonicalLogBump_hasCompactSupport canonicalLogBump_contDiff
    (fun _t ht => canonicalLogBump_zero_above_two ht)
  refine ⟨CB, hCB, ?_⟩
  intro eps heps
  obtain ⟨K, hK, hdiv⟩ := exists_divisors_card_le_const_mul_rpow heps
  refine ⟨K, hK, ?_⟩
  intro m hm rho b hR hRB hb e
  apply central_partner_energy_le_block_sq_mul_amplitude_sq m hm
  intro i hi n hn
  exact adjusted_partner_norm_le_canonical_amplitude_of_divisor_bound
    (8 * m) (centralTargetNat m i) n (by omega) rho eps K CB b
    hR hRB heps hK hCB hdiv e.val
    (fun u => hmodel (((8 * m : ℕ) : ℝ) ^ rho) hR
      (8 * m) u b hb e.val)

end GoldbachCircleMethodCentralPartnerActualAmplitudeV18457
