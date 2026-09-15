import GoldbachCircleMethodCentralPartnerActualAmplitudeV18457

/-!
# Goldbach V1.8.458: polynomial envelope for the actual partner energy

The logarithm in the actual canonical partner amplitude is absorbed into an
arbitrarily small positive power.  This exposes the partner-energy exponent
`2 + 2 * (eps + eta)` and therefore the exact complementary exponent required
from the independent adjusted source energy.

No source-energy estimate is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCentralPartnerPolynomialEnvelopeV18458

open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodCentralPartnerActualAmplitudeV18457
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

noncomputable def canonicalPartnerPolynomialConstant
    (eta K CB : ℝ) : ℝ :=
  ((1 + CB *
      (∫ ξ : ℝ, GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155.tenthDecay ξ) * K) /
    eta) ^ 2

theorem canonicalPartnerPolynomialConstant_nonneg (eta K CB : ℝ) :
    0 ≤ canonicalPartnerPolynomialConstant eta K CB := by
  unfold canonicalPartnerPolynomialConstant
  positivity

/-- Effective logarithm absorption in the actual canonical amplitude. -/
theorem canonical_partner_amplitude_le_polynomial
    (B : ℕ) (hB : 1 ≤ B) (eps eta K CB : ℝ)
    (heta : 0 < eta) (hK : 0 ≤ K) (hCB : 0 ≤ CB) :
    canonicalPartnerAmplitude B eps K CB ≤
      ((1 + CB *
          (∫ ξ : ℝ, GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155.tenthDecay ξ) * K) /
        eta) *
      (B : ℝ) ^ (eps + eta) := by
  let C : ℝ := 1 + CB *
    (∫ ξ : ℝ, GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155.tenthDecay ξ) * K
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hBR
  have hI : 0 ≤
      ∫ ξ : ℝ, GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155.tenthDecay ξ :=
    MeasureTheory.integral_nonneg
      GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155.tenthDecay_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg B) heta
  unfold canonicalPartnerAmplitude
  change C * (B : ℝ) ^ eps * Real.log (B : ℝ) ≤ _
  calc
    C * (B : ℝ) ^ eps * Real.log (B : ℝ) ≤
        C * (B : ℝ) ^ eps * ((B : ℝ) ^ eta / eta) :=
      mul_le_mul_of_nonneg_left hlog
        (by positivity)
    _ = (C / eta) * (B : ℝ) ^ (eps + eta) := by
      rw [Real.rpow_add hBpos]
      ring
    _ = _ := rfl

/-- The actual partner energy is polynomially bounded with exponent
`2 + 2*(eps+eta)`. -/
theorem central_partner_energy_le_polynomial
    (m : ℕ) (hm : 1 ≤ m) (rho b eps eta K CB : ℝ)
    (heta : 0 < eta) (hK : 0 ≤ K) (hCB : 0 ≤ CB)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hEnergy : centralAdjustedPartnerEnergy m rho b e ≤
      ((8 * m : ℕ) : ℝ) ^ 2 *
        (canonicalPartnerAmplitude (8 * m) eps K CB) ^ 2) :
    centralAdjustedPartnerEnergy m rho b e ≤
      canonicalPartnerPolynomialConstant eta K CB *
        ((8 * m : ℕ) : ℝ) ^ (2 + 2 * (eps + eta)) := by
  let B : ℝ := ((8 * m : ℕ) : ℝ)
  let C : ℝ := (1 + CB *
      (∫ ξ : ℝ, GoldbachCircleMethodBumpDecayRadicalEnvelopeV18155.tenthDecay ξ) * K) /
    eta
  have hBm : 1 ≤ 8 * m := by omega
  have hBpos : 0 < B := by
    dsimp [B]
    exact_mod_cast (show 0 < 8 * m by omega)
  have hAmp : canonicalPartnerAmplitude (8 * m) eps K CB ≤
      C * B ^ (eps + eta) := by
    simpa only [B, C] using
      canonical_partner_amplitude_le_polynomial
        (8 * m) hBm eps eta K CB heta hK hCB
  have hAmpNonneg : 0 ≤ canonicalPartnerAmplitude (8 * m) eps K CB :=
    canonicalPartnerAmplitude_nonneg (8 * m) eps K CB hK hCB
  have hAmpSq : (canonicalPartnerAmplitude (8 * m) eps K CB) ^ 2 ≤
      (C * B ^ (eps + eta)) ^ 2 :=
    pow_le_pow_left₀ hAmpNonneg hAmp 2
  calc
    centralAdjustedPartnerEnergy m rho b e ≤
        B ^ 2 * (canonicalPartnerAmplitude (8 * m) eps K CB) ^ 2 := by
      simpa only [B] using hEnergy
    _ ≤ B ^ 2 * (C * B ^ (eps + eta)) ^ 2 :=
      mul_le_mul_of_nonneg_left hAmpSq (sq_nonneg B)
    _ = C ^ 2 * (B ^ (2 : ℕ) * (B ^ (eps + eta)) ^ (2 : ℕ)) := by ring
    _ = C ^ 2 * (B ^ (2 : ℕ) * B ^ ((eps + eta) * 2)) := by
      rw [(Real.rpow_mul_natCast hBpos.le (eps + eta) 2).symm]
      norm_num
    _ = C ^ 2 * (B ^ (2 : ℝ) * B ^ ((eps + eta) * 2)) := by
      exact congrArg
        (fun z : ℝ => C ^ 2 * (z * B ^ ((eps + eta) * 2)))
        (Real.rpow_natCast B 2).symm
    _ = C ^ 2 * B ^ ((2 : ℝ) + (eps + eta) * 2) := by
      rw [Real.rpow_add hBpos]
    _ = C ^ 2 * B ^ (2 + 2 * (eps + eta)) := by
      congr 2
      ring
    _ = canonicalPartnerPolynomialConstant eta K CB *
        ((8 * m : ℕ) : ℝ) ^ (2 + 2 * (eps + eta)) := by
      rfl

end GoldbachCircleMethodCentralPartnerPolynomialEnvelopeV18458
