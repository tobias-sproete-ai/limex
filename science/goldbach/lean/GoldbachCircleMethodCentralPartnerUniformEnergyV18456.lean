import GoldbachCircleMethodCentralL2SubcriticalWitnessV18455

/-!
# Goldbach V1.8.456: central partner-energy census

This module separates the combinatorial size of the central partner energy
from its pointwise arithmetic amplitude.  It proves that a uniform amplitude
bound costs one block factor for the source carrier and one for the target
sweep.  Thus the partner energy is quadratically scaled before any analytic
gain is supplied.

No pointwise arithmetic amplitude bound is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCentralPartnerUniformEnergyV18456

open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- A uniform pointwise partner amplitude controls one target's exact energy
by the cardinality of the source block. -/
theorem adjusted_partner_energy_le_block_mul_amplitude_sq
    (B N : ℕ) (rho b A : ℝ)
    (e : CharacterSlot ⌊((B : ℝ) ^ rho) ^ 2⌋₊)
    (hpoint : ∀ n ∈ blockCarrier B,
      adjustedCorrectionPartnerNorm B N n rho b e ≤ A) :
    adjustedCorrectionPartnerEnergy B N rho b e ≤ (B : ℝ) * A ^ 2 := by
  have hcard :
      (blockCarrier B).card ≤ B := by
    simp only [blockCarrier, Nat.card_Ioc]
    exact Nat.sub_le _ _
  unfold adjustedCorrectionPartnerEnergy
  calc
    (∑ n ∈ blockCarrier B,
        adjustedCorrectionPartnerNorm B N n rho b e ^ 2) ≤
      ∑ _n ∈ blockCarrier B, A ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact pow_le_pow_left₀
          (by unfold adjustedCorrectionPartnerNorm; positivity)
          (hpoint n hn) 2
    _ = ((blockCarrier B).card : ℝ) *
        A ^ 2 := by simp
    _ ≤ (B : ℝ) * A ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg A)

/-- On the canonical central sweep, the same pointwise amplitude is counted
at most once per source/target pair, for a total quadratic block census. -/
theorem central_partner_energy_le_block_sq_mul_amplitude_sq
    (m : ℕ) (hm : 1 ≤ m) (rho b A : ℝ)
    (e : StructurallyAdmissibleActiveSlot
      ⌊(((8 * m : ℕ) : ℝ) ^ rho) ^ 2⌋₊)
    (hpoint : ∀ i ∈ Finset.range (2 * m + 1),
      ∀ n ∈ blockCarrier (8 * m),
        adjustedCorrectionPartnerNorm (8 * m)
          (centralTargetNat m i) n rho b e.val ≤ A) :
    centralAdjustedPartnerEnergy m rho b e ≤
      ((8 * m : ℕ) : ℝ) ^ 2 * A ^ 2 := by
  have htargetCard : ((2 * m + 1 : ℕ) : ℝ) ≤ ((8 * m : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * m + 1 ≤ 8 * m by omega)
  have hsingle (i : ℕ) (hi : i ∈ Finset.range (2 * m + 1)) :
      adjustedCorrectionPartnerEnergy
          (8 * m) (centralTargetNat m i) rho b e.val ≤
        ((8 * m : ℕ) : ℝ) * A ^ 2 :=
    adjusted_partner_energy_le_block_mul_amplitude_sq
      (8 * m) (centralTargetNat m i) rho b A e.val (hpoint i hi)
  unfold centralAdjustedPartnerEnergy
  calc
    (∑ i ∈ Finset.range (2 * m + 1),
        adjustedCorrectionPartnerEnergy
          (8 * m) (centralTargetNat m i) rho b e.val) ≤
      ∑ _i ∈ Finset.range (2 * m + 1),
        ((8 * m : ℕ) : ℝ) * A ^ 2 :=
      Finset.sum_le_sum (fun i hi => hsingle i hi)
    _ = ((2 * m + 1 : ℕ) : ℝ) *
        (((8 * m : ℕ) : ℝ) * A ^ 2) := by simp
    _ ≤ ((8 * m : ℕ) : ℝ) *
        (((8 * m : ℕ) : ℝ) * A ^ 2) :=
      mul_le_mul_of_nonneg_right htargetCard (by positivity)
    _ = ((8 * m : ℕ) : ℝ) ^ 2 * A ^ 2 := by ring

end GoldbachCircleMethodCentralPartnerUniformEnergyV18456
