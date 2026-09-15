import GoldbachCircleMethodHybridPrincipalBlockExponentV18511

/-!
# Goldbach V1.8.512: remaining hybrid-channel interfaces

The two source channels not closed by the centered-principal estimate are
declared as explicit parameter types.  They are not axioms and no inhabitant
is constructed here.  The channel bounds plus the principal estimate imply a
single hybrid source bound without hiding any component.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodHybridRemainingChannelInterfacesV18512

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCenteredPrincipalDecayInterfaceV18503
open GoldbachCircleMethodCenteredPrincipalNetExponentV18504
open GoldbachCircleMethodHybridCenteredCentralMomentV18505
open GoldbachCircleMethodHybridCenteredChannelBudgetSplitV18510
open GoldbachCircleMethodHybridPrincipalBlockExponentV18511

/-- Open analytic target for the genuinely nonprincipal primitive channel. -/
def NonprincipalPrimitiveBlockEstimate
    (Cn rho s : ℝ) : Prop :=
  ∀ (B : ℕ), 3 ≤ B →
    hybridNonprincipalBlockBudget B rho ≤ Cn * (B : ℝ) ^ s

/-- Open analytic target for the selected exceptional-character channel. -/
def ExceptionalCharacterBlockEstimate
    (Ce rho s : ℝ) : Prop :=
  ∀ (B : ℕ), 3 ≤ B →
    ∀ e : CharacterSlot (centeredPrincipalCutoff B rho),
    hybridExceptionalBlockBudget B rho e ≤ Ce * (B : ℝ) ^ s

/-- Three transparent channel estimates assemble into the single source gate.
The principal exponent may be smaller than the common target exponent `s`. -/
theorem hybridCenteredSourceBudget_le_of_channel_estimates
    (C Cn Ce rho sigma s : ℝ)
    (hC : 0 ≤ C)
    (hrho : 0 < rho)
    (hprincipal : CenteredPrincipalDiscrepancyEstimate C rho sigma)
    (hnonprincipal : NonprincipalPrimitiveBlockEstimate Cn rho s)
    (hexceptional : ExceptionalCharacterBlockEstimate Ce rho s)
    (hexponent : 1 + 4 * rho - 2 * sigma ≤ s)
    (B : ℕ) (hB : 3 ≤ B) (b : ℝ)
    (e : CharacterSlot (centeredPrincipalCutoff B rho)) :
    hybridCenteredSourceBudget B rho b e ≤
      (C ^ 2 + Cn + Ce) * (B : ℝ) ^ s := by
  have hbase : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hpower : (B : ℝ) ^ (1 + 4 * rho - 2 * sigma) ≤
      (B : ℝ) ^ s :=
    Real.rpow_le_rpow_of_exponent_le hbase hexponent
  have hpRaw := hybridPrincipalBlockBudget_le_net_power
    C rho sigma hC hrho hprincipal B hB
  have hp : hybridPrincipalBlockBudget B rho ≤
      C ^ 2 * (B : ℝ) ^ s :=
    hpRaw.trans (mul_le_mul_of_nonneg_left hpower (sq_nonneg C))
  have hn := hnonprincipal B hB
  have he := hexceptional B hB e
  rw [hybridCenteredSourceBudget_eq_channel_sum B rho b e]
  calc
    hybridPrincipalBlockBudget B rho +
          hybridNonprincipalBlockBudget B rho +
          hybridExceptionalBlockBudget B rho e ≤
        C ^ 2 * (B : ℝ) ^ s +
          Cn * (B : ℝ) ^ s + Ce * (B : ℝ) ^ s := by
      linarith
    _ = (C ^ 2 + Cn + Ce) * (B : ℝ) ^ s := by ring

/-- The assembled source constant is nonnegative whenever the three channel
constants are nonnegative. -/
theorem hybridSourceConstant_nonneg
    (C Cn Ce : ℝ) (hCn : 0 ≤ Cn) (hCe : 0 ≤ Ce) :
    0 ≤ C ^ 2 + Cn + Ce := by
  positivity

end GoldbachCircleMethodHybridRemainingChannelInterfacesV18512
