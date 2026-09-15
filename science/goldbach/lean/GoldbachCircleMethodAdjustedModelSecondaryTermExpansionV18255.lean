import GoldbachCircleMethodAdjustedCenteredCorrectionNumericAbsorptionV18254

/-!
# Goldbach V1.8.255: adjusted-model secondary-term expansion

The adjusted model is split definitionally into the conductor-one principal
model and one explicit active-character term.  Its self-convolution is then
expanded exactly.  This isolates the reserve obligation without assigning a
sign to the secondary term.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodAdjustedModelSecondaryTermExpansionV18255

open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodSupportedModelErrorConvolutionV18182
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActualResidualExactDecompositionV18225
open GoldbachCircleMethodActiveResidualExactDecompositionV18251

/-- The single supported active-character term subtracted from the principal
model.  This is a slot parameter only; no exceptional-zero claim is made. -/
noncomputable def supportedActiveSecondaryTerm
    (M N : ℕ) (R b : ℝ) (G : ℝ → ℝ)
    (e : CharacterSlot ⌊R^2⌋₊) : ℂ :=
  if _hR : 1 < R then
    if N ∈ Finset.Ioc (M / 2) M then
      windowCoefficient e.1 N (logWeight R G) e.2 * (powerWeight b N : ℂ)
    else 0
  else 0

/-- Global supported identity, including the off-carrier and invalid-scale
branches. -/
theorem supportedAdjustedModel_eq_principal_sub_secondary
    (M N : ℕ) (R b : ℝ) (G : ℝ → ℝ)
    (e : CharacterSlot ⌊R^2⌋₊) :
    supportedAdjustedModel M N R b G e =
      supportedPrincipalModel M N R G -
        supportedActiveSecondaryTerm M N R b G e := by
  unfold supportedAdjustedModel supportedPrincipalModel supportedActiveSecondaryTerm
  by_cases hR : 1 < R
  · simp only [hR, dif_pos]
    by_cases hN : N ∈ Finset.Ioc (M / 2) M
    · simp only [hN, if_true]
      rfl
    · simp only [hN, if_false, sub_zero]
  · simp [hR]

/-- Exact subtraction in the second convolution input. -/
theorem integerPairConvolution_sub_right
    (J : Finset ℕ) (v w z : ℕ → ℂ) (k : ℤ) :
    integerPairConvolution J v (fun n => w n - z n) k =
      integerPairConvolution J v w k - integerPairConvolution J v z k := by
  rw [integerPairConvolution_comm J v (fun n => w n - z n) k,
    integerPairConvolution_sub_left J w z v k,
    integerPairConvolution_comm J w v k,
    integerPairConvolution_comm J z v k]

/-- Exact self-convolution expansion `(p-z)^2 = p^2-2pz+z^2`. -/
theorem integerPairConvolution_sub_self_expansion
    (J : Finset ℕ) (p z : ℕ → ℂ) (k : ℤ) :
    integerPairConvolution J (fun n => p n - z n)
        (fun n => p n - z n) k =
      integerPairConvolution J p p k -
        2 * integerPairConvolution J p z k +
        integerPairConvolution J z z k := by
  rw [integerPairConvolution_sub_left,
    integerPairConvolution_sub_right,
    integerPairConvolution_sub_right,
    integerPairConvolution_comm J z p k]
  ring

/-- Cross term between the principal model and active secondary term. -/
noncomputable def canonicalPrincipalSecondaryCrossAt
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (k : ℤ) : ℂ :=
  integerPairConvolution (blockCarrier B)
    (fun N => supportedPrincipalModel B N ((B : ℝ)^rho) canonicalLogBump)
    (fun N => supportedActiveSecondaryTerm B N ((B : ℝ)^rho)
      b canonicalLogBump e) k

/-- Self-convolution of the active secondary term. -/
noncomputable def canonicalActiveSecondarySquareAt
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (k : ℤ) : ℂ :=
  integerPairConvolution (blockCarrier B)
    (fun N => supportedActiveSecondaryTerm B N ((B : ℝ)^rho)
      b canonicalLogBump e)
    (fun N => supportedActiveSecondaryTerm B N ((B : ℝ)^rho)
      b canonicalLogBump e) k

/-- Exact adjusted-model expansion.  The cross and square terms are not
assigned a sign or bounded by this theorem. -/
theorem canonicalAdjustedModelAt_eq_principal_sub_cross_add_secondarySquare
    (B : ℕ) (rho b : ℝ)
    (e : CharacterSlot ⌊((B : ℝ)^rho)^2⌋₊) (k : ℤ) :
    canonicalAdjustedModelAt B rho b e k =
      canonicalPrincipalModelAt B rho k -
        2 * canonicalPrincipalSecondaryCrossAt B rho b e k +
        canonicalActiveSecondarySquareAt B rho b e k := by
  unfold canonicalAdjustedModelAt canonicalPrincipalModelAt
  unfold canonicalPrincipalSecondaryCrossAt canonicalActiveSecondarySquareAt
  simp_rw [supportedAdjustedModel_eq_principal_sub_secondary]
  exact integerPairConvolution_sub_self_expansion
    (blockCarrier B)
    (fun N => supportedPrincipalModel B N ((B : ℝ)^rho) canonicalLogBump)
    (fun N => supportedActiveSecondaryTerm B N ((B : ℝ)^rho)
      b canonicalLogBump e) k

end GoldbachCircleMethodAdjustedModelSecondaryTermExpansionV18255
