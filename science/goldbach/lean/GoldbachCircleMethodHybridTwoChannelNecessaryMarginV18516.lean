import GoldbachCircleMethodHybridTwoChannelEndToEndReductionV18515

/-!
# Goldbach V1.8.516: necessary margins for the hybrid two-channel gate

The source exponent inequality used by the verified witness transfer is not
compatible with a merely linear source bound.  This module records that
necessary condition as a kernel-checked negative witness.  It neither
inhabits either analytic estimate nor proves Goldbach.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodHybridTwoChannelNecessaryMarginV18516

/-- Any exponent admitted by the source gap is strictly sublinear. -/
theorem sourceGap_implies_sublinear
    (s eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta)
    (hgap : s + 2 * (eps + eta) < 1) :
    s < 1 := by
  linarith

/-- A linear-or-worse source exponent cannot pass the existing source gate. -/
theorem no_sourceGap_of_linear_exponent
    (s eps eta : ℝ) (hs : 1 ≤ s) (heps : 0 < eps) (heta : 0 < eta) :
    ¬ s + 2 * (eps + eta) < 1 := by
  intro hgap
  linarith

/-- The joint two-channel gate also forces the already isolated principal
discrepancy margin. -/
theorem jointGate_implies_principal_margin
    (rho sigma s eps eta : ℝ)
    (hprincipal : 1 + 4 * rho - 2 * sigma ≤ s)
    (hgap : s + 2 * (eps + eta) < 1) :
    2 * rho + eps + eta < sigma := by
  linarith

/-- Both necessary consequences exposed together. -/
theorem jointGate_necessary_conditions
    (rho sigma s eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta)
    (hprincipal : 1 + 4 * rho - 2 * sigma ≤ s)
    (hgap : s + 2 * (eps + eta) < 1) :
    s < 1 ∧ 2 * rho + eps + eta < sigma := by
  exact ⟨sourceGap_implies_sublinear s eps eta heps heta hgap,
    jointGate_implies_principal_margin rho sigma s eps eta hprincipal hgap⟩

end GoldbachCircleMethodHybridTwoChannelNecessaryMarginV18516
