import GoldbachCircleMethodGlobalCollisionAbsoluteBoundV18576
import GoldbachCircleMethodHybridTwoChannelNecessaryMarginV18516

/-!
# Goldbach V1.8.577: global absolute collision-route obstruction

V1.8.576 exposes the literal global square cost `B^2 * Q^8` (up to the
declared nonnegative exponential, weight, and polylogarithmic factors).  Under
the already used scaling `Q ~ B^(2*rho)`, taking square roots therefore gives
the power exponent `1 + 8*rho`.  This module records only the arithmetic
incompatibility between that exponent and the verified strictly sublinear
source gate.

This is a method-specific negative witness.  It is not a lower bound for the
true collision residual, does not exclude cancellation between conductor
pairs, and does not prove or disprove Goldbach.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodGlobalCollisionAbsoluteRouteObstructionV18577

open GoldbachCircleMethodHybridTwoChannelNecessaryMarginV18516

/-- Power exponent obtained from the `B^2 * Q^8` global square envelope after
square-rooting and substituting the scale `Q ~ B^(2*rho)`. -/
def globalAbsoluteCollisionExponent (rho : ℝ) : ℝ :=
  1 + 8 * rho

/-- The global absolute-route exponent is linear or worse for every
nonnegative conductor-scale exponent. -/
theorem globalAbsoluteCollisionExponent_ge_one
    (rho : ℝ) (hrho : 0 ≤ rho) :
    1 ≤ globalAbsoluteCollisionExponent rho := by
  unfold globalAbsoluteCollisionExponent
  linarith

/-- A source estimate no better than the V1.8.576 global absolute exponent
cannot pass the existing strictly sublinear source gate. -/
theorem globalAbsoluteCollisionRoute_cannot_close_sourceGap
    (rho s eps eta : ℝ)
    (hrho : 0 ≤ rho)
    (hcost : globalAbsoluteCollisionExponent rho ≤ s)
    (heps : 0 < eps) (heta : 0 < eta) :
    ¬ s + 2 * (eps + eta) < 1 := by
  have hs : 1 ≤ s :=
    (globalAbsoluteCollisionExponent_ge_one rho hrho).trans hcost
  exact no_sourceGap_of_linear_exponent s eps eta hs heps heta

/-- For a genuinely growing conductor scale (`rho > 0`), the same exponent is
strictly superlinear.  This strengthens the route diagnosis without making a
claim about the size of the actual collision sum. -/
theorem globalAbsoluteCollisionExponent_gt_one
    (rho : ℝ) (hrho : 0 < rho) :
    1 < globalAbsoluteCollisionExponent rho := by
  unfold globalAbsoluteCollisionExponent
  linarith

end GoldbachCircleMethodGlobalCollisionAbsoluteRouteObstructionV18577
