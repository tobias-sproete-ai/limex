import GoldbachCircleMethodCentralDivisorSubpowerClosedV18419
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Goldbach V1.8.420: exact exponent threshold for the central source gate

A literal character-family estimate with polynomial decay exponent `sigma`
absorbs the arithmetic divisor loss with exponent `eps` exactly when the
declared strict gap `eps < sigma` is available.  The module proves only this
scalar asymptotic implication; it does not prove the source estimate.

This isolates the remaining analytic target without big-O notation and leaves
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical Topology
open Filter

namespace GoldbachCircleMethodCentralSourceExponentAbsorptionV18420

/-- The base `14*m` tends to infinity along the natural numbers. -/
theorem tendsto_fourteen_mul_natCast_atTop :
    Tendsto (fun m : ℕ => ((14 * m : ℕ) : ℝ)) atTop atTop := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 14 by norm_num)

/-- A source decay `x^-sigma` absorbs a divisor loss `x^eps` for every strict
exponent gap `eps < sigma`, with all fixed nonnegative constants retained. -/
theorem source_power_decay_absorbs_divisor_subpower
    (CA CT Gamma eps sigma : ℝ)
    (hCA : 0 ≤ CA) (hCT : 0 ≤ CT) (hGamma : 0 ≤ Gamma)
    (hgap : eps < sigma) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (2 * (CA * ((14 * m : ℕ) : ℝ) ^ (-sigma))) *
          (CT * ((14 * m : ℕ) : ℝ) ^ eps) * Gamma <
        (1 : ℝ) / 2048 := by
  let K : ℝ := 2 * CA * CT * Gamma
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hdecay : Tendsto
      (fun m : ℕ => ((14 * m : ℕ) : ℝ) ^ (-(sigma - eps)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hgap)).comp
      tendsto_fourteen_mul_natCast_atTop
  have hlim : Tendsto
      (fun m : ℕ => K * ((14 * m : ℕ) : ℝ) ^ (-(sigma - eps)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  have hsmall : ∀ᶠ m : ℕ in atTop,
      K * ((14 * m : ℕ) : ℝ) ^ (-(sigma - eps)) < (1 : ℝ) / 2048 :=
    (tendsto_order.1 hlim).2 ((1 : ℝ) / 2048) (by norm_num)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall] with m hm hlt
  have hx : (0 : ℝ) < ((14 * m : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 14 * m by omega)
  have hrewrite :
      (2 * (CA * ((14 * m : ℕ) : ℝ) ^ (-sigma))) *
          (CT * ((14 * m : ℕ) : ℝ) ^ eps) * Gamma =
        K * ((14 * m : ℕ) : ℝ) ^ (-(sigma - eps)) := by
    rw [show -(sigma - eps) = -sigma + eps by ring]
    rw [Real.rpow_add hx]
    dsimp [K]
    ring
  rw [hrewrite]
  exact hlt

end GoldbachCircleMethodCentralSourceExponentAbsorptionV18420
