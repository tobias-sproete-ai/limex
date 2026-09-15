import GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
import GoldbachCircleMethodHybridAugmentedConductorTargetV18517

/-!
# Goldbach V1.8.521: nonprincipal conductor-sum envelope

The nonprincipal coefficient mass is reindexed exactly by conductor and then
bounded by the V1.8.520 conductor-local interval estimates.  All conductor
weights and diagonal energies remain explicit.  No power saving is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodNonprincipalConductorSumEnvelopeV18521

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodHybridAugmentedConductorTargetV18517
open GoldbachCircleMethodHybridCenteredCorrelationEnergyV18501
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodNonprincipalConductorIntervalEnergyV18520
open GoldbachCircleMethodPrincipalWindowBoundaryV18121

/-- Generic block coefficient mass on the literal nonprincipal support. -/
noncomputable def blockNonprincipalCoefficientMass
    (Q B : ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ n ∈ blockCarrier B, nonprincipalCoefficientEnergy Q n w

/-- Exact conductor reindexing.  Conductor one is removed by a literal zero;
all other primitive-character families remain unchanged. -/
theorem blockNonprincipalCoefficientMass_eq_conductor_sum
    (Q B : ℕ) (w : ℕ → ℂ) :
    blockNonprincipalCoefficientMass Q B w =
      ∑ r : PositiveLevel Q,
        if r.val = 1 then 0 else
          ∑ n ∈ blockCarrier B,
            ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
              ‖windowCoefficient r n w χ‖ ^ 2 := by
  unfold blockNonprincipalCoefficientMass nonprincipalCoefficientEnergy
  simp_rw [Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hprincipal : r.val = 1
  · simp [hprincipal]
  · simp [hprincipal]

/-- Summing the exact conductor-local bounds gives the finite nonprincipal
envelope.  This statement deliberately leaves the conductor sum visible: a
future source estimate must control it rather than hide it in cardinality. -/
theorem blockNonprincipalCoefficientMass_le_conductor_envelope
    (Q B : ℕ) (w : ℕ → ℂ)
    (hwReal : ∀ n : ℕ, star (w n) = w n)
    (V : ℝ) (hV : 0 ≤ V)
    (hwBound : ∀ (r q : PositiveLevel Q),
      r.val * q.val ≤ Q ∧ Nat.Coprime r.val q.val →
        ‖w (r.val * q.val)‖ ≤ V) :
    blockNonprincipalCoefficientMass Q B w ≤
      ∑ r : PositiveLevel Q,
        if r.val = 1 then 0 else
          primitiveFamilyScale r *
            (((B + 1 : ℕ) : ℝ) * (∑ q : PositiveLevel Q,
              ‖literalCoefficient r q w‖ ^ 2 *
                (q.val.totient : ℝ)) +
              2 * (Q : ℝ) ^ 4 * V * V) := by
  rw [blockNonprincipalCoefficientMass_eq_conductor_sum]
  apply Finset.sum_le_sum
  intro r _hr
  by_cases hprincipal : r.val = 1
  · simp [hprincipal]
  · simp only [hprincipal, if_false]
    exact primitive_windowCoefficient_block_energy_le
      r B w hwReal V hV (hwBound r)

/-- The canonical hybrid mass from V1.8.517 is definitionally the generic
mass at the centered cutoff and canonical logarithmic weight. -/
theorem hybridNonprincipalCoefficientMass_eq_blockMass
    (B : ℕ) (rho : ℝ) :
    hybridNonprincipalCoefficientMass B rho =
      blockNonprincipalCoefficientMass
        (GoldbachCircleMethodCenteredPrincipalNetExponentV18504.centeredPrincipalCutoff
          B rho)
        B
        (logWeight ((B : ℝ) ^ rho)
          GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220.canonicalLogBump) := by
  rfl

end GoldbachCircleMethodNonprincipalConductorSumEnvelopeV18521
