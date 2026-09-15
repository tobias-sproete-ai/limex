import GoldbachCircleMethodOddOddSmallCoreLargePerturbationV18670

/-!
# V1.8.671: exact q>2 denominator-energy reduction

The literal large-denominator perturbation from V1.8.670 is decomposed into
its fixed-denominator components. A finite Cauchy inequality then reduces its
target-block square energy to the sum of the fixed-denominator square energies,
with the exact cardinality loss of the `q > 2` carrier.

This is an algebraic reduction only. No fixed-denominator energy estimate is
supplied, and the cardinality factor is not claimed to be harmless.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddOddSmallCoreLargePerturbationV18670
open GoldbachCircleMethodSignedMagnitudeIdentityV18628

namespace GoldbachCircleMethodOddOddLargeDenominatorEnergyReductionV18671

/-- Literal finite carrier of denominators strictly larger than two. -/
def largeDenominatorCarrier (R : Nat) :
    Finset (GoldbachCircleMethodOriginalMaskModelBindingV1859.Denominator R) :=
  Finset.univ.filter (fun q => 2 < q.val)

/-- Contribution of one fixed denominator to the signed large perturbation. -/
noncomputable def fixedLargeDenominatorPerturbation
    (M P R : Nat)
    (q : GoldbachCircleMethodOriginalMaskModelBindingV1859.Denominator R)
    (N : Nat) : Real :=
  -∑ t ∈ oddOddOffDiagonalSumCarrier M N,
    oddOddPairFiberMass M t *
      (explicitDenominatorSincTerm M P R ((N : Int) - (t : Int)) q).re

/-- Exact reindexing of the q>2 perturbation as a sum of fixed-denominator
components. No triangle inequality is used. -/
theorem largeDenominatorPerturbation_eq_sum_fixed
    (M P R N : Nat) :
    largeDenominatorPerturbation M P R N =
      ∑ q ∈ largeDenominatorCarrier R,
        fixedLargeDenominatorPerturbation M P R q N := by
  classical
  unfold largeDenominatorPerturbation largeDenominatorOddOddDeficit
    explicitLargeDenominatorSincKernel largeDenominatorCarrier
    fixedLargeDenominatorPerturbation
  simp_rw [Complex.re_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_neg_distrib]

/-- Finite Cauchy reduction for a sum of real-valued denominator channels. -/
theorem squareEnergy_sum_le_card_mul_sum_squareEnergy
    {ι κ : Type*} (s : Finset ι) (Q : Finset κ) (F : κ → ι → Real) :
    squareEnergy s (fun i => ∑ q ∈ Q, F q i) ≤
      (Q.card : Real) * ∑ q ∈ Q, squareEnergy s (F q) := by
  classical
  unfold squareEnergy
  calc
    (∑ i ∈ s, (∑ q ∈ Q, F q i) ^ 2) ≤
        ∑ i ∈ s, (Q.card : Real) * ∑ q ∈ Q, (F q i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact sq_sum_le_card_mul_sum_sq
    _ = (Q.card : Real) * ∑ q ∈ Q, ∑ i ∈ s, (F q i) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

/-- Exact project specialization. The right side is still an open arithmetic
quantity, now separated denominator by denominator. -/
theorem project_largePerturbation_energy_le_fixedDenominatorEnergies
    (M : Nat) :
    squareEnergy (evenTargetBlock M)
        (largeDenominatorPerturbation M
          (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectWidth M)
          (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M)) ≤
      ((largeDenominatorCarrier
          (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M)).card : Real) *
        ∑ q ∈ largeDenominatorCarrier
            (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M),
          squareEnergy (evenTargetBlock M)
            (fixedLargeDenominatorPerturbation M
              (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectWidth M)
              (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M) q) := by
  have hfun :
      largeDenominatorPerturbation M
          (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectWidth M)
          (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M) =
        fun N => ∑ q ∈ largeDenominatorCarrier
            (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M),
          fixedLargeDenominatorPerturbation M
            (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectWidth M)
            (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M) q N := by
    funext N
    exact largeDenominatorPerturbation_eq_sum_fixed M
      (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectWidth M)
      (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M) N
  rw [hfun]
  exact squareEnergy_sum_le_card_mul_sum_squareEnergy
    (evenTargetBlock M)
    (largeDenominatorCarrier
      (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M))
    (fixedLargeDenominatorPerturbation M
      (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectWidth M)
      (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M))

/-- Honest conditional discharge of the V1.8.670 large-perturbation premise.
The fixed-denominator aggregate bound remains visible. -/
theorem project_largePerturbation_energy_lt_of_fixedDenominatorBudget
    (M : Nat)
    (hFixed :
      ((largeDenominatorCarrier
          (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M)).card : Real) *
        ∑ q ∈ largeDenominatorCarrier
            (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M),
          squareEnergy (evenTargetBlock M)
            (fixedLargeDenominatorPerturbation M
              (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectWidth M)
              (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M) q) <
        (M : Real) ^ 2 / 50176) :
    squareEnergy (evenTargetBlock M)
        (largeDenominatorPerturbation M
          (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectWidth M)
          (GoldbachCircleMethodOddChannelEventualAbsorptionV18658.oddProjectRadius M)) <
      (M : Real) ^ 2 / 50176 :=
  (project_largePerturbation_energy_le_fixedDenominatorEnergies M).trans_lt hFixed

end GoldbachCircleMethodOddOddLargeDenominatorEnergyReductionV18671
