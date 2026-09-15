import GoldbachCircleMethodActualQ3ExplicitPrefixSqrtEnvelopeV18762

/-!
# V1.8.763: q=3 small-prefix envelope in project normalization

The source-matched `3.49 * sqrt M` prefix ceiling from V1.8.762 is inserted
into the literal project envelope.  At the fixed schedule
`R = ceil(log(M)^10)`, `P = 8 R^2`, the kernel derives a conservative
`2300 * chebyshevConstant * log(M)^21 * sqrt(M)` majorant.

The final theorem closes the q=3 branch only under an explicit signed-reserve
floor and an explicit finite scale inequality.  Neither is asserted here.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology

namespace GoldbachCircleMethodActualQ3SmallPrefixProjectAbsorptionV18763

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualLambdaPairSourceMeanChebyshevBoundV18719
open GoldbachCircleMethodChebyshevEnergyBudgetV1889
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
open GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756
open GoldbachCircleMethodActualQ3ExplicitPrefixSqrtEnvelopeV18762

/-- Conservative normalized majorant after substituting the project schedule
and the source-matched square-root prefix ceiling. -/
noncomputable def actualQ3SmallPrefixProjectMajorant (M : Nat) : Real :=
  2300 * chebyshevConstant * Real.log (M : Real) ^ 21 *
    Real.sqrt (M : Real)

theorem oddProjectWidth_le_log20
    (M : Nat) (hlog : 1 ≤ Real.log (M : Real)) :
    (oddProjectWidth M : Real) ≤
      32 * Real.log (M : Real) ^ 20 := by
  have hR := (ceil_power_bounds (Real.log (M : Real)) hlog 10).2
  change (oddProjectRadius M : Real) ≤
    2 * Real.log (M : Real) ^ 10 at hR
  have hR2 : (oddProjectRadius M : Real) ^ 2 ≤
      (2 * Real.log (M : Real) ^ 10) ^ 2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hR 2
  unfold oddProjectWidth cubicModelScale
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    8 * (oddProjectRadius M : Real) ^ 2 ≤
        8 * (2 * Real.log (M : Real) ^ 10) ^ 2 := by
      gcongr
    _ = 32 * Real.log (M : Real) ^ 20 := by
      rw [mul_pow]
      rw [show (Real.log (M : Real) ^ 10) ^ 2 =
          Real.log (M : Real) ^ 20 by rw [← pow_mul]]
      ring

/-- Exact project-scale bound.  The hypothesis `log M <= sqrt M` is retained
as a visible finite threshold condition. -/
theorem actualQ3UnitDifferenceScaleEnvelope_smallPrefix_le_majorant
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hq : q.val.val = 3)
    (hlog : 1 ≤ Real.log (M : Real))
    (hLogSqrt : Real.log (M : Real) ≤ Real.sqrt (M : Real)) :
    actualQ3UnitDifferenceScaleEnvelope M q
        ((349 / 100 : Real) * Real.sqrt (M : Real) +
          Real.log (M : Real)) ≤
      actualQ3SmallPrefixProjectMajorant M := by
  have hm : (0 : Real) < M := by exact_mod_cast hM
  have hmne : (M : Real) ≠ 0 := hm.ne'
  have hqR : (q.val.val : Real) = 3 := by exact_mod_cast hq
  have hW := oddProjectWidth_le_log20 M hlog
  have hlog0 : 0 ≤ Real.log (M : Real) := le_trans (by norm_num) hlog
  have hlogTwo : 1 + Real.log (M : Real) ≤
      2 * Real.log (M : Real) := by linarith
  have hD :
      (349 / 100 : Real) * Real.sqrt (M : Real) +
          Real.log (M : Real) ≤
        (449 / 100 : Real) * Real.sqrt (M : Real) := by
    linarith
  have hWeight :
      (oddProjectWidth M : Real) * (1 + Real.log (M : Real)) ≤
        (32 * Real.log (M : Real) ^ 20) *
          (2 * Real.log (M : Real)) := by
    exact mul_le_mul hW hlogTwo (by positivity) (by positivity)
  have hWeighted :
      (8 * chebyshevConstant) *
          ((oddProjectWidth M : Real) * (1 + Real.log (M : Real))) ≤
        (8 * chebyshevConstant) *
          ((32 * Real.log (M : Real) ^ 20) *
            (2 * Real.log (M : Real))) := by
    exact mul_le_mul_of_nonneg_left hWeight
      (mul_nonneg (by norm_num) chebyshevConstant_pos.le)
  have hD0 : 0 ≤
      (349 / 100 : Real) * Real.sqrt (M : Real) +
        Real.log (M : Real) := by positivity
  have hBigWeighted0 : 0 ≤
      (8 * chebyshevConstant) *
        ((32 * Real.log (M : Real) ^ 20) *
          (2 * Real.log (M : Real))) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) chebyshevConstant_pos.le)
      (mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg hlog0 20))
        (mul_nonneg (by norm_num) hlog0))
  have hProduct := mul_le_mul hWeighted hD hD0 hBigWeighted0
  have hEnvelopeEq :
      actualQ3UnitDifferenceScaleEnvelope M q
          ((349 / 100 : Real) * Real.sqrt (M : Real) +
            Real.log (M : Real)) =
        8 * chebyshevConstant * (oddProjectWidth M : Real) *
          (1 + Real.log (M : Real)) *
          ((349 / 100 : Real) * Real.sqrt (M : Real) +
            Real.log (M : Real)) := by
    unfold actualQ3UnitDifferenceScaleEnvelope
    rw [hqR]
    field_simp
    ring
  rw [hEnvelopeEq]
  calc
    8 * chebyshevConstant * (oddProjectWidth M : Real) *
          (1 + Real.log (M : Real)) *
          ((349 / 100 : Real) * Real.sqrt (M : Real) +
            Real.log (M : Real)) ≤
        8 * chebyshevConstant *
          (32 * Real.log (M : Real) ^ 20) *
          (2 * Real.log (M : Real)) *
          ((449 / 100 : Real) * Real.sqrt (M : Real)) := by
      simpa only [mul_assoc] using hProduct
    _ ≤ actualQ3SmallPrefixProjectMajorant M := by
      unfold actualQ3SmallPrefixProjectMajorant
      have hc := chebyshevConstant_pos.le
      have hs := Real.sqrt_nonneg (M : Real)
      have hp : 0 ≤ Real.log (M : Real) ^ 21 := pow_nonneg hlog0 21
      calc
        8 * chebyshevConstant *
              (32 * Real.log (M : Real) ^ 20) *
              (2 * Real.log (M : Real)) *
              ((449 / 100 : Real) * Real.sqrt (M : Real)) =
            (229888 / 100 : Real) * chebyshevConstant *
              Real.log (M : Real) ^ 21 * Real.sqrt (M : Real) := by
                ring
        _ ≤ 2300 * chebyshevConstant *
              Real.log (M : Real) ^ 21 * Real.sqrt (M : Real) := by
                gcongr
                norm_num

/-- A transparent finite criterion for strict absorption of the explicit
project majorant by a linear reserve `rho*M`. -/
theorem actualQ3SmallPrefixProjectMajorant_lt_linear
    (M : Nat) (hM : 0 < M) (rho : Real)
    (hScale : 2300 * chebyshevConstant *
        Real.log (M : Real) ^ 21 <
      rho * Real.sqrt (M : Real)) :
    actualQ3SmallPrefixProjectMajorant M < rho * (M : Real) := by
  have hm : (0 : Real) < M := by exact_mod_cast hM
  have hs : 0 < Real.sqrt (M : Real) := Real.sqrt_pos.mpr hm
  have hs2 : Real.sqrt (M : Real) * Real.sqrt (M : Real) =
      (M : Real) := Real.mul_self_sqrt hm.le
  unfold actualQ3SmallPrefixProjectMajorant
  calc
    2300 * chebyshevConstant * Real.log (M : Real) ^ 21 *
          Real.sqrt (M : Real) <
        (rho * Real.sqrt (M : Real)) * Real.sqrt (M : Real) :=
      mul_lt_mul_of_pos_right hScale hs
    _ = rho * (M : Real) := by
      rw [mul_assoc, hs2]

/-- Fully composed finite-range q=3 gate.  The theorem does not manufacture
the external source estimate or the signed reserve floor. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_smallPrefixScale
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hSource : BennettMartinOBryantRechnitzerQ3SmallPrefixBound M)
    (rho : Real)
    (hlog : 1 ≤ Real.log (M : Real))
    (hLogSqrt : Real.log (M : Real) ≤ Real.sqrt (M : Real))
    (hScale : 2300 * chebyshevConstant *
        Real.log (M : Real) ^ 21 <
      rho * Real.sqrt (M : Real))
    (hReserve : rho * (M : Real) ≤
      actualQ3PrefixLocalDensityProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  apply projectReserve_add_negativeAggregate_re_pos_of_smallPrefixSource
    M hM q n hTarget hq hSource
  exact lt_of_le_of_lt
    (actualQ3UnitDifferenceScaleEnvelope_smallPrefix_le_majorant
      M hM q hq hlog hLogSqrt)
    ((actualQ3SmallPrefixProjectMajorant_lt_linear M hM rho hScale).trans_le
      hReserve)

end GoldbachCircleMethodActualQ3SmallPrefixProjectAbsorptionV18763
