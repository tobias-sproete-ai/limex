import GoldbachCircleMethodActualQ3ScaleProjectAbsorptionV18766

/-!
# V1.8.767: full conditional closure of the actual q=3 project branch

The source-matched fixed-modulus distribution input, the elementary prefix
split, the project-scale absorption, and an explicitly named signed-reserve
floor are composed without changing any carrier.

The scale estimate and the signed-reserve floor are open propositions.  Their
conditional composition is not a proof of Goldbach.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology

namespace GoldbachCircleMethodActualQ3FullConditionalClosureV18767

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformMajorPrefixReductionV1865
open GoldbachCircleMethodUniformResidueInputBridgeV1869
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
open GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756
open GoldbachCircleMethodActualQ3FullCharacterPartialSumNormalizationV18759
open GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760
open GoldbachCircleMethodActualQ3ScaleCombinedPrefixEnvelopeV18765
open GoldbachCircleMethodActualQ3ScaleProjectAbsorptionV18766

/-- The remaining signed local-density input, stated as a uniform eventual
linear floor on the literal q=3 project reserve. -/
def EventualActualQ3PrefixLocalDensityReserveFloor (rho : Real) : Prop :=
  ∀ᶠ M : Nat in atTop,
    ∀ q : PairedOddBase (oddProjectRadius M),
      ∀ n : Nat, 2 * n ∈ evenTargetBlock M → q.val.val = 3 →
        rho * (M : Real) ≤
          actualQ3PrefixLocalDensityProjectReserve M q n

/-- The elementary size conditions required by the q=3 scale bridge hold at
all sufficiently large project scales. -/
theorem eventually_actualQ3_scale_prerequisites (k₀ : Nat) :
    ∀ᶠ M : Nat in atTop,
      0 < M ∧
      (2 : Real) ^ 12 ≤ Real.log (M : Real) ∧
      (k₀ : Real) ≤ Real.sqrt (M : Real) ∧
      3 ≤ logRadius 10 M := by
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      ((2 : Real) ^ 12)
  have hsqrt :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (k₀ : Real)
  filter_upwards [hlog, hsqrt, eventually_gt_atTop (0 : Nat)] with M hlogM hsqrtM hM
  refine ⟨hM, hlogM, hsqrtM, ?_⟩
  have hlogOne : 1 ≤ Real.log (M : Real) :=
    (by norm_num : (1 : Real) ≤ 2 ^ 12).trans hlogM
  have hthreeLog : (3 : Real) ≤ Real.log (M : Real) :=
    (by norm_num : (3 : Real) ≤ 2 ^ 12).trans hlogM
  have hpow : (3 : Real) ≤ Real.log (M : Real) ^ 10 := by
    calc
      (3 : Real) ≤ 3 ^ 10 := by norm_num
      _ ≤ Real.log (M : Real) ^ 10 :=
        pow_le_pow_left₀ (by norm_num) hthreeLog 10
  have hceil := (ceil_power_bounds (Real.log (M : Real)) hlogOne 10).1
  have : (3 : Real) ≤ logRadius 10 M := hpow.trans hceil
  exact_mod_cast this

/-- Complete conditional closure of the literal q=3 project branch.  No open
input is hidden: both the distribution estimate and signed reserve floor are
arguments. -/
theorem eventually_actualQ3_projectBranch_positive
    (k₀ : Nat) (C c rho : Real)
    (hC : 0 ≤ C) (hc : 0 < c) (hrho : 0 < rho)
    (hscale : ScaleReducedClassEstimate 11 k₀ C c)
    (hreserve : EventualActualQ3PrefixLocalDensityReserveFloor rho) :
    ∀ᶠ M : Nat in atTop,
      ∀ q : PairedOddBase (oddProjectRadius M),
        ∀ n : Nat, 2 * n ∈ evenTargetBlock M → q.val.val = 3 →
          0 < (M : Real) / 14 +
            (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  have habsorb := eventually_actualQ3ScaleProjectEnvelope_lt_linear
    C c rho hC hc hrho
  filter_upwards [eventually_actualQ3_scale_prerequisites k₀,
    habsorb, hreserve] with M hpre habsorbM hreserveM
  intro q n hTarget hq
  have hD := actualQ3DirichletCharacterPartialSumCeiling_of_scaleEstimate
    M k₀ C c hpre.1 hC hc.le hpre.2.1 hpre.2.2.1 hscale hpre.2.2.2
  have hAbsorb :
      actualQ3UnitDifferenceScaleEnvelope M q
          (actualQ3ScaleCombinedPrefixEnvelope M C c +
            Real.log (M : Real)) <
        actualQ3PrefixLocalDensityProjectReserve M q n :=
    (habsorbM q hq).trans_le (hreserveM q n hTarget hq)
  exact projectReserve_add_negativeAggregate_re_pos_of_partialSumCeiling
    M hpre.1 q n hTarget hq
      (actualQ3ScaleCombinedPrefixEnvelope M C c)
      ((dirichletCharacterCeiling_iff_actualPartialSumCeiling
        M (actualQ3ScaleCombinedPrefixEnvelope M C c)).1 hD) hAbsorb

end GoldbachCircleMethodActualQ3FullConditionalClosureV18767
