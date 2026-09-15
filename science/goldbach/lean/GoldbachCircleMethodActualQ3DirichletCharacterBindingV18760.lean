import GoldbachCircleMethodActualQ3FullCharacterPartialSumNormalizationV18759
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# V1.8.760: genuine Dirichlet-character binding for the actual q=3 table

The residue table isolated in V1.8.757 is now identified with Mathlib's
quadratic Dirichlet character modulo three, after the canonical cast from
integers to complex numbers.  This closes the semantic interface required
before any literature result about Dirichlet-character von-Mangoldt sums can
be matched.

No analytic cancellation result is imported, asserted, or inhabited.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757
open GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
open GoldbachCircleMethodActualQ3FullCharacterPartialSumNormalizationV18759

/-- The canonical quadratic Dirichlet character modulo three, valued in the
complex numbers. -/
noncomputable def q3QuadraticDirichletCharacter :
    DirichletCharacter Complex 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom Complex)

/-- Exact pointwise identification of the formerly ad hoc residue table with
the genuine Mathlib Dirichlet character modulo three. -/
theorem q3QuadraticDirichletCharacter_eq_table
    (r : ZMod 3) :
    q3QuadraticDirichletCharacter r =
      q3UnitDifferenceCharacterTable r := by
  by_cases h1 : r = 1
  · subst r
    change (((quadraticChar (ZMod 3)) (1 : ZMod 3) : Int) : Complex) = _
    rw [map_one]
    unfold q3UnitDifferenceCharacterTable
    rw [if_pos rfl]
    norm_num
  · by_cases h2 : r = 2
    · subst r
      change (((quadraticChar (ZMod 3)) (2 : ZMod 3) : Int) : Complex) = _
      have hquad : quadraticChar (ZMod 3) (2 : ZMod 3) = -1 := by
        change legendreSym 3 2 = -1
        norm_num
      have h21 : (2 : ZMod 3) ≠ 1 := by decide
      rw [hquad]
      unfold q3UnitDifferenceCharacterTable
      rw [if_neg h21, if_pos rfl]
      norm_num
    · have h0 : r = 0 := by
        have hv1 : r.val ≠ 1 := by
          intro hv
          apply h1
          apply ZMod.val_injective 3
          rw [ZMod.val_one 3]
          exact hv
        have hv2 : r.val ≠ 2 := by
          intro hv
          apply h2
          apply ZMod.val_injective 3
          rw [ZMod.val_two_eq_two_mod 3]
          norm_num
          exact hv
        have hvlt : r.val < 3 := ZMod.val_lt r
        have hv0 : r.val = 0 := by omega
        apply ZMod.val_injective 3
        simpa using hv0
      subst r
      change (((quadraticChar (ZMod 3)) (0 : ZMod 3) : Int) : Complex) = _
      have h01 : (0 : ZMod 3) ≠ 1 := by decide
      have h02 : (0 : ZMod 3) ≠ 2 := by decide
      rw [quadraticChar_zero]
      unfold q3UnitDifferenceCharacterTable
      rw [if_neg h01, if_neg h02]
      norm_num

/-- Standard finite von-Mangoldt partial sum against the genuine quadratic
Dirichlet character modulo three. -/
noncomputable def fullLambdaQ3DirichletCharacterPartialSum
    (X : Nat) : Complex :=
  ∑ a ∈ Finset.range X,
    (ArithmeticFunction.vonMangoldt a : Complex) *
      q3QuadraticDirichletCharacter (a : ZMod 3)

/-- The standard character sum is definitionally aligned with the normalized
actual q=3 sum from V1.8.759. -/
theorem fullLambdaQ3DirichletCharacterPartialSum_eq_actual
    (X : Nat) :
    fullLambdaQ3DirichletCharacterPartialSum X =
      fullLambdaQ3CharacterPartialSum X := by
  apply Finset.sum_congr rfl
  intro a _ha
  rw [q3QuadraticDirichletCharacter_eq_table]

/-- Literature-facing single-scale contract stated directly with a genuine
Dirichlet character.  It remains an open proposition. -/
def ActualQ3DirichletCharacterPartialSumCeiling
    (M : Nat) (D : Real) : Prop :=
  0 ≤ D ∧ ∀ X : Nat, X ≤ M.succ →
    ‖fullLambdaQ3DirichletCharacterPartialSum X‖ ≤ D

/-- The genuine-character ceiling is exactly equivalent to the normalized
actual-table ceiling. -/
theorem dirichletCharacterCeiling_iff_actualPartialSumCeiling
    (M : Nat) (D : Real) :
    ActualQ3DirichletCharacterPartialSumCeiling M D ↔
      ActualFullLambdaQ3CharacterPartialSumCeiling M D := by
  constructor <;> intro hD
  · refine ⟨hD.1, ?_⟩
    intro X hX
    rw [← fullLambdaQ3DirichletCharacterPartialSum_eq_actual]
    exact hD.2 X hX
  · refine ⟨hD.1, ?_⟩
    intro X hX
    rw [fullLambdaQ3DirichletCharacterPartialSum_eq_actual]
    exact hD.2 X hX

/-- Final exact composition at q=3: a ceiling for a genuine fixed-modulus
Dirichlet-character Mangoldt sum, plus the explicit even correction, suffices
whenever the resulting envelope is strictly absorbed by the signed project
reserve. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_dirichletCharacterCeiling
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (D : Real)
    (hD : ActualQ3DirichletCharacterPartialSumCeiling M D)
    (hAbsorb : actualQ3UnitDifferenceScaleEnvelope M q
        (D + Real.log (M : Real)) <
      actualQ3PrefixLocalDensityProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  exact projectReserve_add_negativeAggregate_re_pos_of_partialSumCeiling
    M hM q n hTarget hq D
      ((dirichletCharacterCeiling_iff_actualPartialSumCeiling M D).1 hD)
      hAbsorb

end GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760
