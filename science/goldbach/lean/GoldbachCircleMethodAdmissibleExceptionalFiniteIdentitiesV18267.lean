import GoldbachCircleMethodZeroGapReserveScaleV18266
import GoldbachCircleMethodExceptionalModelDiagonalV18107
import GoldbachCircleMethodSmallConductorPairReserveV18108

/-!
# Goldbach V1.8.267: admissible exceptional-character finite identities

The exact finite identities from V1.8.107--108 are retyped over the repaired
structurally admissible slot and the proof-carrying zero-gap attestation.
No analytic reserve or exceptional-zero existence is added.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodAdmissibleExceptionalFiniteIdentitiesV18267

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodExceptionalModelDiagonalV18107
open GoldbachCircleMethodSmallConductorPairReserveV18108

theorem admissible_quadratic_value_square
    {Q : ℕ} (e : StructurallyAdmissibleActiveSlot Q)
    (a : ZMod e.val.1.val) :
    e.val.2.val a * e.val.2.val a = if IsUnit a then 1 else 0 := by
  exact quadratic_value_square e.val.1.val e.val.2.val
    (admissible_character_self_inverse e) a

theorem admissible_quadratic_primitive_gauss_square
    {Q : ℕ} (e : StructurallyAdmissibleActiveSlot Q) :
    gaussSum e.val.2.val ZMod.stdAddChar *
        gaussSum e.val.2.val ZMod.stdAddChar =
      e.val.2.val (-1) * (e.val.1.val : ℂ) := by
  exact quadratic_primitive_gauss_square e.val.1.val e.val.2.val
    e.val.2.property (admissible_character_self_inverse e)

theorem admissible_primitive_quadratic_self_convolution
    {Q : ℕ} (e : StructurallyAdmissibleActiveSlot Q)
    (n : ZMod e.val.1.val) :
    (∑ u : ZMod e.val.1.val, e.val.2.val u * e.val.2.val (n-u)) =
      e.val.2.val (-1) * unitCharacterSum e.val.1.val n := by
  exact primitive_quadratic_self_convolution e.val.1.val e.val.2.val
    e.val.2.property (admissible_character_self_inverse e) n

theorem admissible_primitive_unit_pair_sum
    {Q : ℕ} (e : StructurallyAdmissibleActiveSlot Q)
    (n : ZMod e.val.1.val) :
    (∑ u : ZMod e.val.1.val,
        e.val.2.val u * unitIndicator e.val.1.val (n-u)) =
      ((ArithmeticFunction.moebius e.val.1.val : ℤ) : ℂ) * e.val.2.val n := by
  exact primitive_unit_pair_sum e.val.1.val e.val.2.val e.val.2.property n

theorem attested_primitive_quadratic_self_convolution
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (n : ZMod d.slot.val.1.val) :
    (∑ u : ZMod d.slot.val.1.val,
        d.slot.val.2.val u * d.slot.val.2.val (n-u)) =
      d.slot.val.2.val (-1) * unitCharacterSum d.slot.val.1.val n := by
  exact admissible_primitive_quadratic_self_convolution d.slot n

theorem attested_primitive_unit_pair_sum
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (n : ZMod d.slot.val.1.val) :
    (∑ u : ZMod d.slot.val.1.val,
        d.slot.val.2.val u * unitIndicator d.slot.val.1.val (n-u)) =
      ((ArithmeticFunction.moebius d.slot.val.1.val : ℤ) : ℂ) *
        d.slot.val.2.val n := by
  exact admissible_primitive_unit_pair_sum d.slot n

end GoldbachCircleMethodAdmissibleExceptionalFiniteIdentitiesV18267

