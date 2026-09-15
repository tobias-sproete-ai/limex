import GoldbachCircleMethodAdmissibleExceptionalFiniteIdentitiesV18267
import GoldbachCircleMethodActualUnitPairWeightedReserveV18195

/-!
# Goldbach V1.8.271: attested unit-pair zero-gap reserve

The already kernel-verified finite block reserve from V1.8.195 is composed
with the repaired proof-carrying zero-gap attestation from V1.8.263.
No fixed positive floor replaces the retained zero-gap scale.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAttestedUnitPairZeroGapReserveV18271

open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodZeroGapReserveScaleV18266
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualUnitPairWeightedReserveV18195

/-- A structurally admissible exceptional-zero record inhabits the literal
finite unit-pair power-weight reserve at its corrected scale `1 - beta`.

The carrier variables `n` and `u` are fixed during the residue average. The
theorem does not perform an incomplete-interval or spatial-weight transfer.
-/
theorem attested_actual_block_power_unit_pair_reserve
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (m B n u : ℕ)
    (hr3 : 3 < d.slot.val.1.val) (hm : Even m)
    (hB : 4 ≤ B)
    (hn : n ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B)
    (hu : u ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B) :
    (unitPairCount d.slot.val.1.val (m : ℤ) : ℝ) *
        zeroGapReserveScale d.zeroGap B / 6 ≤
      (∑ x ∈ unitPairResidues d.slot.val.1.val (m : ℤ),
        (1-(((n : ℝ)^(-d.zeroGap) : ℝ) : ℂ)*d.slot.val.2.val x) *
          (1-(((u : ℝ)^(-d.zeroGap) : ℝ) : ℂ)*
            d.slot.val.2.val (((m : ℤ) : ZMod d.slot.val.1.val)-x))).re := by
  simpa [zeroGapReserveScale] using
    actual_block_power_unit_pair_reserve
      d.slot.val.1.val m B n u hr3 hm hB hn hu d.slot.val.2.val
      d.slot.val.2.property (admissible_character_self_inverse d.slot)
      d.zeroGap (zeroGap_pos d)

end GoldbachCircleMethodAttestedUnitPairZeroGapReserveV18271
