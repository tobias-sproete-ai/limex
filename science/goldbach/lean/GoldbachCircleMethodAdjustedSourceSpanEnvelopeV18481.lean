import GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480

/-!
# Goldbach V1.8.481: adjusted-source span envelope

The sharp primitive span envelope is combined with the two sparse correction
budgets. This closes the pointwise finite source-energy accounting only. The
result is not promoted to the required global subcritical source gate.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodAdjustedSourceSpanEnvelopeV18481

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrimitiveBaseSlotEnergyV18474
open GoldbachCircleMethodPrimitiveBaseSpanEnvelopeV18478
open GoldbachCircleMethodAdjustedSourceThreeTermDecompositionV18479
open GoldbachCircleMethodPrincipalExceptionalSourceEnergyV18480

/-- Literal pointwise adjusted-source envelope. The constant `9/2` is the
sum of the independently verified principal and exceptional `9/4` costs. -/
theorem adjustedSourceEnergy_le_span_envelope_add_corrections
    (Q B N : ℕ) (H b : ℝ) (hB : 2 ≤ B) (hH : 1 ≤ H) (hb : 0 ≤ b)
    (e : CharacterSlot Q) :
    adjustedSourceEnergy Q B N H b (blockInput B) e ≤
      3 * (primitiveBaseSpanEnvelope Q B H + (9 : ℝ) / 2) := by
  have hbase := primitiveBaseSourceEnergy_le_span_envelope
    Q B N H hB (show 0 ≤ H by linarith)
  have hprincipal := principalSourceEnergy_le_nine_fourths
    Q B N H hH
  have hexceptional := exceptionalPowerSourceEnergy_le_nine_fourths
    Q B N H b hH hb e
  calc
    adjustedSourceEnergy Q B N H b (blockInput B) e ≤
        3 * (primitiveBaseSourceEnergy Q B N H +
          principalSourceEnergy Q B N H +
            exceptionalPowerSourceEnergy Q B N H b e) :=
      adjustedSourceEnergy_le_three_budgets Q B N H b e
    _ ≤ 3 * (primitiveBaseSpanEnvelope Q B H + (9 : ℝ) / 2) := by
      nlinarith

end GoldbachCircleMethodAdjustedSourceSpanEnvelopeV18481
