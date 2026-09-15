import GoldbachCircleMethodOddDoubleResidueCenteringV18680

/-!
# V1.8.682: exact outer-sign and real-part bridge for one odd/double pair

The V1.8.676 project normal form subtracts the real part of every literal
denominator contribution.  This append-only module exposes, for one chosen
`q`/`2*q` pair at the project schedule, exactly that negative real quantity.
It then transports the V1.8.680 centered residue identity through the same
outer minus sign and real-part projection.

There is no factor `2`: this module concerns one explicitly chosen pair only.
Positive real part of the complex pair is harmful because the project normal
form subtracts it.  No equality between `|re z|^2` and `norm z^2`, no extraction
of these pairs from the full denominator `Finset`, and no moment or Goldbach
conclusion is asserted.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodOddDoubleSignedRealBridgeV18682

open GoldbachCircleMethodOddDoubleResidueCenteringV18680
open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFiniteResiduePrefixV1866

/-- The exact real contribution of one selected odd/double denominator pair
to the subtracted off-diagonal term in the V1.8.676 project normal form. -/
noncomputable def projectOddDoubleSignedContribution
    (M N : Nat)
    (q q₂ : Denominator (oddProjectRadius M)) : Real :=
  -∑ t ∈ oddOddOffDiagonalSumCarrier M N,
    oddOddPairFiberMass M t *
      (explicitDenominatorSincTerm M
          (oddProjectWidth M) (oddProjectRadius M)
          ((N : Int) - (t : Int)) q +
        explicitDenominatorSincTerm M
          (oddProjectWidth M) (oddProjectRadius M)
          ((N : Int) - (t : Int)) q₂).re

/-- The real schedule-specialized definition is exactly the negative real part
of the V1.8.680 literal complex pair contribution.  No hypotheses are needed. -/
theorem projectOddDoubleSignedContribution_eq_neg_re_actualPair
    (M N : Nat)
    (q q₂ : Denominator (oddProjectRadius M)) :
    projectOddDoubleSignedContribution M N q q₂ =
      -(oddDoubleActualPairContribution M
          (oddProjectWidth M) (oddProjectRadius M) N q q₂).re := by
  unfold projectOddDoubleSignedContribution oddDoubleActualPairContribution
  apply congrArg Neg.neg
  change
    (∑ t ∈ oddOddOffDiagonalSumCarrier M N,
      oddOddPairFiberMass M t *
        (explicitDenominatorSincTerm M
            (oddProjectWidth M) (oddProjectRadius M)
            ((N : Int) - (t : Int)) q +
          explicitDenominatorSincTerm M
            (oddProjectWidth M) (oddProjectRadius M)
            ((N : Int) - (t : Int)) q₂).re) =
      Complex.reCLM
        (∑ t ∈ oddOddOffDiagonalSumCarrier M N,
          (oddOddPairFiberMass M t : Complex) *
            (explicitDenominatorSincTerm M
                (oddProjectWidth M) (oddProjectRadius M)
                ((N : Int) - (t : Int)) q +
              explicitDenominatorSincTerm M
                (oddProjectWidth M) (oddProjectRadius M)
                ((N : Int) - (t : Int)) q₂))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  simp [Complex.mul_re]

/-- Exact centered representation with the same V1.8.676 outer minus sign.
The expression remains signed; no absolute value or inequality is introduced. -/
theorem projectOddDoubleSignedContribution_eq_neg_re_centered
    (M N : Nat) (hN : Even N)
    (q q₂ : Denominator (oddProjectRadius M))
    (hq : 2 < q.val) (hqOdd : Odd q.val)
    (hq₂ : q₂.val = 2 * q.val) (C : Complex) :
    projectOddDoubleSignedContribution M N q q₂ =
      -(∑ x : ZMod q.val,
          unitCharacterSum q.val ((N : ZMod q.val) - x) *
            (oddDoubleResidueFiberWeight M
              (oddProjectWidth M) (oddProjectRadius M) N q q₂ x - C)).re := by
  rw [projectOddDoubleSignedContribution_eq_neg_re_actualPair]
  rw [oddDoubleActualPairContribution_eq_centered_residue_fibers
    M (oddProjectWidth M) (oddProjectRadius M) N hN
    q q₂ hq hqOdd hq₂ C]

end GoldbachCircleMethodOddDoubleSignedRealBridgeV18682
