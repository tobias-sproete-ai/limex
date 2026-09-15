import GoldbachCircleMethodActualSelectedPairJointRawModeIdentityV18707

/-!
# V1.8.709: exact counter-modulation of the actual selected-pair joint modes

This append-only module records the structural obstruction exposed by the
V1.8.707 joint-mode representation.  The visible nonzero target character is
not an independent source of cancellation: after multiplying each literal
V1.8.705 raw phase sum by its matching target phase, the coupled character is
absorbed exactly into two demodulated one-fiber modes.

The result is an exact finite identity.  It proves neither constancy nor
smallness of the demodulated modes.  In particular, it supplies no variation
estimate, dispersion theorem, moment bound, exceptional-set estimate, or
Goldbach conclusion.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodActualJointModeCounterModulationV18709

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698
open GoldbachCircleMethodActualOneFiberDFTRawPhaseSumV18705
open GoldbachCircleMethodActualSelectedPairJointRawModeIdentityV18707

/-- The literal V1.8.705 raw phase sum after multiplication by the matching
target character.  This is a definition, not an estimate. -/
noncomputable def selectedPairOneFiberDemodulatedRawPhaseSum
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) : Complex :=
  ZMod.stdAddChar ((n : ZMod q.val.val) * xi) *
    selectedPairOneFiberRawPhaseSum M q n xi

/-- Exact expansion of the demodulated mode.  The phase now depends on the
relative coordinate `n-a`; no oscillatory gain is asserted. -/
theorem selectedPairOneFiberDemodulatedRawPhaseSum_eq_relativePhaseSum
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat) (xi : ZMod q.val.val) :
    selectedPairOneFiberDemodulatedRawPhaseSum M q n xi =
      ∑ a ∈ Finset.range M.succ,
        ZMod.stdAddChar
            (((n : ZMod q.val.val) - (a : ZMod q.val.val)) * xi) *
          (selectedPairOneFiberHalfWeight M q n a : Complex) := by
  unfold selectedPairOneFiberDemodulatedRawPhaseSum
    selectedPairOneFiberRawPhaseSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← mul_assoc]
  congr 1
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- At the coupled target frequency the complete target character is exactly
the product of the two demodulating base characters.  Hence the visible
nonzero target phase is fully absorbed into the actual moving raw modes. -/
theorem selectedPairJointRawMode_at_coupled_eq_sum_demodulated_products
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (xi : ZMod q.val.val) (eta : ZMod r.val.val) :
    selectedPairJointRawMode M q r xi eta
        (coupledTargetFrequency q r xi eta) =
      ∑ n ∈ Finset.range M.succ,
        selectedPairOneFiberDemodulatedRawPhaseSum M q n xi *
          selectedPairOneFiberDemodulatedRawPhaseSum M r n eta := by
  unfold selectedPairJointRawMode
    selectedPairOneFiberDemodulatedRawPhaseSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [stdAddChar_neg_mul_coupledTargetFrequency q r xi eta
    (n : ZMod (q.val.val * r.val.val))]
  simp only [map_natCast]
  ring

/-- The exact unit modes used by V1.8.707 therefore have the same
counter-modulated normal form.  The unit hypotheses are retained to match the
actual character carrier, but no inequality is derived from them. -/
theorem selectedPairJointRawMode_unit_mode_counter_modulation
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (a : ZMod q.val.val) (b : ZMod r.val.val)
    (_ha : IsUnit a) (_hb : IsUnit b) :
    selectedPairJointRawMode M q r
        (-((2 : ZMod q.val.val) * a))
        ((2 : ZMod r.val.val) * b)
        (coupledTargetFrequency q r
          (-((2 : ZMod q.val.val) * a))
          ((2 : ZMod r.val.val) * b)) =
      ∑ n ∈ Finset.range M.succ,
        selectedPairOneFiberDemodulatedRawPhaseSum M q n
            (-((2 : ZMod q.val.val) * a)) *
          selectedPairOneFiberDemodulatedRawPhaseSum M r n
            ((2 : ZMod r.val.val) * b) := by
  exact selectedPairJointRawMode_at_coupled_eq_sum_demodulated_products
    M q r _ _

end GoldbachCircleMethodActualJointModeCounterModulationV18709
