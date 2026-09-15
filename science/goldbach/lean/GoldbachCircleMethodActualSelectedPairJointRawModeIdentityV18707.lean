import GoldbachCircleMethodActualOneFiberDFTRawPhaseSumV18705
import GoldbachCircleMethodActualCompanionPeriodicLiftV18202

/-!
# V1.8.707: actual selected-pair joint raw-mode identity

This append-only module opens the exact frequency geometry of one ordered
pair of distinct selected odd bases immediately before the V1.8.701 Cauchy
step.  The coupled target frequency is defined on the pair-local modulus
`q*r`; unit base frequencies at distinct bases force that target frequency
to be nonzero.

The actual V1.8.705 raw phase sums remain unchanged.  No absolute value,
triangle inequality, global LCM, weight replacement, smallness estimate,
asymptotic claim, moment estimate, exceptional-set theorem, or Goldbach
conclusion is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodActualSelectedPairJointRawModeIdentityV18707

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodFiniteRamanujanEnergyV18131
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodFullChannelPartitionedGramV18689
open GoldbachCircleMethodSelectedPairCrossCorrelationExpansionV18690
open GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691
open GoldbachCircleMethodExactSignedResidueFiberAggregationBeforeGlobalTriangleV18695
open GoldbachCircleMethodActualSignedTargetResidueFiberCenteredEnergyV18696
open GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698
open GoldbachCircleMethodActualOneFiberKernelCrossSpectralIdentityV18704
open GoldbachCircleMethodActualOneFiberDFTRawPhaseSumV18705

/-- The target frequency forced by two base frequencies.  Natural
representatives are multiplied by the complementary moduli before being cast,
so the value is independent of the chosen representatives. -/
def coupledTargetFrequency
    {R : Nat} (q r : PairedOddBase R)
    (xi : ZMod q.val.val) (eta : ZMod r.val.val) :
    ZMod (q.val.val * r.val.val) :=
  -((r.val.val * xi.val + q.val.val * eta.val : Nat) :
      ZMod (q.val.val * r.val.val))

/-- The literal joint target/base Fourier mode built from the two unchanged
V1.8.705 raw phase sums. -/
noncomputable def selectedPairJointRawMode
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (xi : ZMod q.val.val) (eta : ZMod r.val.val)
    (zeta : ZMod (q.val.val * r.val.val)) : Complex :=
  ∑ n ∈ Finset.range M.succ,
    ZMod.stdAddChar (-((n : ZMod (q.val.val * r.val.val)) * zeta)) *
      selectedPairOneFiberRawPhaseSum M q n xi *
      selectedPairOneFiberRawPhaseSum M r n eta

/-- The complete three-coordinate DFT of the genuine V1.8.695 real atom. -/
noncomputable def selectedPairBaseResidueAtomTripleDFT
    {R : Nat} (q r : PairedOddBase R)
    (xi : ZMod q.val.val) (eta : ZMod r.val.val)
    (zeta : ZMod (q.val.val * r.val.val)) : Complex :=
  ∑ x : ZMod q.val.val,
    ∑ y : ZMod r.val.val,
      ∑ z : ZMod (q.val.val * r.val.val),
        ZMod.stdAddChar (-(x * xi)) *
          ZMod.stdAddChar (-(y * eta)) *
          ZMod.stdAddChar (-(z * zeta)) *
          (selectedPairBaseResidueAtom q r x y z : Complex)

/-- Pulling a target phase through the right complementary modulus gives the
literal base character. -/
theorem stdAddChar_mul_right_complementary
    (q r k : Nat) [NeZero q] [NeZero r]
    (n : ZMod (q * r)) :
    ZMod.stdAddChar (n * ((r * k : Nat) : ZMod (q * r))) =
      ZMod.stdAddChar
        (ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) n * (k : ZMod q)) := by
  rw [← ZMod.natCast_zmod_val n]
  rw [show (n.val : ZMod (q * r)) * ((r * k : Nat) : ZMod (q * r)) =
      ((n.val * (r * k) : Nat) : ZMod (q * r)) by norm_cast]
  rw [show ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
        (n.val : ZMod (q * r)) * (k : ZMod q) =
      ((n.val * k : Nat) : ZMod q) by
        simp only [map_natCast]
        norm_cast]
  rw [show ((n.val * (r * k) : Nat) : ZMod (q * r)) =
      (((n.val * (r * k) : Nat) : Int) : ZMod (q * r)) by norm_cast,
    show ((n.val * k : Nat) : ZMod q) =
      (((n.val * k : Nat) : Int) : ZMod q) by norm_cast,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hq : (q : Complex) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hr : (r : Complex) ≠ 0 := by exact_mod_cast (NeZero.ne r)
  field_simp [hq, hr]

/-- Pulling a target phase through the left complementary modulus gives the
literal second base character. -/
theorem stdAddChar_mul_left_complementary
    (q r k : Nat) [NeZero q] [NeZero r]
    (n : ZMod (q * r)) :
    ZMod.stdAddChar (n * ((q * k : Nat) : ZMod (q * r))) =
      ZMod.stdAddChar
        (ZMod.castHom (Nat.dvd_mul_left r q) (ZMod r) n * (k : ZMod r)) := by
  rw [← ZMod.natCast_zmod_val n]
  rw [show (n.val : ZMod (q * r)) * ((q * k : Nat) : ZMod (q * r)) =
      ((n.val * (q * k) : Nat) : ZMod (q * r)) by norm_cast]
  rw [show ZMod.castHom (Nat.dvd_mul_left r q) (ZMod r)
        (n.val : ZMod (q * r)) * (k : ZMod r) =
      ((n.val * k : Nat) : ZMod r) by
        simp only [map_natCast]
        norm_cast]
  rw [show ((n.val * (q * k) : Nat) : ZMod (q * r)) =
      (((n.val * (q * k) : Nat) : Int) : ZMod (q * r)) by norm_cast,
    show ((n.val * k : Nat) : ZMod r) =
      (((n.val * k : Nat) : Int) : ZMod r) by norm_cast,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hq : (q : Complex) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hr : (r : Complex) ≠ 0 := by exact_mod_cast (NeZero.ne r)
  field_simp [hq, hr]

/-- The pair-local target character is exactly the product of the two base
characters.  This is the normalization check which fixes all signs in the
joint raw mode. -/
theorem stdAddChar_neg_mul_coupledTargetFrequency
    {R : Nat} (q r : PairedOddBase R)
    (xi : ZMod q.val.val) (eta : ZMod r.val.val)
    (n : ZMod (q.val.val * r.val.val)) :
    ZMod.stdAddChar (-(n * coupledTargetFrequency q r xi eta)) =
      ZMod.stdAddChar
          (ZMod.castHom (Nat.dvd_mul_right q.val.val r.val.val)
            (ZMod q.val.val) n * xi) *
        ZMod.stdAddChar
          (ZMod.castHom (Nat.dvd_mul_left r.val.val q.val.val)
            (ZMod r.val.val) n * eta) := by
  unfold coupledTargetFrequency
  rw [show -(n *
      -((r.val.val * xi.val + q.val.val * eta.val : Nat) :
        ZMod (q.val.val * r.val.val))) =
      n * ((r.val.val * xi.val + q.val.val * eta.val : Nat) :
        ZMod (q.val.val * r.val.val)) by ring]
  rw [show n *
        ((r.val.val * xi.val + q.val.val * eta.val : Nat) :
          ZMod (q.val.val * r.val.val)) =
      n * ((r.val.val * xi.val : Nat) :
          ZMod (q.val.val * r.val.val)) +
        n * ((q.val.val * eta.val : Nat) :
          ZMod (q.val.val * r.val.val)) by
        push_cast
        ring]
  rw [AddChar.map_add_eq_mul,
    stdAddChar_mul_right_complementary q.val.val r.val.val xi.val n,
    stdAddChar_mul_left_complementary q.val.val r.val.val eta.val n]
  simp only [ZMod.natCast_zmod_val]

/-- The real V1.8.695 atom embeds back into `Complex` as the literal product
of its two real Ramanujan factors. -/
theorem ofReal_selectedPairBaseResidueAtom_eq_product
    {R : Nat} (q r : PairedOddBase R)
    (x : ZMod q.val.val) (y : ZMod r.val.val)
    (z : ZMod (q.val.val * r.val.val)) :
    (selectedPairBaseResidueAtom q r x y z : Complex) =
      unitCharacterSum q.val.val
          ((2 : ZMod q.val.val) *
            (x - ZMod.castHom (Nat.dvd_mul_right q.val.val r.val.val)
              (ZMod q.val.val) z)) *
        unitCharacterSum r.val.val
          ((2 : ZMod r.val.val) *
            (ZMod.castHom (Nat.dvd_mul_left r.val.val q.val.val)
              (ZMod r.val.val) z - y)) := by
  unfold selectedPairBaseResidueAtom
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im, Complex.mul_im,
      unitCharacterSum_im_eq_zero, mul_zero, zero_mul, add_zero]

/-- The first affine Ramanujan factor contracts exactly onto the negative
doubled unit raw modes. -/
theorem sum_firstRamanujanFactor_mul_weight_eq_rawModes
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) :
    (∑ x : ZMod q.val.val,
      unitCharacterSum q.val.val
          ((2 : ZMod q.val.val) *
            (x - (n : ZMod q.val.val))) *
        (selectedPairOneFiberSignedResidueWeight M q n x : Complex)) =
      ∑ a : ZMod q.val.val,
        if IsUnit a then
          ZMod.stdAddChar
              (-((n : ZMod q.val.val) * ((2 : ZMod q.val.val) * a))) *
            selectedPairOneFiberRawPhaseSum M q n
              (-((2 : ZMod q.val.val) * a))
        else 0 := by
  simp_rw [← selectedPairOneFiberResidueDFT_eq_rawPhaseSum]
  unfold unitCharacterSum
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hunit : IsUnit a
  · simp only [hunit, if_true]
    rw [show selectedPairOneFiberResidueDFT M q n
          (-((2 : ZMod q.val.val) * a)) =
        ∑ x : ZMod q.val.val,
          ZMod.stdAddChar (-(x * (-((2 : ZMod q.val.val) * a)))) *
            (selectedPairOneFiberSignedResidueWeight M q n x : Complex) by rfl]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [← mul_assoc]
    congr 1
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  · simp [hunit]

/-- The reflected second affine Ramanujan factor contracts exactly onto the
positive doubled unit raw modes. -/
theorem sum_secondRamanujanFactor_mul_weight_eq_rawModes
    (M : Nat) (r : PairedOddBase (oddProjectRadius M)) (n : Nat) :
    (∑ y : ZMod r.val.val,
      unitCharacterSum r.val.val
          ((2 : ZMod r.val.val) *
            ((n : ZMod r.val.val) - y)) *
        (selectedPairOneFiberSignedResidueWeight M r n y : Complex)) =
      ∑ b : ZMod r.val.val,
        if IsUnit b then
          ZMod.stdAddChar
              ((n : ZMod r.val.val) * ((2 : ZMod r.val.val) * b)) *
            selectedPairOneFiberRawPhaseSum M r n
              ((2 : ZMod r.val.val) * b)
        else 0 := by
  simp_rw [← selectedPairOneFiberResidueDFT_eq_rawPhaseSum]
  unfold unitCharacterSum
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hunit : IsUnit b
  · simp only [hunit, if_true]
    rw [show selectedPairOneFiberResidueDFT M r n
          ((2 : ZMod r.val.val) * b) =
        ∑ y : ZMod r.val.val,
          ZMod.stdAddChar (-(y * ((2 : ZMod r.val.val) * b))) *
            (selectedPairOneFiberSignedResidueWeight M r n y : Complex) by rfl]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    rw [← mul_assoc]
    congr 1
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  · simp [hunit]

/-- Exact character-indexed raw-mode slice at one target index. -/
noncomputable def selectedPairCharacterRawSlice
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ a : ZMod q.val.val,
    ∑ b : ZMod r.val.val,
      if IsUnit a ∧ IsUnit b then
        ZMod.stdAddChar
            (-((n : ZMod q.val.val) * ((2 : ZMod q.val.val) * a))) *
          ZMod.stdAddChar
            ((n : ZMod r.val.val) * ((2 : ZMod r.val.val) * b)) *
          selectedPairOneFiberRawPhaseSum M q n
            (-((2 : ZMod q.val.val) * a)) *
          selectedPairOneFiberRawPhaseSum M r n
            ((2 : ZMod r.val.val) * b)
      else 0

/-- Complexified genuine factorized residue-atom slice. -/
noncomputable def selectedPairFactorizedResidueAtomSlice
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ x : ZMod q.val.val,
    ∑ y : ZMod r.val.val,
      (selectedPairBaseResidueAtom q r x y
          (n : ZMod (q.val.val * r.val.val)) : Complex) *
        (selectedPairOneFiberSignedResidueWeight M q n x : Complex) *
        (selectedPairOneFiberSignedResidueWeight M r n y : Complex)

noncomputable def selectedPairFirstResidueContraction
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) : Complex :=
  ∑ x : ZMod q.val.val,
    unitCharacterSum q.val.val
        ((2 : ZMod q.val.val) * (x - (n : ZMod q.val.val))) *
      (selectedPairOneFiberSignedResidueWeight M q n x : Complex)

noncomputable def selectedPairSecondResidueContraction
    (M : Nat) (r : PairedOddBase (oddProjectRadius M)) (n : Nat) : Complex :=
  ∑ y : ZMod r.val.val,
    unitCharacterSum r.val.val
        ((2 : ZMod r.val.val) * ((n : ZMod r.val.val) - y)) *
      (selectedPairOneFiberSignedResidueWeight M r n y : Complex)

noncomputable def selectedPairFirstRawModeSum
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) : Complex :=
  ∑ a : ZMod q.val.val,
    if IsUnit a then
      ZMod.stdAddChar
          (-((n : ZMod q.val.val) * ((2 : ZMod q.val.val) * a))) *
        selectedPairOneFiberRawPhaseSum M q n
          (-((2 : ZMod q.val.val) * a))
    else 0

noncomputable def selectedPairSecondRawModeSum
    (M : Nat) (r : PairedOddBase (oddProjectRadius M)) (n : Nat) : Complex :=
  ∑ b : ZMod r.val.val,
    if IsUnit b then
      ZMod.stdAddChar
          ((n : ZMod r.val.val) * ((2 : ZMod r.val.val) * b)) *
        selectedPairOneFiberRawPhaseSum M r n
          ((2 : ZMod r.val.val) * b)
    else 0

theorem selectedPairFactorizedResidueAtomSlice_eq_contractions
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    selectedPairFactorizedResidueAtomSlice M q r n =
      selectedPairFirstResidueContraction M q n *
        selectedPairSecondResidueContraction M r n := by
  unfold selectedPairFactorizedResidueAtomSlice
    selectedPairFirstResidueContraction selectedPairSecondResidueContraction
  simp_rw [ofReal_selectedPairBaseResidueAtom_eq_product]
  simp only [map_natCast]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  ring

theorem selectedPairFirstResidueContraction_eq_rawModeSum
    (M : Nat) (q : PairedOddBase (oddProjectRadius M)) (n : Nat) :
    selectedPairFirstResidueContraction M q n =
      selectedPairFirstRawModeSum M q n := by
  exact sum_firstRamanujanFactor_mul_weight_eq_rawModes M q n

theorem selectedPairSecondResidueContraction_eq_rawModeSum
    (M : Nat) (r : PairedOddBase (oddProjectRadius M)) (n : Nat) :
    selectedPairSecondResidueContraction M r n =
      selectedPairSecondRawModeSum M r n := by
  exact sum_secondRamanujanFactor_mul_weight_eq_rawModes M r n

theorem selectedPairFirstRawModeSum_mul_second_eq_characterRawSlice
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    selectedPairFirstRawModeSum M q n *
        selectedPairSecondRawModeSum M r n =
      selectedPairCharacterRawSlice M q r n := by
  unfold selectedPairFirstRawModeSum selectedPairSecondRawModeSum
    selectedPairCharacterRawSlice
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases ha : IsUnit a
  · by_cases hb : IsUnit b
    · simp only [ha, hb, and_self, if_true]
      ring
    · simp [ha, hb]
  · simp [ha]

/-- At each target index the complete genuine residue atom contracts exactly
to the character-indexed V1.8.705 raw modes. -/
theorem selectedPairFactorizedResidueAtomSlice_eq_characterRawSlice
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    selectedPairFactorizedResidueAtomSlice M q r n =
      selectedPairCharacterRawSlice M q r n := by
  rw [selectedPairFactorizedResidueAtomSlice_eq_contractions,
    selectedPairFirstResidueContraction_eq_rawModeSum,
    selectedPairSecondResidueContraction_eq_rawModeSum,
    selectedPairFirstRawModeSum_mul_second_eq_characterRawSlice]

/-- The same slice written with the unique pair-local coupled target phase. -/
noncomputable def selectedPairCoupledJointRawSlice
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) : Complex :=
  ∑ a : ZMod q.val.val,
    ∑ b : ZMod r.val.val,
      if IsUnit a ∧ IsUnit b then
        ZMod.stdAddChar
            (-((n : ZMod (q.val.val * r.val.val)) *
              coupledTargetFrequency q r
                (-((2 : ZMod q.val.val) * a))
                ((2 : ZMod r.val.val) * b))) *
          selectedPairOneFiberRawPhaseSum M q n
            (-((2 : ZMod q.val.val) * a)) *
          selectedPairOneFiberRawPhaseSum M r n
            ((2 : ZMod r.val.val) * b)
      else 0

/-- Exact phase assembly: the two base phases are the single coupled target
phase on `ZMod (q*r)`. -/
theorem selectedPairCharacterRawSlice_eq_coupledJointRawSlice
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n : Nat) :
    selectedPairCharacterRawSlice M q r n =
      selectedPairCoupledJointRawSlice M q r n := by
  unfold selectedPairCharacterRawSlice selectedPairCoupledJointRawSlice
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases ha : IsUnit a
  · by_cases hb : IsUnit b
    · simp only [ha, hb, and_self, if_true]
      rw [stdAddChar_neg_mul_coupledTargetFrequency q r
        (-((2 : ZMod q.val.val) * a))
        ((2 : ZMod r.val.val) * b)
        (n : ZMod (q.val.val * r.val.val))]
      simp only [map_natCast]
      ring
    · simp [ha, hb]
  · simp [ha]

/-- Sum of all coupled unit-character modes for one ordered selected pair. -/
noncomputable def selectedPairCoupledJointRawModeSum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) : Complex :=
  ∑ a : ZMod q.val.val,
    ∑ b : ZMod r.val.val,
      if IsUnit a ∧ IsUnit b then
        selectedPairJointRawMode M q r
          (-((2 : ZMod q.val.val) * a))
          ((2 : ZMod r.val.val) * b)
          (coupledTargetFrequency q r
            (-((2 : ZMod q.val.val) * a))
            ((2 : ZMod r.val.val) * b))
      else 0

/-- Finite interchange of the target-index sum and the two unit-character
sums.  No estimate is used. -/
theorem sum_coupledJointRawSlice_eq_coupledJointRawModeSum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    (∑ n ∈ Finset.range M.succ,
      selectedPairCoupledJointRawSlice M q r n) =
      selectedPairCoupledJointRawModeSum M q r := by
  unfold selectedPairCoupledJointRawSlice
    selectedPairCoupledJointRawModeSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases ha : IsUnit a
  · by_cases hb : IsUnit b
    · simp only [ha, hb, and_self, if_true]
      unfold selectedPairJointRawMode
      rfl
    · simp [ha, hb]
  · simp [ha]

/-- Distinct selected bases and unit base modes force the coupled target
frequency away from zero.  No coprimality between the bases is assumed. -/
theorem coupledTargetFrequency_ne_zero
    {R : Nat} (q r : PairedOddBase R)
    (hqr : q ≠ r)
    (xi : ZMod q.val.val) (eta : ZMod r.val.val)
    (hxi : IsUnit xi) (heta : IsUnit eta) :
    coupledTargetFrequency q r xi eta ≠ 0 := by
  intro hzero
  have hzero' :
      ((r.val.val * xi.val + q.val.val * eta.val : Nat) :
        ZMod (q.val.val * r.val.val)) = 0 := by
    simpa only [coupledTargetFrequency, neg_eq_zero] using hzero
  have hprod : q.val.val * r.val.val ∣
      r.val.val * xi.val + q.val.val * eta.val :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero'
  have hqsum : q.val.val ∣
      r.val.val * xi.val + q.val.val * eta.val :=
    dvd_trans (Nat.dvd_mul_right q.val.val r.val.val) hprod
  have hrsum : r.val.val ∣
      r.val.val * xi.val + q.val.val * eta.val :=
    dvd_trans (Nat.dvd_mul_left r.val.val q.val.val) hprod
  have hqmul : q.val.val ∣ r.val.val * xi.val :=
    (Nat.dvd_add_left (dvd_mul_right q.val.val eta.val)).mp hqsum
  have hrmul : r.val.val ∣ q.val.val * eta.val :=
    (Nat.dvd_add_right (dvd_mul_right r.val.val xi.val)).mp hrsum
  have hxicoprime : xi.val.Coprime q.val.val := by
    apply (ZMod.isUnit_iff_coprime xi.val q.val.val).mp
    simpa only [ZMod.natCast_zmod_val] using hxi
  have hetacoprime : eta.val.Coprime r.val.val := by
    apply (ZMod.isUnit_iff_coprime eta.val r.val.val).mp
    simpa only [ZMod.natCast_zmod_val] using heta
  have hqdivr : q.val.val ∣ r.val.val := by
    exact hxicoprime.symm.dvd_of_dvd_mul_right hqmul
  have hrdivq : r.val.val ∣ q.val.val := by
    exact hetacoprime.symm.dvd_of_dvd_mul_right hrmul
  have hval : q.val.val = r.val.val := Nat.dvd_antisymm hqdivr hrdivq
  apply hqr
  apply Subtype.ext
  apply Subtype.ext
  exact hval

/-- The exact character modes used in `selectedPairCoupledJointRawModeSum`
are unit base modes, hence their target mode is automatically nontrivial for
every ordered off-diagonal pair. -/
theorem coupledTargetFrequency_neg_two_two_ne_zero
    {R : Nat} (q r : PairedOddBase R)
    (hqr : q ≠ r)
    (a : ZMod q.val.val) (b : ZMod r.val.val)
    (ha : IsUnit a) (hb : IsUnit b) :
    coupledTargetFrequency q r
        (-((2 : ZMod q.val.val) * a))
        ((2 : ZMod r.val.val) * b) ≠ 0 := by
  have h2qCoprime : Nat.Coprime 2 q.val.val := by
    rw [Nat.coprime_comm]
    exact (Nat.coprime_two_right).mpr (pairedOddBase_odd q)
  have h2rCoprime : Nat.Coprime 2 r.val.val := by
    rw [Nat.coprime_comm]
    exact (Nat.coprime_two_right).mpr (pairedOddBase_odd r)
  have h2q : IsUnit (2 : ZMod q.val.val) :=
    (ZMod.isUnit_iff_coprime 2 q.val.val).mpr h2qCoprime
  have h2r : IsUnit (2 : ZMod r.val.val) :=
    (ZMod.isUnit_iff_coprime 2 r.val.val).mpr h2rCoprime
  apply coupledTargetFrequency_ne_zero q r hqr
  · exact IsUnit.neg (h2q.mul ha)
  · exact h2r.mul hb

theorem coupledTargetFrequency_neg_two_two_ne_zero_of_mem_erase
    {R : Nat} (q r : PairedOddBase R)
    (hrErase : r ∈ Finset.univ.erase q)
    (a : ZMod q.val.val) (b : ZMod r.val.val)
    (ha : IsUnit a) (hb : IsUnit b) :
    coupledTargetFrequency q r
        (-((2 : ZMod q.val.val) * a))
        ((2 : ZMod r.val.val) * b) ≠ 0 := by
  exact coupledTargetFrequency_neg_two_two_ne_zero q r
    (Finset.ne_of_mem_erase hrErase).symm a b ha hb

/-- Complexification of the actual V1.8.695 pair correlation exposes exactly
the sum of the factorized residue-atom slices. -/
theorem ofReal_selectedPairCrossFiberSum_eq_factorizedResidueAtomSlices
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    ((∑ N ∈ evenTargetBlock M,
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        ∑ u ∈ oddOddOffDiagonalSumCarrier M N,
          projectPairedBaseFiberTerm M q N t *
            projectPairedBaseFiberTerm M r N u : Real) : Complex) =
      ∑ n ∈ Finset.range M.succ,
        selectedPairFactorizedResidueAtomSlice M q r n := by
  rw [selectedPairCrossFiberSum_eq_signedResidueFibers]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  simp_rw [selectedPairSignedResidueFiberWeight_eq_oneFiber_product]
  simp only [Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold selectedPairFactorizedResidueAtomSlice
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  ring

/-- Exact pair-local answer immediately before every Cauchy or triangle step:
the actual V1.8.690 ordered-pair correlation is a sum solely of the coupled
V1.8.705 raw modes. -/
theorem ofReal_selectedPairCrossFiberSum_eq_coupledJointRawModeSum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    ((∑ N ∈ evenTargetBlock M,
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        ∑ u ∈ oddOddOffDiagonalSumCarrier M N,
          projectPairedBaseFiberTerm M q N t *
            projectPairedBaseFiberTerm M r N u : Real) : Complex) =
      selectedPairCoupledJointRawModeSum M q r := by
  rw [ofReal_selectedPairCrossFiberSum_eq_factorizedResidueAtomSlices]
  calc
    (∑ n ∈ Finset.range M.succ,
        selectedPairFactorizedResidueAtomSlice M q r n) =
      ∑ n ∈ Finset.range M.succ,
        selectedPairCharacterRawSlice M q r n := by
          apply Finset.sum_congr rfl
          intro n _hn
          exact selectedPairFactorizedResidueAtomSlice_eq_characterRawSlice
            M q r n
    _ = ∑ n ∈ Finset.range M.succ,
          selectedPairCoupledJointRawSlice M q r n := by
          apply Finset.sum_congr rfl
          intro n _hn
          exact selectedPairCharacterRawSlice_eq_coupledJointRawSlice M q r n
    _ = selectedPairCoupledJointRawModeSum M q r :=
      sum_coupledJointRawSlice_eq_coupledJointRawModeSum M q r

/-- Full V1.8.690 ordered off-diagonal Gram, assembled pair by pair into the
exact coupled raw-mode normal form.  The `erase` carrier is unchanged. -/
theorem ofReal_orderedOffDiagonalGram_eq_coupledJointRawModeSums
    (M : Nat) :
    (orderedOffDiagonalGram (evenTargetBlock M)
        (projectPairedBaseContribution M) : Complex) =
      ∑ q : PairedOddBase (oddProjectRadius M),
        ∑ r ∈ Finset.univ.erase q,
          selectedPairCoupledJointRawModeSum M q r := by
  rw [orderedOffDiagonalGram_eq_qrntu]
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  apply Finset.sum_congr rfl
  intro r _hr
  simpa only [Complex.ofReal_sum] using
    ofReal_selectedPairCrossFiberSum_eq_coupledJointRawModeSum M q r

end GoldbachCircleMethodActualSelectedPairJointRawModeIdentityV18707
