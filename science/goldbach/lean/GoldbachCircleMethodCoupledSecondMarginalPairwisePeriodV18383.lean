import GoldbachCircleMethodCanonicalFullFirstMarginalQuarticV18382
import GoldbachCircleMethodFiniteRamanujanEnergyV18131

/-!
# Goldbach V1.8.383: coupled second marginal on one pairwise period

The first coupled marginal is already controlled without a common LCM.  The
remaining arithmetic channel contains a product of two Ramanujan sums at
coprime levels.  This module tests the exact pairwise-period mechanism.

The key finite statement is that the actual Ramanujan sum has zero average
along a complete even-step period whenever the modulus is greater than two.
No incomplete-interval estimate, target-weight estimate, aggregation over
levels, reserve absorption, or Goldbach conclusion is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCoupledSecondMarginalPairwisePeriodV18383

open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodFiniteRamanujanEnergyV18131
open GoldbachCircleMethodFiniteResiduePrefixV1866

/-- Multiplication by a unit cannot hide the nonzero residue of two modulo a
modulus strictly larger than two. -/
theorem two_mul_unit_ne_zero
    (q : ℕ) [NeZero q] (hq : 2 < q) (a : ZMod q) (ha : IsUnit a) :
    ((2 : ℕ) : ZMod q) * a ≠ 0 := by
  intro h
  have h' : a * ((2 : ℕ) : ZMod q) = 0 := by
    simpa only [mul_comm] using h
  have htwo : ((2 : ℕ) : ZMod q) = 0 := ha.mul_right_eq_zero.mp h'
  have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp htwo
  have hle : q ≤ 2 := Nat.le_of_dvd (by omega) hdiv
  omega

/-- Every unit frequency has zero complete additive-character sum along the
even target step once the modulus is larger than two. -/
theorem even_step_unit_frequency_sum_eq_zero
    (q : ℕ) [NeZero q] (hq : 2 < q) (A : ZMod q)
    (a : ZMod q) (ha : IsUnit a) :
    (∑ i : ZMod q, ZMod.stdAddChar ((A + ((2 : ℕ) : ZMod q) * i) * a)) = 0 := by
  have hfreq : ((2 : ℕ) : ZMod q) * a ≠ 0 := two_mul_unit_ne_zero q hq a ha
  have hterm (i : ZMod q) :
      ZMod.stdAddChar ((A + ((2 : ℕ) : ZMod q) * i) * a) =
        ZMod.stdAddChar (A * a) *
          ZMod.stdAddChar ((((2 : ℕ) : ZMod q) * a) * i) := by
    rw [show (A + ((2 : ℕ) : ZMod q) * i) * a =
        A * a + (((2 : ℕ) : ZMod q) * a) * i by ring,
      AddChar.map_add_eq_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum,
    standard_character_orthogonality q (((2 : ℕ) : ZMod q) * a),
    if_neg hfreq, mul_zero]

/-- The literal V66 Ramanujan sum cancels over one full even-step period.
This is a finite identity at the actual source definition. -/
theorem even_step_unitCharacterSum_complete_period_eq_zero
    (q : ℕ) [NeZero q] (hq : 2 < q) (A : ℕ) :
    ∑ i ∈ Finset.range q,
        unitCharacterSum q ((A + 2 * i : ℕ) : ZMod q) = 0 := by
  calc
    (∑ i ∈ Finset.range q,
        unitCharacterSum q ((A + 2 * i : ℕ) : ZMod q)) =
        ∑ i : ZMod q,
          unitCharacterSum q ((A : ZMod q) + ((2 : ℕ) : ZMod q) * i) := by
      simp only [Nat.cast_add, Nat.cast_mul]
      exact sum_range_residues_complex q
        (fun i : ZMod q =>
          unitCharacterSum q ((A : ZMod q) + ((2 : ℕ) : ZMod q) * i))
    _ = 0 := by
      unfold unitCharacterSum
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro a _ha_mem
      by_cases ha : IsUnit a
      · simp only [ha, if_true]
        exact even_step_unit_frequency_sum_eq_zero q hq (A : ZMod q) a ha
      · simp [ha]

end GoldbachCircleMethodCoupledSecondMarginalPairwisePeriodV18383
