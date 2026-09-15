import GoldbachCircleMethodOddDoublePairAmplitudeV18679

/-!
# V1.8.680: exact local residue centering for an odd/double denominator pair

For one fixed odd denominator `q > 2` and its double `q₂ = 2*q`, this
append-only module reindexes the literal V1.8.676/V1.8.678 odd-odd fiber
contribution by residues modulo `q`.  The residue weight retains the actual
`oddOddPairFiberMass` and the two distinct sinc radii.  It is neither frozen
nor replaced by a regularity model.

The actual Ramanujan atom has zero complete-period mean, so an arbitrary
constant component of the residue weights vanishes exactly.  This is only a
signed algebraic identity.  It supplies no estimate for the centered residue
fluctuation and therefore no sign, size, moment, exceptional-set, or Goldbach
conclusion.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodOddDoubleResidueCenteringV18680

open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOddDoublePairAmplitudeV18679
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddKernelL1V18655
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodFiniteRamanujanEnergyV18131
open GoldbachCircleMethodOriginalMaskModelBindingV1859

/-- The literal weight attached to one retained odd-odd sum fiber after the
`q`/`2*q` Ramanujan coefficient has been factored.  Both sinc radii and the
actual von-Mangoldt pair-fiber mass remain present. -/
noncomputable def oddDoubleActualFiberWeight
    (M P R N : Nat) (q q₂ : Denominator R) (t : Nat) : Complex :=
  (oddOddPairFiberMass M t : Complex) *
    (explicitSincRadiusFactor M P R ((N : Int) - (t : Int)) q +
      explicitSincRadiusFactor M P R ((N : Int) - (t : Int)) q₂)

/-- Total actual weight carried by one residue class of the retained
odd-odd off-diagonal carrier. -/
noncomputable def oddDoubleResidueFiberWeight
    (M P R N : Nat) (q q₂ : Denominator R) (x : ZMod q.val) : Complex :=
  ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
    if (t : ZMod q.val) = x then
      oddDoubleActualFiberWeight M P R N q q₂ t
    else 0

/-- The literal contribution of the two denominators before residue
reindexing.  This definition keeps the exact V1.8.676 fiber carrier. -/
noncomputable def oddDoubleActualPairContribution
    (M P R N : Nat) (q q₂ : Denominator R) : Complex :=
  ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
    (oddOddPairFiberMass M t : Complex) *
      (explicitDenominatorSincTerm M P R
          ((N : Int) - (t : Int)) q +
        explicitDenominatorSincTerm M P R
          ((N : Int) - (t : Int)) q₂)

/-- Exact reindexing of the actual `q`/`2*q` contribution through residue
fibers modulo `q`.  No absolute value or inequality is introduced. -/
theorem oddDoubleActualPairContribution_eq_residue_fibers
    (M P R N : Nat) (hN : Even N)
    (q q₂ : Denominator R) (hqOdd : Odd q.val)
    (hq₂ : q₂.val = 2 * q.val) :
    oddDoubleActualPairContribution M P R N q q₂ =
      ∑ x : ZMod q.val,
        unitCharacterSum q.val ((N : ZMod q.val) - x) *
          oddDoubleResidueFiberWeight M P R N q q₂ x := by
  have hPair :
      oddDoubleActualPairContribution M P R N q q₂ =
        ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
          unitCharacterSum q.val
              ((N : ZMod q.val) - (t : ZMod q.val)) *
            oddDoubleActualFiberWeight M P R N q q₂ t := by
    unfold oddDoubleActualPairContribution oddDoubleActualFiberWeight
    apply Finset.sum_congr rfl
    intro t ht
    rw [explicitDenominatorSincTerm_odd_double_pair M P R
      ((N : Int) - (t : Int)) q q₂ hqOdd hq₂
      (retained_oddOdd_shift_even hN ht)]
    rw [integerFourierRamanujan_neg_eq_unitCharacterSum]
    simp only [Int.cast_sub, Int.cast_natCast]
    ring
  rw [hPair]
  unfold oddDoubleResidueFiberWeight
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _ht
  simp

/-- A unit residue is nonzero once the modulus is larger than one. -/
theorem unit_ne_zero_of_one_lt
    (q : Nat) [NeZero q] (hq : 1 < q) (a : ZMod q) (ha : IsUnit a) :
    a ≠ 0 := by
  rcases ha with ⟨u, rfl⟩
  intro hu0
  have hone : (1 : ZMod q) = 0 := by
    calc
      1 = (u : ZMod q) * ((↑(u⁻¹) : ZMod q)) := by simp
      _ = 0 := by rw [hu0]; simp
  have hdiv : q ∣ 1 := by
    apply (ZMod.natCast_eq_zero_iff 1 q).mp
    simpa using hone
  have hqLe : q ≤ 1 := Nat.le_of_dvd (by omega) hdiv
  omega

/-- The actual translated Ramanujan atom has zero complete-period mean.
The proof is local character orthogonality, not an imported estimate. -/
theorem unitCharacterSum_sub_complete_period_eq_zero
    (q : Nat) [NeZero q] (hq : 2 < q) (A : ZMod q) :
    (∑ x : ZMod q, unitCharacterSum q (A - x)) = 0 := by
  unfold unitCharacterSum
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _haMem
  by_cases ha : IsUnit a
  · simp only [ha, if_true]
    have ha0 : a ≠ 0 := unit_ne_zero_of_one_lt q (by omega) a ha
    have hterm (x : ZMod q) :
        ZMod.stdAddChar ((A - x) * a) =
          ZMod.stdAddChar (A * a) * ZMod.stdAddChar ((-a) * x) := by
      rw [show (A - x) * a = A * a + (-a) * x by ring,
        AddChar.map_add_eq_mul]
    simp_rw [hterm]
    rw [← Finset.mul_sum,
      standard_character_orthogonality q (-a), if_neg]
    · simp
    · simpa using ha0
  · simp [ha]

/-- Exact centering identity for the real V1.8.676/V1.8.678 residue weights.
The centering scalar is arbitrary; no regularity of the weights is assumed. -/
theorem oddDoubleActualPairContribution_eq_centered_residue_fibers
    (M P R N : Nat) (hN : Even N)
    (q q₂ : Denominator R) (hq : 2 < q.val) (hqOdd : Odd q.val)
    (hq₂ : q₂.val = 2 * q.val) (C : Complex) :
    oddDoubleActualPairContribution M P R N q q₂ =
      ∑ x : ZMod q.val,
        unitCharacterSum q.val ((N : ZMod q.val) - x) *
          (oddDoubleResidueFiberWeight M P R N q q₂ x - C) := by
  rw [oddDoubleActualPairContribution_eq_residue_fibers M P R N hN
    q q₂ hqOdd hq₂]
  calc
    (∑ x : ZMod q.val,
        unitCharacterSum q.val ((N : ZMod q.val) - x) *
          oddDoubleResidueFiberWeight M P R N q q₂ x) =
      (∑ x : ZMod q.val,
        unitCharacterSum q.val ((N : ZMod q.val) - x) *
          (oddDoubleResidueFiberWeight M P R N q q₂ x - C)) +
        (∑ x : ZMod q.val,
          unitCharacterSum q.val ((N : ZMod q.val) - x)) * C := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ x : ZMod q.val,
        unitCharacterSum q.val ((N : ZMod q.val) - x) *
          (oddDoubleResidueFiberWeight M P R N q q₂ x - C) := by
      rw [unitCharacterSum_sub_complete_period_eq_zero q.val hq]
      simp

end GoldbachCircleMethodOddDoubleResidueCenteringV18680
