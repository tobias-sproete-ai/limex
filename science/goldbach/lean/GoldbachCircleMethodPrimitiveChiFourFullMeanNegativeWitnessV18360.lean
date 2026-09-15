import GoldbachCircleMethodVariableMeanCombinedReserveV18340
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Goldbach V1.8.360: inhabited primitive-chi-four negative full-mean witness

The pairwise-period machinery controls incomplete-interval boundary costs
without a common LCM.  This module proves that such control does not determine
the sign of the exact arithmetic mean: at the genuine primitive quadratic
character modulo four, the literal full frozen pairwise mean is `-1/4`.

This is a negative witness for a uniform positivity inference from the bare
finite structural interfaces.  It is not a Goldbach counterexample and does
not assert the existence of an exceptional real zero.
-/

set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodPrimitiveChiFourFullMeanNegativeWitnessV18360

/-- The standard quadratic character modulo four, transported from integers
to complex numbers. -/
noncomputable def complexChiFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem complexChiFour_one : complexChiFour (1 : ZMod 4) = 1 := by
  simp [complexChiFour]

theorem complexChiFour_three : complexChiFour (3 : ZMod 4) = -1 := by
  norm_num [complexChiFour, ZMod.χ₄]

theorem complexChiFour_ne_one : complexChiFour ≠ 1 := by
  intro h
  have h3 := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ZMod 4)) h
  rw [complexChiFour_three] at h3
  have hOne : (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) = 1 := by
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime 3 4).mpr (by norm_num))
  rw [hOne] at h3
  norm_num at h3

theorem complexChiFour_conductor_ne_two :
    DirichletCharacter.conductor complexChiFour ≠ 2 := by
  intro hc
  have hfac := DirichletCharacter.factorsThrough_conductor complexChiFour
  rw [hc] at hfac
  rcases hfac with ⟨h24, χ₂, heq⟩
  have h3 : complexChiFour (3 : ℤ) = χ₂ (3 : ℤ) := by
    rw [heq]
    exact DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₂ h24 (by norm_num)
  have h1 : complexChiFour (1 : ℤ) = χ₂ (1 : ℤ) := by
    rw [heq]
    exact DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₂ h24 (by norm_num)
  have h31 : χ₂ (3 : ℤ) = χ₂ (1 : ℤ) := by
    congr 1
  have : complexChiFour (3 : ℤ) = complexChiFour (1 : ℤ) := by
    rw [h3, h31, ← h1]
  norm_num [complexChiFour, ZMod.χ₄] at this

theorem complexChiFour_isPrimitive : complexChiFour.IsPrimitive := by
  have hdiv := DirichletCharacter.conductor_dvd_level complexChiFour
  have hne0 : DirichletCharacter.conductor complexChiFour ≠ 0 :=
    DirichletCharacter.conductor_ne_zero complexChiFour
  have hne1 : DirichletCharacter.conductor complexChiFour ≠ 1 := by
    intro hc
    have : complexChiFour = 1 :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one).mpr hc
    exact complexChiFour_ne_one this
  have hne2 := complexChiFour_conductor_ne_two
  have hle : DirichletCharacter.conductor complexChiFour ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hdiv
  interval_cases hcond : DirichletCharacter.conductor complexChiFour <;>
    simp_all [DirichletCharacter.IsPrimitive]

theorem complexChiFour_inv : complexChiFour⁻¹ = complexChiFour := by
  exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).inv

noncomputable def complexChiFourPrimitive :
    {χ : DirichletCharacter ℂ 4 // χ.IsPrimitive} :=
  ⟨complexChiFour, complexChiFour_isPrimitive⟩

theorem unitCharacterSum_four_four [NeZero 4] :
    GoldbachCircleMethodFiniteResiduePrefixV1866.unitCharacterSum 4
      (((4 : ℤ) : ZMod 4)) = 2 := by
  have h := GoldbachCircleMethodFullSquarefreeCoefficientV1847.finiteFourierRamanujan_eq_totient_of_dvd
    (a := 4) (N := 4) (by norm_num) (by norm_num)
  rw [GoldbachCircleMethodGeneralCoprimeCharacterV1868.finiteFourierRamanujan_eq_unitCharacterSum]
    at h
  norm_num at h ⊢
  exact h

/-- At target four and unit weights the literal unit-pair bracket vanishes. -/
theorem unitPairBracket_four_zero [NeZero 4] :
    GoldbachCircleMethodActualUnitPairSignedResidualV18214.unitPairBracket
      4 4 complexChiFour 1 1 = 0 := by
  rw [GoldbachCircleMethodActualUnitPairSignedResidualV18214.actual_unit_pair_bracket
    4 4 complexChiFour complexChiFour_isPrimitive complexChiFour_inv 1 1]
  rw [GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.unitPairCount_four_four]
  rw [unitCharacterSum_four_four]
  have hminus : (-1 : ZMod 4) = (3 : ZMod 4) := by
    change (3 : ZMod 4) = (3 : ZMod 4)
    rfl
  rw [hminus, complexChiFour_three]
  norm_num [complexChiFour, ZMod.χ₄]

/-- Inhabited negative witness: the complete exact pairwise arithmetic mean
is `-1/4` at `Q=4`, `K=12`, `N=4`, constant level weights and the genuine
primitive quadratic character modulo four. -/
theorem fullFrozenPairwiseMean_four_negative :
    (GoldbachCircleMethodFullFrozenPairwiseIntervalV18323.fullFrozenPairwiseMean
      (by norm_num : 1 ≤ 4)
      GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.fourLevel
      complexChiFourPrimitive
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) 1 1 4).re =
        -(1 : ℝ) / 4 := by
  rw [GoldbachCircleMethodVariableMeanUnitPairNormalFormV18335.fullFrozenPairwiseMean_eq_signedResidual_add_unitPairBracket
    (by norm_num : 1 ≤ 4)
    GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.divisorsOfTwelve
    GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.fourLevel
    complexChiFourPrimitive complexChiFour_inv
    (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) 1 1 4]
  change
    (GoldbachCircleMethodActualUnitPairSignedResidualV18214.signedDiagonalResidual
          GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.divisorsOfTwelve
          GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.fourLevel
          (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) (4 : ZMod 12) +
        ((4 : ℂ) / (Nat.totient 4 : ℂ) ^ 2) *
          GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213.coupledDiagonal
            GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.divisorsOfTwelve
            GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.fourLevel
            (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) (4 : ZMod 12) *
          GoldbachCircleMethodActualUnitPairSignedResidualV18214.unitPairBracket
            4 (4 : ℤ) complexChiFour 1 1).re = -(1 : ℝ) / 4
  rw [unitPairBracket_four_zero]
  simp only [mul_zero, add_zero]
  exact GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.signedDiagonalResidual_four_negative

/-- Consequently the literal full pairwise mean is not uniformly
nonnegative under only the finite primitive/self-inverse interfaces. -/
theorem fullFrozenPairwiseMean_not_uniformly_nonnegative :
    ¬ ∀ {Q : ℕ} (hQ : 1 ≤ Q) (r : GoldbachCircleMethodBoundedConductorReindexV18117.PositiveLevel Q)
        (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
        (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (N : ℕ),
      0 ≤ (GoldbachCircleMethodFullFrozenPairwiseIntervalV18323.fullFrozenPairwiseMean
        hQ r χ v w t₁ t₂ N).re := by
  intro h
  have hnonneg := h (by norm_num : 1 ≤ 4)
    GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339.fourLevel
    complexChiFourPrimitive
    (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) 1 1 4
  rw [fullFrozenPairwiseMean_four_negative] at hnonneg
  norm_num at hnonneg

end GoldbachCircleMethodPrimitiveChiFourFullMeanNegativeWitnessV18360
