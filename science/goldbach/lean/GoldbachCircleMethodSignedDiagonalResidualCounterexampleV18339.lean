import GoldbachCircleMethodCanonicalVariableMeanReserveV18338

/-!
# V1.8.339: signed-diagonal residual counterexample

This module gives an exact finite witness showing that the signed diagonal
residual used by V1.8.337/V1.8.338 is not nonnegative in general.  The witness
uses `Q = 4`, common period `K = 12`, target `N = 4`, conductor `r = 4`, and
constant unit weights.  Its principal real diagonal is `7/4`, its coupled real
diagonal is `1`, its literal unit-pair count is `2`, and hence its signed
residual is exactly `-1/4`.

This closes only the proposed unconditional residual-positivity route.  It does
not make the full variable mean negative, estimate the pairwise boundary cost,
or prove Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339

open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualUnitPairPrimePowerV18197
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualCoupledDiagonalRealReadbackV18218
open GoldbachCircleMethodFullSquarefreePrefixFloorV1848
open GoldbachCircleMethodConditionalWeightedBindingPreflightV18217
open GoldbachCircleMethodFullSquarefreeCoefficientV1847
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActualUnitPairSignedResidualV18214

/-- The selected conductor `4` in the positive-level carrier up to `4`. -/
def fourLevel : PositiveLevel 4 :=
  ⟨4, Finset.mem_Icc.mpr (by norm_num)⟩

/-- Every positive level at cutoff `4` divides the common period `12`. -/
theorem divisorsOfTwelve (q : PositiveLevel 4) : q.val ∣ 12 := by
  obtain ⟨hq1, hq4⟩ := Finset.mem_Icc.mp q.property
  interval_cases q.val <;> norm_num

/-- The literal two-unit carrier modulo `4` at target `4` has two elements. -/
theorem unitPairCount_four_four : unitPairCount 4 4 = 2 := by
  simpa using
    (unitPairCount_prime_pow_succ (p := 2) (k := 1) (by norm_num) (4 : ℤ))

/-- The selected coupled diagonal has real part exactly one. -/
theorem coupledDiagonal_four_four_re :
    (coupledDiagonal divisorsOfTwelve fourLevel
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) (4 : ZMod 12)).re = 1 := by
  calc
    _ = actualRealWeightedCoupledPrefix 4 4 fourLevel.val
          (fun _ => (1 : ℝ)) := by
        exact coupledDiagonal_re_eq_actualRealWeightedCoupledPrefix
          divisorsOfTwelve fourLevel 4 (fun _ => (1 : ℝ))
    _ = 1 := by
      norm_num [actualRealWeightedCoupledPrefix, fourLevel,
        restrictedRealFourierCoefficient, realFourierCoefficient,
        finiteFourierRamanujan_one]

theorem realFourierCoefficient_four_one : realFourierCoefficient 4 1 = 1 := by
  norm_num [realFourierCoefficient, finiteFourierRamanujan_one]

theorem realFourierCoefficient_four_two : realFourierCoefficient 4 2 = 1 := by
  rw [realFourierCoefficient]
  simp only [dif_neg (by norm_num : (2 : ℕ) ≠ 0)]
  rw [finiteFourierRamanujan_eq_totient_of_dvd (by norm_num) (by norm_num)]
  norm_num

theorem realFourierCoefficient_four_three :
    realFourierCoefficient 4 3 = -(1 : ℝ) / 4 := by
  rw [realFourierCoefficient]
  simp only [dif_neg (by norm_num : (3 : ℕ) ≠ 0)]
  rw [finiteFourierRamanujan_eq_moebius_of_coprime 3 4 (by norm_num) (by norm_num)]
  norm_num [ArithmeticFunction.moebius_apply_prime,
    Nat.totient_prime (by norm_num : Nat.Prime 3)]

/-- The exact principal diagonal is `1 + 1 - 1/4 = 7/4`; the nonsquarefree
level `4` is eliminated by the retained Moebius-square mask. -/
theorem principalDiagonal_four_re :
    (principalDiagonal divisorsOfTwelve
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) (4 : ZMod 12)).re =
        (7 : ℝ) / 4 := by
  calc
    _ = (coupledDiagonal divisorsOfTwelve (oneLevel (by norm_num : 1 ≤ 4))
          (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ))
          (4 : ZMod 12)).re := by
        exact congrArg Complex.re
          (principalDiagonal_eq_coupledDiagonal_one (by norm_num : 1 ≤ 4)
            divisorsOfTwelve (fun _ => ((1 : ℝ) : ℂ))
            (fun _ => (1 : ℂ)) (4 : ZMod 12))
    _ = actualRealWeightedCoupledPrefix 4 4 1 (fun _ => (1 : ℝ)) := by
        exact coupledDiagonal_re_eq_actualRealWeightedCoupledPrefix
          divisorsOfTwelve (oneLevel (by norm_num : 1 ≤ 4)) 4
          (fun _ => (1 : ℝ))
    _ = (7 : ℝ) / 4 := by
      have hIcc : Finset.Icc 1 4 = {1, 2, 3, 4} := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hs2 : Squarefree (2 : ℕ) := (by norm_num : Nat.Prime 2).squarefree
      have hs3 : Squarefree (3 : ℕ) := (by norm_num : Nat.Prime 3).squarefree
      have hs4 : ¬ Squarefree (4 : ℕ) := by decide
      rw [actualRealWeightedCoupledPrefix, hIcc]
      norm_num [restrictedRealFourierCoefficient,
        realFourierCoefficient_four_one, realFourierCoefficient_four_two,
        realFourierCoefficient_four_three, hs2, hs3, hs4]

/-- Exact negative witness.  In particular, the premise
`0 ≤ signedDiagonalResidual.re` retained by V1.8.337/V1.8.338 cannot be
discharged uniformly from the bare finite definitions. -/
theorem signedDiagonalResidual_four_negative :
    (signedDiagonalResidual divisorsOfTwelve fourLevel
      (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ))
      (4 : ZMod 12)).re = -(1 : ℝ) / 4 := by
  have htot : Nat.totient 4 = 2 := by decide
  rw [signedDiagonalResidual, Complex.sub_re, principalDiagonal_four_re]
  change (7 : ℝ) / 4 -
      (((4 : ℂ) / (Nat.totient 4 : ℂ) ^ 2) *
        (unitPairCount 4 4 : ℂ) *
        coupledDiagonal divisorsOfTwelve fourLevel
          (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ))
          (4 : ZMod 12)).re = -(1 : ℝ) / 4
  rw [unitPairCount_four_four, htot]
  norm_num [Complex.mul_re]
  have hC :
      (coupledDiagonal divisorsOfTwelve fourLevel
        (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (4 : ZMod 12)).re = 1 := by
    simpa using coupledDiagonal_four_four_re
  rw [hC]
  norm_num

theorem signedDiagonalResidual_not_uniformly_nonnegative :
    ¬ ∀ {Q K : ℕ} [NeZero K]
        (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r : PositiveLevel Q)
        (v w : ℕ → ℂ) (m : ZMod K),
      0 ≤ (signedDiagonalResidual hK r v w m).re := by
  intro h
  have hnonneg := h divisorsOfTwelve fourLevel
    (fun _ => ((1 : ℝ) : ℂ)) (fun _ => (1 : ℂ)) (4 : ZMod 12)
  rw [signedDiagonalResidual_four_negative] at hnonneg
  norm_num at hnonneg

end GoldbachCircleMethodSignedDiagonalResidualCounterexampleV18339
