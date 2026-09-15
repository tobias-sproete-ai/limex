import GoldbachCircleMethodExplicitMaskFourierKernelV1887

/-! A finite regression witness: geometric q=4 arcs are not Moebius-weighted. -/
set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodFullSquarefreeCoefficientV1847
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodExplicitMaskFourierKernelV1887

namespace GoldbachCircleMethodNonsquarefreeMaskRegressionV1888

theorem ramanujan_four_zero :
    integerFourierRamanujan 4 0 (by norm_num) = 2 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, integerFourierRamanujan_natCast,
    finiteFourierRamanujan_eq_totient_of_dvd (by norm_num) (dvd_zero 4)]
  have ht : Nat.totient 4 = 2 := by decide
  rw [ht]
  norm_num

theorem four_not_squarefree : ¬ Squarefree (4 : ℕ) := by decide

theorem major_model_four_zero (N : ℕ) : signedMajorCoefficient N 4 = 0 :=
  signedMajorCoefficient_eq_zero_of_not_squarefree four_not_squarefree

theorem geometric_four_zero (M P : ℕ) :
    integerFourierRamanujan 4 0 (by norm_num) *
      centeredCharacterKernel 0 ((P : ℝ)/((4 : ℝ)*(M : ℝ))) =
        (((P : ℝ)/(M : ℝ) : ℝ) : ℂ) := by
  rw [ramanujan_four_zero]
  simp only [centeredCharacterKernel]
  push_cast
  ring

noncomputable def geometricZeroTerm (M P : ℕ) (q : Denominator 4) : ℂ :=
  integerFourierRamanujan q.val 0 (NeZero.ne q.val) *
    centeredCharacterKernel 0 ((P : ℝ)/((q.val : ℝ)*(M : ℝ)))

def fourDenominator : Denominator 4 := ⟨4, by norm_num⟩

theorem erase_four_changes_zero_kernel (M P : ℕ) :
    (∑ q : Denominator 4, geometricZeroTerm M P q) -
      (∑ q : Denominator 4, if q.val = 4 then 0 else geometricZeroTerm M P q) =
        (((P : ℝ)/(M : ℝ) : ℝ) : ℂ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ = geometricZeroTerm M P fourDenominator := by
      rw [Finset.sum_eq_single fourDenominator]
      · simp [fourDenominator]
      · intro q _ hq
        have hn : q.val ≠ 4 := by
          intro h
          apply hq
          exact Subtype.ext h
        simp [hn]
      · simp
    _ = _ := geometric_four_zero M P

theorem omitted_zero_mass_positive (M P : ℕ) (hM : 0 < M) (hP : 0 < P) :
    0 < (integerFourierRamanujan 4 0 (by norm_num) *
      centeredCharacterKernel 0 ((P : ℝ)/((4 : ℝ)*(M : ℝ)))).re := by
  rw [geometric_four_zero]
  simp only [Complex.ofReal_re]
  exact div_pos (by exact_mod_cast hP) (by exact_mod_cast hM)

theorem small_denominator_squarefree_iff (q : Denominator 4) :
    Squarefree q.val ↔ q.val ≠ 4 := by
  have hs : ∀ n : ℕ, 1 ≤ n → n ≤ 4 → (Squarefree n ↔ n ≠ 4) := by
    intro n hn1 hn4
    interval_cases n
    · simp
    · simp [Nat.prime_two.squarefree]
    · simp [Nat.prime_three.squarefree]
    · simp [four_not_squarefree]
  exact hs q.val (Finset.mem_Icc.mp q.property).1 (Finset.mem_Icc.mp q.property).2

theorem squarefree_truncation_changes_actual_zero_kernel (M P : ℕ)
    (hscale : 2*P*4 < M) :
    GoldbachCircleMethodSignedMaskKernelConvolutionV1884.minorMaskKernel M P 4 0 -
      (1 - ∑ q : Denominator 4,
        if Squarefree q.val then geometricZeroTerm M P q else 0) =
      -(((P : ℝ)/(M : ℝ) : ℝ) : ℂ) := by
  rw [explicit_denominator_mask_kernel M P 4 hscale]
  simp only [neg_zero, ite_true]
  have hs : (∑ q : Denominator 4,
      if Squarefree q.val then geometricZeroTerm M P q else 0) =
      ∑ q : Denominator 4, if q.val = 4 then 0 else geometricZeroTerm M P q := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : q.val = 4
    · simp [h, four_not_squarefree]
    · have hsquare := (small_denominator_squarefree_iff q).mpr h
      simp [hsquare, h]
  rw [hs]
  change (1 - ∑ q : Denominator 4, geometricZeroTerm M P q) -
      (1 - ∑ q : Denominator 4, if q.val = 4 then 0 else geometricZeroTerm M P q) = _
  linear_combination -(erase_four_changes_zero_kernel M P)

end GoldbachCircleMethodNonsquarefreeMaskRegressionV1888
