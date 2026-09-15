import GoldbachCircleMethodMajorantSubunitObstructionV1880

/-! A countermodel for support-and-L2-only reasoning, NOT a prime exponential sum. -/
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory AddCircle
open GoldbachCircleMethodExceptionalTransferV1823

namespace GoldbachCircleMethodMaskedFrequencyCountermodelV1881

/-- Comparator in the broad masked L2 class; no arithmetic-realizability claim. -/
noncomputable def negativeMaskedMode (s : Set UnitAddCircle) (n : ℕ) :
    UnitAddCircle → ℂ :=
  s.indicator (fun x => -(fourier (n : ℤ) x))

theorem negativeMaskedMode_memLp (s : Set UnitAddCircle) (hs : MeasurableSet s) (n : ℕ) :
    MemLp (negativeMaskedMode s n) 2 haarAddCircle := by
  exact MemLp.indicator hs
    (ContinuousMap.memLp (p := 2) haarAddCircle ℂ (-fourier (n : ℤ)))

theorem negativeMaskedMode_coefficient (s : Set UnitAddCircle)
    (hs : MeasurableSet s) (n : ℕ) :
    fourierCoeff (negativeMaskedMode s n) (n : ℤ) =
      -(haarAddCircle.real s : ℂ) := by
  rw [fourierCoeff]
  have hi : (fun x => fourier (-(n : ℤ)) x • negativeMaskedMode s n x) =
      s.indicator (fun _ => (-1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [negativeMaskedMode, Set.indicator_of_mem hx, smul_eq_mul, mul_neg]
      rw [← fourier_add, neg_add_cancel, fourier_zero]
    · simp [negativeMaskedMode, Set.indicator_of_notMem hx]
  rw [hi, integral_indicator hs]
  simp [integral_const, Complex.real_smul]

theorem negativeMaskedMode_energy (s : Set UnitAddCircle)
    (hs : MeasurableSet s) (n : ℕ) :
    (∫ x : UnitAddCircle, ‖negativeMaskedMode s n x‖^2 ∂haarAddCircle) =
      haarAddCircle.real s := by
  have hi : (fun x => ‖negativeMaskedMode s n x‖^2) =
      s.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s
    · simp [negativeMaskedMode, Set.indicator_of_mem hx, fourier_apply, Circle.norm_coe]
    · simp [negativeMaskedMode, Set.indicator_of_notMem hx]
  rw [hi, integral_indicator hs]
  simp [integral_const]

theorem target_negative_moment_floor (s : Set UnitAddCircle)
    (hs : MeasurableSet s) (T : Finset ℕ) (n : ℕ) (hn : n ∈ T) :
    (haarAddCircle.real s)^2 ≤
      negativePartSquaredMoment T
        (fun N => (fourierCoeff (negativeMaskedMode s n) (N : ℤ)).re) := by
  have hterm : (negativePart
      (fourierCoeff (negativeMaskedMode s n) (n : ℤ)).re)^2 =
      (haarAddCircle.real s)^2 := by
    rw [negativeMaskedMode_coefficient s hs n]
    simp [negativePart]
  rw [← hterm]
  unfold negativePartSquaredMoment
  exact Finset.single_le_sum (fun (i : ℕ) (_ : i ∈ T) => sq_nonneg
    (negativePart (fourierCoeff (negativeMaskedMode s n) (i : ℤ)).re)) hn

theorem masked_mode_rejects_small_factor (s : Set UnitAddCircle)
    (hs : MeasurableSet s) (hpos : 0 < haarAddCircle.real s)
    (T : Finset ℕ) (n : ℕ) (hn : n ∈ T) (ε : ℝ)
    (hε : ε < haarAddCircle.real s) :
    ¬ (negativePartSquaredMoment T
        (fun N => (fourierCoeff (negativeMaskedMode s n) (N : ℤ)).re) ≤
      ε * (∫ x : UnitAddCircle, ‖negativeMaskedMode s n x‖^2 ∂haarAddCircle)) := by
  intro h
  rw [negativeMaskedMode_energy s hs n] at h
  have hf := target_negative_moment_floor s hs T n hn
  nlinarith [mul_lt_mul_of_pos_right hε hpos]

end GoldbachCircleMethodMaskedFrequencyCountermodelV1881
