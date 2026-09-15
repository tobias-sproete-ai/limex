import GoldbachCircleMethodActualLogWeightSquareBindingV18219
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# V1.8.220: canonical smooth bump and actual principal-diagonal floor

V1.8.219 exposed a precise order contract for the two actual logarithmic
weights.  This module supplies a concrete `C∞`, compactly supported function
that inhabits that contract.  It then identifies conductor one in the unchanged
V1.8.213 model with the actual principal diagonal and obtains its real lower
floor for every even target.

This closes a finite-weight and model-binding gate.  It does not prove an
analytic approximation theorem, a minor-arc estimate, an exceptional-set
bound, or Goldbach.
-/

set_option autoImplicit false

open scoped BigOperators Classical ContDiff

namespace GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualLogWeightSquareBindingV18219

/-- A fixed smooth cutoff: zero on `(-∞,-1]` and `[2,∞)`, one on `[0,1]`,
and nonincreasing on the only interval consumed by the logarithmic conductor
cutoff, `[0,2]`. -/
noncomputable def canonicalLogBump (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) * Real.smoothTransition (2 - x)

theorem canonicalLogBump_nonneg (x : ℝ) :
    0 ≤ canonicalLogBump x := by
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem canonicalLogBump_eq_right {x : ℝ} (hx : 0 ≤ x) :
    canonicalLogBump x = Real.smoothTransition (2 - x) := by
  rw [canonicalLogBump, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem canonicalLogBump_antitoneOn :
    AntitoneOn canonicalLogBump (Set.Icc (0 : ℝ) 2) := by
  intro x hx y hy hxy
  rw [canonicalLogBump_eq_right hx.1, canonicalLogBump_eq_right hy.1]
  exact Real.smoothTransition.monotone (by linarith)

theorem canonicalLogBump_zero_outside_Icc (x : ℝ)
    (hx : x ∉ Set.Icc (-1 : ℝ) 2) :
    canonicalLogBump x = 0 := by
  by_cases hleft : -1 ≤ x
  · have hright : ¬ x ≤ 2 := fun hx2 => hx ⟨hleft, hx2⟩
    have harg : 2 - x ≤ 0 := by linarith
    simp [canonicalLogBump, Real.smoothTransition.zero_of_nonpos harg]
  · have harg : x + 1 ≤ 0 := by linarith
    simp [canonicalLogBump, Real.smoothTransition.zero_of_nonpos harg]

theorem canonicalLogBump_hasCompactSupport :
    HasCompactSupport canonicalLogBump := by
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 2) isCompact_Icc ?_
  exact canonicalLogBump_zero_outside_Icc

theorem canonicalLogBump_contDiff :
    ContDiff ℝ ∞ canonicalLogBump := by
  unfold canonicalLogBump
  have hleft : ContDiff ℝ ∞ (fun x : ℝ => x + 1) :=
    contDiff_id.add contDiff_const
  have hright : ContDiff ℝ ∞ (fun x : ℝ => 2 - x) :=
    contDiff_const.sub contDiff_id
  simpa only [Function.comp_apply] using
    (Real.smoothTransition.contDiff.comp hleft).mul
      (Real.smoothTransition.contDiff.comp hright)

theorem canonicalLogBump_zero : canonicalLogBump 0 = 1 := by
  rw [canonicalLogBump]
  norm_num [Real.smoothTransition.one_of_one_le]

/-- The conductor-one coupled diagonal is definitionally the principal
diagonal after eliminating its always-true cutoff and coprimality guards. -/
theorem principalDiagonal_eq_coupledDiagonal_one
    {Q K : ℕ} [NeZero K] (hQ : 1 ≤ Q)
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (v w : ℕ → ℂ) (m : ZMod K) :
    principalDiagonal hK v w m =
      coupledDiagonal hK (oneLevel hQ) v w m := by
  unfold principalDiagonal coupledDiagonal
  apply Finset.sum_congr rfl
  intro l _
  have hlQ : l.val ≤ Q := (Finset.mem_Icc.mp l.property).2
  have hcut :
      (oneLevel hQ).val * l.val ≤ Q ∧
        Nat.Coprime (oneLevel hQ).val l.val := by
    simp [oneLevel, hlQ]
  rw [if_pos hcut]
  simp [oneLevel]

/-- The V1.8.219 actual two-weight floor with the canonical smooth compactly
supported bump; no uninhabited order-contract parameter remains. -/
theorem actual_canonicalLogBump_coupled_floor
    {K N : ℕ} [NeZero K]
    (R : ℝ) (hR : 1 < R)
    (hK : ∀ q : PositiveLevel ⌊R ^ 2⌋₊, q.val ∣ K)
    (r : PositiveLevel ⌊R ^ 2⌋₊) (hEven : Even N) :
    (2 - Real.exp (Real.pi ^ 2 / 24)) *
        (canonicalLogBump
          (Real.log (r.val : ℝ) / Real.log R)) ^ 2 ≤
      (coupledDiagonal hK r
        (logWeight R canonicalLogBump)
        (logWeight R canonicalLogBump) (N : ZMod K)).re := by
  exact conditional_actual_logWeight_square_floor R hR hK r hEven
    canonicalLogBump
    (fun x _ => canonicalLogBump_nonneg x)
    canonicalLogBump_antitoneOn

/-- Kernel-checked lower floor for the real part of the actual V1.8.213
principal diagonal with the explicit canonical bump. -/
theorem actual_principalDiagonal_canonicalLogBump_floor
    {K N : ℕ} [NeZero K]
    (R : ℝ) (hR : 1 < R)
    (hK : ∀ q : PositiveLevel ⌊R ^ 2⌋₊, q.val ∣ K)
    (hEven : Even N) :
    2 - Real.exp (Real.pi ^ 2 / 24) ≤
      (principalDiagonal hK
        (logWeight R canonicalLogBump)
        (logWeight R canonicalLogBump) (N : ZMod K)).re := by
  let hQ : 1 ≤ ⌊R ^ 2⌋₊ := log_cutoff_contains_one R hR
  have hfloor := actual_canonicalLogBump_coupled_floor R hR hK
    (oneLevel hQ) hEven
  have hweight :
      (canonicalLogBump
        (Real.log ((oneLevel hQ).val : ℝ) / Real.log R)) ^ 2 = 1 := by
    simp [oneLevel, canonicalLogBump_zero]
  rw [hweight, mul_one] at hfloor
  rw [principalDiagonal_eq_coupledDiagonal_one hQ hK]
  exact hfloor

end GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
