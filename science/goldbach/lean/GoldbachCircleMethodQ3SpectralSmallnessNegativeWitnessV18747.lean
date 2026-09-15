import GoldbachCircleMethodActualQ3RefinedProjectDebitV18746

/-!
# V1.8.747: negative witness against automatic q=3 spectral smallness

V1.8.746 reduces the complete-endpoint portion of the actual project debit to
two nonzero additive modes modulo three.  This append-only module tests the
strictly narrower method claim that positivity, finite support, and a known
total mass could by themselves force such a mode-square budget to be small.

A nonnegative one-point source has total mass `A`, but both unit-frequency
q=3 modes have norm `A`; its two-mode square budget is exactly `2*A^2` and is
unbounded.  Therefore no nontrivial project-scale absorption follows from
support and positivity alone.  This does not evaluate the actual von-Mangoldt
source.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodQ3SpectralSmallnessNegativeWitnessV18747

/-- A finite nonnegative point mass at residue zero. -/
noncomputable def q3OnePointSource (A : Real) (a : Nat) : Real :=
  if a = 0 then A else 0

/-- The corresponding one-variable additive mode on its one-point carrier. -/
noncomputable def q3OnePointMode (A : Real) (xi : ZMod 3) : Complex :=
  ∑ a ∈ Finset.range 1,
    (q3OnePointSource A a : Complex) *
      ZMod.stdAddChar ((a : ZMod 3) * xi)

theorem q3OnePointSource_nonneg
    {A : Real} (hA : 0 ≤ A) (a : Nat) :
    0 ≤ q3OnePointSource A a := by
  unfold q3OnePointSource
  split_ifs <;> positivity

theorem q3OnePointSource_totalMass (A : Real) :
    (∑ a ∈ Finset.range 1, q3OnePointSource A a) = A := by
  simp [q3OnePointSource]

theorem q3OnePointMode_eq_real (A : Real) (xi : ZMod 3) :
    q3OnePointMode A xi = (A : Complex) := by
  simp [q3OnePointMode, q3OnePointSource]

theorem q3OnePointMode_norm_eq
    {A : Real} (hA : 0 ≤ A) (xi : ZMod 3) :
    ‖q3OnePointMode A xi‖ = A := by
  rw [q3OnePointMode_eq_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hA]

/-- Exact analogue of the two-mode budget used for the actual source. -/
noncomputable def q3OnePointSquareBudget (A : Real) : Real :=
  ‖q3OnePointMode A (1 : ZMod 3)‖ ^ 2 +
    ‖q3OnePointMode A (2 : ZMod 3)‖ ^ 2

theorem q3OnePointSquareBudget_eq_two_mul_sq
    {A : Real} (hA : 0 ≤ A) :
    q3OnePointSquareBudget A = 2 * A ^ 2 := by
  unfold q3OnePointSquareBudget
  rw [q3OnePointMode_norm_eq hA, q3OnePointMode_norm_eq hA]
  ring

/-- For every requested ceiling `B`, a nonnegative finite source with known
total mass has a two-mode square budget strictly above `B`. -/
theorem exists_nonnegative_source_twoModeBudget_gt
    (B : Real) :
    ∃ A : Real,
      0 ≤ A ∧
      (∑ a ∈ Finset.range 1, q3OnePointSource A a) = A ∧
      B < q3OnePointSquareBudget A := by
  let A : Real := |B| + 1
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : B ≤ |B| := le_abs_self B
  refine ⟨A, hA, q3OnePointSource_totalMass A, ?_⟩
  rw [q3OnePointSquareBudget_eq_two_mul_sq hA]
  dsimp [A]
  nlinarith [sq_nonneg (|B| : Real)]

/-- In particular, positivity plus finite support cannot imply a universal
project reserve ceiling for the q=3 two-mode budget. -/
theorem not_forall_nonnegative_source_twoModeBudget_le
    (B : Real) :
    ¬ ∀ A : Real, 0 ≤ A → q3OnePointSquareBudget A ≤ B := by
  intro h
  obtain ⟨A, hA, _hMass, hLarge⟩ :=
    exists_nonnegative_source_twoModeBudget_gt B
  exact (not_lt_of_ge (h A hA)) hLarge

end GoldbachCircleMethodQ3SpectralSmallnessNegativeWitnessV18747
