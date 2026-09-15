import GoldbachCircleMethodConditionalGlobalExceptionDecayV1879

/-!
# V1.8.623: logarithmic exceptional-set decay is not a decision theorem

This module gives a concrete logical countermodel to the invalid inference

  `(forall fixed A, E(X) = O_A (X / log(X)^A)) -> E(X) = 0`.

The witness is deliberately not the actual Goldbach exceptional-count function.
It proves only that the family of upper bounds, by itself, is compatible with a
persistent nonzero count. Hence no pointwise Goldbach conclusion may be obtained
from V1.8.79 by choosing larger and larger fixed logarithmic exponents.

`proof_status = NO_PROOF` remains mandatory.
-/
set_option autoImplicit false
open Filter Topology
open GoldbachCircleMethodConditionalGlobalExceptionDecayV1879

namespace GoldbachCircleMethodLogDecayNondecisionWitnessV18623

/-- A natural-valued, monotone synthetic cumulative exception count containing
one persistent exception. It is a logical countermodel only, not a claim about
Goldbach exceptions. -/
def persistentSingleExceptionCount (_X : ℕ) : ℕ := 1

/-- Real coercion of the synthetic counting function, used in asymptotic norms. -/
def persistentSingleException (X : ℕ) : ℝ := persistentSingleExceptionCount X

theorem persistentSingleExceptionCount_monotone :
    Monotone persistentSingleExceptionCount := by
  intro X Y hXY
  simp [persistentSingleExceptionCount]

/-- For every fixed natural exponent, the classical logarithmic comparison scale
eventually dominates one. -/
theorem eventually_one_le_log_decay_scale (A : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (1 : ℝ) ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ A := by
  filter_upwards [eventual_remainder_absorption A,
      eventually_ge_atTop (1 : ℕ)] with X hscale hX
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hrad : (0 : ℝ) ≤ 2 * (X : ℝ) := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * (X : ℝ)) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (2 * (X : ℝ))) ^ 2 = 2 * (X : ℝ) :=
    Real.sq_sqrt hrad
  have hone : (1 : ℝ) ≤ Real.sqrt (2 * (X : ℝ)) := by
    nlinarith
  exact hone.trans hscale

/-- One persistent exception satisfies every fixed-power logarithmic exceptional-
set upper bound. -/
theorem persistentSingleException_isBigO (A : ℕ) :
    Asymptotics.IsBigO atTop persistentSingleException
      (fun X : ℕ => (X : ℝ) / (Real.log (X : ℝ)) ^ A) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_one_le_log_decay_scale A] with X hX
  have hnonneg :
      0 ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ A := le_trans (by norm_num) hX
  change |persistentSingleException X| ≤
    1 * |(X : ℝ) / (Real.log (X : ℝ)) ^ A|
  rw [one_mul, abs_of_nonneg hnonneg]
  simpa [persistentSingleException, persistentSingleExceptionCount] using hX

/-- The witness never vanishes. -/
theorem persistentSingleException_ne_zero (X : ℕ) :
    persistentSingleException X ≠ 0 := by
  norm_num [persistentSingleException, persistentSingleExceptionCount]

theorem persistentSingleExceptionCount_pos (X : ℕ) :
    0 < persistentSingleExceptionCount X := by
  simp [persistentSingleExceptionCount]

/-- Explicit countermodel: simultaneous fixed-A logarithmic Big-O bounds do not,
as a matter of logic, force a counting function to vanish. -/
theorem fixed_log_decay_family_has_persistent_nonzero_model :
    ∃ E : ℕ → ℕ,
      Monotone E ∧
      (∀ A : ℕ, Asymptotics.IsBigO atTop (fun X => (E X : ℝ))
        (fun X : ℕ => (X : ℝ) / (Real.log (X : ℝ)) ^ A)) ∧
      (∀ X : ℕ, 0 < E X) := by
  refine ⟨persistentSingleExceptionCount,
    persistentSingleExceptionCount_monotone, ?_, persistentSingleExceptionCount_pos⟩
  intro A
  change Asymptotics.IsBigO atTop persistentSingleException
    (fun X : ℕ => (X : ℝ) / (Real.log (X : ℝ)) ^ A)
  exact persistentSingleException_isBigO A

end GoldbachCircleMethodLogDecayNondecisionWitnessV18623
