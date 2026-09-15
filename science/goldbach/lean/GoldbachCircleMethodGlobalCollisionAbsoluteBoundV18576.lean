import GoldbachCircleMethodGlobalCollisionResidualSplitV18575
import GoldbachCircleMethodCollisionExplicitPolynomialBoundV18574

/-!
# Goldbach V1.8.576: global absolute collision bound

The explicit V1.8.574 bound for one ordered conductor pair is aggregated over
the genuine global collision residual of V1.8.575.  Cauchy--Schwarz is applied
at both finite conductor levels.  The resulting `Q^8` square cost is retained
literally.  No cancellation or sublinear estimate is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodGlobalCollisionAbsoluteBoundV18576

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCollisionExplicitPolynomialBoundV18574
open GoldbachCircleMethodCollisionPolylogSourceBoundV18573
open GoldbachCircleMethodGlobalCollisionResidualSplitV18575
open GoldbachCircleMethodRemovedConvolutionNormV18123

/-- The common nonnegative square envelope for one ordered conductor pair. -/
noncomputable def collisionPairPolynomialEnvelope
    (Q B : ℕ) (V : ℝ) : ℝ :=
  Real.exp 30 * (B : ℝ) ^ 2 * (Q : ℝ) ^ 4 * V ^ 4 *
    (collisionSourcePolylogCap B) ^ 2

theorem collisionPairPolynomialEnvelope_nonneg
    (Q B : ℕ) (V : ℝ) :
    0 ≤ collisionPairPolynomialEnvelope Q B V := by
  unfold collisionPairPolynomialEnvelope
  positivity

/-- The level-one guard preserves the V1.8.574 pairwise square bound. -/
theorem guardedCollisionPairResidual_sq_le_envelope
    (Q B : ℕ) (H V : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H)
    (hw : ∀ n, ‖w n‖ ≤ V) :
    (guardedCollisionPairResidual Q B H w r s) ^ 2 ≤
      collisionPairPolynomialEnvelope Q B V := by
  by_cases hlevel : r.val = 1 ∨ s.val = 1
  · rw [guardedCollisionPairResidual, if_pos hlevel]
    simpa using collisionPairPolynomialEnvelope_nonneg Q B V
  · rw [guardedCollisionPairResidual, if_neg hlevel]
    exact collisionLiteralCrossBlockCorrelation_sq_le_explicit_polynomial
      Q B H V w r s hB hH hQH hw

/-- For one outer conductor, the inner ordered collision sum pays at most
`Q^2` times the common pair envelope after Cauchy--Schwarz. -/
theorem inner_guarded_collision_sum_sq_le
    (Q B : ℕ) (H V : ℝ) (w : ℕ → ℂ)
    (r : PositiveLevel Q)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H)
    (hw : ∀ n, ‖w n‖ ≤ V) :
    (∑ s ∈ (Finset.univ.erase r),
        guardedCollisionPairResidual Q B H w r s) ^ 2 ≤
      (Q : ℝ) ^ 2 * collisionPairPolynomialEnvelope Q B V := by
  let K := collisionPairPolynomialEnvelope Q B V
  have hK : 0 ≤ K := collisionPairPolynomialEnvelope_nonneg Q B V
  have hcardNat : (Finset.univ.erase r).card ≤ Q := by
    calc
      (Finset.univ.erase r).card ≤ Finset.univ.card := Finset.card_erase_le
      _ = Q := by
        rw [Finset.card_univ, positive_level_card]
  have hcard : ((Finset.univ.erase r).card : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast hcardNat
  have hsum :
      (∑ s ∈ (Finset.univ.erase r),
          (guardedCollisionPairResidual Q B H w r s) ^ 2) ≤
        ((Finset.univ.erase r).card : ℝ) * K := by
    calc
      (∑ s ∈ (Finset.univ.erase r),
          (guardedCollisionPairResidual Q B H w r s) ^ 2) ≤
          ∑ _s ∈ (Finset.univ.erase r), K := by
            exact Finset.sum_le_sum (fun s _hs =>
              guardedCollisionPairResidual_sq_le_envelope
                Q B H V w r s hB hH hQH hw)
      _ = ((Finset.univ.erase r).card : ℝ) * K := by simp
  calc
    (∑ s ∈ (Finset.univ.erase r),
        guardedCollisionPairResidual Q B H w r s) ^ 2 ≤
        ((Finset.univ.erase r).card : ℝ) *
          ∑ s ∈ (Finset.univ.erase r),
            (guardedCollisionPairResidual Q B H w r s) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ ((Finset.univ.erase r).card : ℝ) *
          (((Finset.univ.erase r).card : ℝ) * K) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (Q : ℝ) * ((Q : ℝ) * K) := by
      gcongr
    _ = (Q : ℝ) ^ 2 * K := by ring

/-- Global absolute aggregation of the collision branch.  The theorem exposes
the full `Q^8` cost in the square; it is not a minor-arc absorption result. -/
theorem blockCollisionResidual_sq_le_global_absolute
    (Q B : ℕ) (H V : ℝ) (w : ℕ → ℂ)
    (hB : 2 ≤ B) (hH : 1 ≤ H) (hQH : (Q : ℝ) ≤ H)
    (hw : ∀ n, ‖w n‖ ≤ V) :
    (blockCollisionResidual Q B H w) ^ 2 ≤
      (Q : ℝ) ^ 4 * collisionPairPolynomialEnvelope Q B V := by
  let K := collisionPairPolynomialEnvelope Q B V
  have hK : 0 ≤ K := collisionPairPolynomialEnvelope_nonneg Q B V
  have hQ : 0 ≤ (Q : ℝ) := by positivity
  have hsum :
      (∑ r : PositiveLevel Q,
          (∑ s ∈ (Finset.univ.erase r),
            guardedCollisionPairResidual Q B H w r s) ^ 2) ≤
        (Q : ℝ) * ((Q : ℝ) ^ 2 * K) := by
    calc
      (∑ r : PositiveLevel Q,
          (∑ s ∈ (Finset.univ.erase r),
            guardedCollisionPairResidual Q B H w r s) ^ 2) ≤
          ∑ _r : PositiveLevel Q, (Q : ℝ) ^ 2 * K := by
            exact Finset.sum_le_sum (fun r _hr =>
              inner_guarded_collision_sum_sq_le
                Q B H V w r hB hH hQH hw)
      _ = (Q : ℝ) * ((Q : ℝ) ^ 2 * K) := by
        simp
  unfold blockCollisionResidual
  calc
    (∑ r : PositiveLevel Q,
        ∑ s ∈ (Finset.univ.erase r),
          guardedCollisionPairResidual Q B H w r s) ^ 2 ≤
        (Fintype.card (PositiveLevel Q) : ℝ) *
          ∑ r : PositiveLevel Q,
            (∑ s ∈ (Finset.univ.erase r),
              guardedCollisionPairResidual Q B H w r s) ^ 2 := by
      simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ)
          (f := fun r : PositiveLevel Q =>
            ∑ s ∈ (Finset.univ.erase r),
              guardedCollisionPairResidual Q B H w r s))
    _ = (Q : ℝ) *
          ∑ r : PositiveLevel Q,
            (∑ s ∈ (Finset.univ.erase r),
              guardedCollisionPairResidual Q B H w r s) ^ 2 := by
      rw [positive_level_card]
    _ ≤ (Q : ℝ) * ((Q : ℝ) * ((Q : ℝ) ^ 2 * K)) := by
      exact mul_le_mul_of_nonneg_left hsum hQ
    _ = (Q : ℝ) ^ 4 * K := by ring

end GoldbachCircleMethodGlobalCollisionAbsoluteBoundV18576
