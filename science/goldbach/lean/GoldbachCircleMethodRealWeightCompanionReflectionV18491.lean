import GoldbachCircleMethodSupportSeparatedCoefficientMomentsV18490
import GoldbachCircleMethodFiniteRamanujanEnergyV18131

/-!
# Goldbach V1.8.491: real-weight companion reflection

This module closes the missing conjugation adapter between the literal finite
companion and the existing pairwise-period convolution machinery.  It makes no
estimate: it proves only exact identities for the original Ramanujan sums and
for weights whose values are fixed by complex conjugation.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodRealWeightCompanionReflectionV18491

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodFiniteRamanujanEnergyV18131
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

/-- Complex conjugation reflects the frequency of the literal Ramanujan sum.
No squarefreeness, coprimality, or asymptotic premise is used. -/
theorem star_unitCharacterSum (q : ℕ) [NeZero q] (a : ZMod q) :
    star (unitCharacterSum q a) = unitCharacterSum q (-a) := by
  unfold unitCharacterSum
  simp_rw [star_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hu : IsUnit r
  · simp only [hu, if_true, standard_character_conjugate]
    congr 2
    ring
  · simp [hu]

/-- Every logarithmic cutoff weight obtained from a real bump is fixed by
complex conjugation. -/
theorem star_logWeight (R : ℝ) (G : ℝ → ℝ) (n : ℕ) :
    star (logWeight R G n) = logWeight R G n := by
  simp [logWeight]

/-- Reflection formula for the original finite companion.  The only premise
is the pointwise reality of the weight; all original cutoff and coprimality
guards remain definitionally present. -/
theorem star_finiteCompanion
    {Q : ℕ} (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ)
    (hw : ∀ n : ℕ, star (w n) = w n) :
    star (finiteCompanion r N w) =
      ∑ l : PositiveLevel Q,
        if r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val then
          ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
            unitCharacterSum l.val (-(N : ZMod l.val)) /
              (l.val.totient : ℂ) * w (r.val * l.val)
        else 0 := by
  unfold finiteCompanion
  simp_rw [star_sum]
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hsupport : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · rcases hsupport with ⟨hcut, hcop⟩
    rw [if_pos ⟨hcut, hcop⟩, if_pos ⟨hcut, hcop⟩]
    rw [star_mul, hw, star_div₀, star_mul, star_unitCharacterSum]
    norm_num [Complex.star_def]
    ring
  · simp [hsupport]

/-- Canonical specialization used by the circle-method source budget. -/
theorem star_finiteCompanion_logWeight
    {Q : ℕ} (r : PositiveLevel Q) (N : ℕ) (R : ℝ) (G : ℝ → ℝ) :
    star (finiteCompanion r N (logWeight R G)) =
      ∑ l : PositiveLevel Q,
        if r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val then
          ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
            unitCharacterSum l.val (-(N : ZMod l.val)) /
              (l.val.totient : ℂ) *
                logWeight R G (r.val * l.val)
        else 0 := by
  exact star_finiteCompanion r N (logWeight R G) (star_logWeight R G)

end GoldbachCircleMethodRealWeightCompanionReflectionV18491
