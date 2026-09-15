import GoldbachCircleMethodUniformMajorPrefixReductionV1865

/-! # V1.8.66: exact finite residue decomposition at rational centers.
No distribution estimate is assumed to hold. Nonreduced residue mass is retained.
-/
open scoped BigOperators
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodComplexArcModelBindingV1856

namespace GoldbachCircleMethodFiniteResiduePrefixV1866

attribute [local instance] Classical.propDecidable

noncomputable def psiResidue (k q : ℕ) [NeZero q] (r : ZMod q) : ℝ :=
  ∑ n ∈ (Finset.range k.succ).filter (fun (n : ℕ) => (n : ZMod q) = r),
    ArithmeticFunction.vonMangoldt n

noncomputable def unitCharacterSum (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ r : ZMod q, if IsUnit r then ZMod.stdAddChar (a*r) else 0

noncomputable def reducedResidueError (k q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ r : ZMod q, if IsUnit r then
    ((psiResidue k q r : ℂ)-(k : ℂ)/(Nat.totient q : ℂ))*ZMod.stdAddChar (a*r) else 0

noncomputable def nonreducedResidueSum (k q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ∑ r : ZMod q, if IsUnit r then 0 else
    (psiResidue k q r : ℂ)*ZMod.stdAddChar (a*r)

noncomputable def nonreducedMass (k q : ℕ) [NeZero q] : ℝ :=
  ∑ r : ZMod q, if IsUnit r then 0 else psiResidue k q r

theorem psiResidue_nonneg (k q : ℕ) [NeZero q] (r : ZMod q) :
    0 ≤ psiResidue k q r := by
  exact Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)

theorem residue_reindex (k q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    (∑ r : ZMod q, (psiResidue k q r : ℂ)*f r) =
      ∑ n ∈ Finset.range k.succ, (ArithmeticFunction.vonMangoldt n : ℂ)*f (n : ZMod q) := by
  simp only [psiResidue, Finset.sum_filter, Complex.ofReal_sum,
    apply_ite, Complex.ofReal_zero, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem rational_prefix_eq_residue_sum (k q : ℕ) [NeZero q] (a : ZMod q) :
    exponentialSum k.succ (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) =
      ∑ r : ZMod q, (psiResidue k q r : ℂ)*ZMod.stdAddChar (a*r) := by
  rw [residue_reindex]
  simp only [exponentialSum, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, rational_fourier_phase_eq_stdAddChar, Int.cast_natCast]

theorem rational_prefix_decomposition (k q : ℕ) [NeZero q] (a : ZMod q) :
    exponentialSum k.succ (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle) =
      ((k : ℂ)/(Nat.totient q : ℂ))*unitCharacterSum q a +
        reducedResidueError k q a + nonreducedResidueSum k q a := by
  rw [rational_prefix_eq_residue_sum]
  unfold unitCharacterSum reducedResidueError nonreducedResidueSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : IsUnit r <;> simp only [hr, if_true, if_false] <;> ring

theorem standard_character_norm (q : ℕ) [NeZero q] (r : ZMod q) :
    ‖ZMod.stdAddChar r‖ = 1 := by
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe]

theorem nonreducedMass_nonneg (k q : ℕ) [NeZero q] :
    0 ≤ nonreducedMass k q := by
  apply Finset.sum_nonneg
  intro r _
  split_ifs
  · exact le_rfl
  · exact psiResidue_nonneg k q r

theorem nonreducedResidueSum_norm_le (k q : ℕ) [NeZero q] (a : ZMod q) :
    ‖nonreducedResidueSum k q a‖ ≤ nonreducedMass k q := by
  unfold nonreducedResidueSum nonreducedMass
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : IsUnit r
  · simp [hr]
  · simp only [hr, if_false, norm_mul, standard_character_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (psiResidue_nonneg k q r)]
    exact le_rfl

theorem reducedResidueError_norm_le (k q : ℕ) [NeZero q] (a : ZMod q)
    (B : ℝ) (hB : 0 ≤ B)
    (hclasses : ∀ r : ZMod q, IsUnit r →
      |psiResidue k q r-(k : ℝ)/(Nat.totient q : ℝ)| ≤ B) :
    ‖reducedResidueError k q a‖ ≤ (q : ℝ)*B := by
  unfold reducedResidueError
  calc
    _ ≤ ∑ r : ZMod q, ‖if IsUnit r then
        ((psiResidue k q r : ℂ)-(k : ℂ)/(Nat.totient q : ℂ))*ZMod.stdAddChar (a*r)
          else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ZMod q, B := by
      apply Finset.sum_le_sum
      intro r _
      by_cases hr : IsUnit r
      · simp only [hr, if_true, norm_mul, standard_character_norm, mul_one]
        have hcast : (psiResidue k q r : ℂ)-(k : ℂ)/(Nat.totient q : ℂ) =
            ((psiResidue k q r-(k : ℝ)/(Nat.totient q : ℝ) : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
        exact hclasses r hr
      · simpa only [hr, if_false, norm_zero] using hB
    _ = _ := by simp

theorem rational_prefix_error_le (k q : ℕ) [NeZero q] (a : ZMod q)
    (B : ℝ) (hB : 0 ≤ B)
    (hclasses : ∀ r : ZMod q, IsUnit r →
      |psiResidue k q r-(k : ℝ)/(Nat.totient q : ℝ)| ≤ B) :
    ‖exponentialSum k.succ (((a.val : ℝ)/(q : ℝ) : ℝ) : UnitAddCircle)-
      ((k : ℂ)/(Nat.totient q : ℂ))*unitCharacterSum q a‖ ≤
        (q : ℝ)*B+nonreducedMass k q := by
  rw [rational_prefix_decomposition]
  have heq (u v w : ℂ) : u+v+w-u=v+w := by ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    (reducedResidueError_norm_le k q a B hB hclasses)
    (nonreducedResidueSum_norm_le k q a))

end GoldbachCircleMethodFiniteResiduePrefixV1866
