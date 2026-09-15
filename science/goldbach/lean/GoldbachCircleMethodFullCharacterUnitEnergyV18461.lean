import GoldbachCircleMethodFullCharacterUnitParsevalV18460

/-!
# Goldbach V1.8.461: real energy and filtered-character domination

The complex Parseval identity from V1.8.460 is converted into the exact real
squared-norm identity used by the analytic energy ledger.  An arbitrary
filtered character family is then bounded by the full family solely by
nonnegativity.  In particular, primitive characters incur no crude cardinality
loss at one fixed modulus.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodFullCharacterUnitEnergyV18461

open GoldbachCircleMethodFullCharacterUnitParsevalV18460

variable (q : ℕ) [NeZero q]

private theorem star_mul_eq_norm_sq (z : ℂ) :
    star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]

/-- Exact squared-norm Parseval identity over the complete Dirichlet-character
family of a fixed modulus. -/
theorem full_character_unit_energy_real (A : (ZMod q)ˣ → ℂ) :
    (∑ chi : DirichletCharacter ℂ q, ‖unitCharacterTransform q A chi‖ ^ 2) =
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖A u‖ ^ 2 := by
  have h := full_character_unit_parseval_complex q A
  simp_rw [star_mul_eq_norm_sq] at h
  exact_mod_cast h

/-- Every decidable subfamily of characters, including the primitive ones, is
dominated by the exact full-family Parseval energy. -/
theorem filtered_character_unit_energy_le
    (A : (ZMod q)ˣ → ℂ) (P : DirichletCharacter ℂ q → Prop)
    [DecidablePred P] :
    (∑ chi ∈ (Finset.univ.filter P), ‖unitCharacterTransform q A chi‖ ^ 2) ≤
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖A u‖ ^ 2 := by
  calc
    _ ≤ ∑ chi : DirichletCharacter ℂ q,
        ‖unitCharacterTransform q A chi‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro chi _hchi _hnot
        positivity
    _ = _ := full_character_unit_energy_real q A

end GoldbachCircleMethodFullCharacterUnitEnergyV18461
