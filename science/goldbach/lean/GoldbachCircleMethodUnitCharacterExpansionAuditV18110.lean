import GoldbachCircleMethodPrimitiveRamanujanProjectionV18103
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866

namespace GoldbachCircleMethodUnitCharacterExpansionAuditV18110
variable (q : ℕ) [NeZero q]

/-- Exact finite multiplicative-character inversion on units, with the totient retained. -/
theorem unit_character_inversion (f : ZMod q → ℂ) (u : ZMod q) (hu : IsUnit u) :
    (∑ χ : DirichletCharacter ℂ q, χ u⁻¹ * (∑ v : ZMod q, χ v * f v)) =
      (q.totient : ℂ) * f u := by
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu]
  simp

/-- The actual Ramanujan function is reconstructed at every unit input;
the shift n is arbitrary, not assumed to be a unit. -/
theorem ramanujan_unit_character_expansion (n u : ZMod q) (hu : IsUnit u) :
    (∑ χ : DirichletCharacter ℂ q, χ u⁻¹ *
      (∑ v : ZMod q, χ v * unitCharacterSum q (n-v))) =
      (q.totient : ℂ) * unitCharacterSum q (n-u) := by
  exact unit_character_inversion q (fun v => unitCharacterSum q (n-v)) u hu

/-- No analytic assertion: the primitive coefficient is the already checked q*chi(n). -/
theorem primitive_ramanujan_coefficient (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (n : ZMod q) :
    (∑ v : ZMod q, χ v * unitCharacterSum q (n-v)) = (q : ℂ) * χ n := by
  simpa only [mul_comm (χ _) (unitCharacterSum q _)] using
    GoldbachCircleMethodPrimitiveRamanujanProjectionV18103.primitive_ramanujan_convolution q χ hχ n


/-- Unit-frequency Gauss shift needs no primitive-character hypothesis. -/
theorem dft_at_unit_gauss (χ : DirichletCharacter ℂ q) (a : ZMod q)
    (ha : IsUnit a) :
    ZMod.dft (χ : ZMod q → ℂ) a =
      χ⁻¹ (-a) * gaussSum χ ZMod.stdAddChar := by
  have hd : ZMod.dft (χ : ZMod q → ℂ) a =
      gaussSum χ (ZMod.stdAddChar.mulShift (-a)) := by
    simp only [ZMod.dft_apply, smul_eq_mul, gaussSum, AddChar.mulShift_apply]
    apply Finset.sum_congr rfl
    intro v _
    simp only [mul_neg, mul_comm]
  rw [hd]
  obtain ⟨u, hu⟩ := ha.neg
  rw [← hu]
  exact gaussSum_mulShift_eq χ ZMod.stdAddChar u

/-- Exact coefficient for any character, including imprimitive conductors.
No nonzero Gauss-sum or primitive reduction is assumed. -/
theorem general_ramanujan_gauss_coefficient (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    (∑ v : ZMod q, χ v * unitCharacterSum q (n-v)) =
      χ⁻¹ (-1) * gaussSum χ ZMod.stdAddChar *
        gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift n) := by
  have hc := GoldbachCircleMethodPrimitiveRamanujanProjectionV18103.ramanujan_convolution_dft
    q (χ : ZMod q → ℂ) n
  rw [show (∑ v : ZMod q, χ v * unitCharacterSum q (n-v)) =
      (∑ v : ZMod q, unitCharacterSum q (n-v) * χ v) by
        apply Finset.sum_congr rfl
        intro v _
        ring, hc]
  rw [show gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift n) =
      (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n*a)) by rfl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : IsUnit a
  · simp only [ha, if_true]
    rw [dft_at_unit_gauss q χ a ha]
    rw [show -a = (-1) * a by ring, map_mul χ⁻¹ (-1) a]
    ring
  · simp only [ha, if_false, MulChar.map_nonunit χ⁻¹ ha, zero_mul, mul_zero]



/-- Full Gauss-coefficient reconstruction of the actual Ramanujan function on units.
Both primitive and imprimitive characters are present; no division by a Gauss sum. -/
theorem ramanujan_full_gauss_expansion (n u : ZMod q) (hu : IsUnit u) :
    (∑ χ : DirichletCharacter ℂ q, χ u⁻¹ *
      (χ⁻¹ (-1) * gaussSum χ ZMod.stdAddChar *
        gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift n))) =
      (q.totient : ℂ) * unitCharacterSum q (n-u) := by
  simpa only [general_ramanujan_gauss_coefficient] using
    ramanujan_unit_character_expansion q n u hu


end GoldbachCircleMethodUnitCharacterExpansionAuditV18110
