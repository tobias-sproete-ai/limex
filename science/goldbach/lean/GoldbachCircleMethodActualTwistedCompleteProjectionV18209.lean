import GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodActualTwistedCompleteProjectionV18209
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodPrimitiveRamanujanProjectionV18103
open GoldbachCircleMethodMixedRamanujanOrthogonalityV18203
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208

/-- Fourier inversion with the nonunit coefficients removed only under an explicit zero hypothesis. -/
theorem unit_supported_fourier_expansion {l : ℕ} [NeZero l]
    (f : ZMod l → ℂ) (hf : ∀ b, ¬ IsUnit b → ZMod.dft f b = 0) (y : ZMod l) :
    (∑ b : ZMod l, if IsUnit b then
      ZMod.stdAddChar (y*b) * ZMod.dft f b else 0) = (l : ℂ) * f y := by
  have hdrop :
      (∑ b : ZMod l, if IsUnit b then
        ZMod.stdAddChar (y*b) * ZMod.dft f b else 0) =
      ∑ b : ZMod l, ZMod.stdAddChar (y*b) * ZMod.dft f b := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : IsUnit b
    · simp only [hb, if_true]
    · simp only [hb, if_false, hf b hb, mul_zero]
  rw [hdrop]
  have hi := congrFun (ZMod.dft_dft f) (-y)
  simpa only [ZMod.dft_apply, mul_neg, neg_neg, smul_eq_mul, mul_comm y] using hi

/-- The original Ramanujan kernel acts as l times identity on the exact unit-supported subspace. -/
theorem unit_supported_ramanujan_projection {l : ℕ} [NeZero l]
    (f : ZMod l → ℂ) (hf : ∀ b, ¬ IsUnit b → ZMod.dft f b = 0) (y : ZMod l) :
    (∑ x : ZMod l, unitCharacterSum l (y-x) * f x) = (l : ℂ) * f y := by
  rw [ramanujan_convolution_dft]
  exact unit_supported_fourier_expansion f hf y

/-- A full common period repeats the smaller-modulus projection exactly K/l times. -/
theorem unit_supported_lifted_projection {K l : ℕ} [NeZero K] [NeZero l]
    (hl : l ∣ K) (f : ZMod l → ℂ)
    (hf : ∀ b, ¬ IsUnit b → ZMod.dft f b = 0) (m : ZMod K) :
    (∑ x : ZMod K,
      unitCharacterSum l (ZMod.castHom hl (ZMod l) (m-x)) *
        f (ZMod.castHom hl (ZMod l) x)) =
      (K : ℂ) * f (ZMod.castHom hl (ZMod l) m) := by
  simp only [map_sub]
  rw [sum_reduction_exact hl
    (fun y => unitCharacterSum l (ZMod.castHom hl (ZMod l) m-y) * f y),
    unit_supported_ramanujan_projection f hf]
  rw [← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hl]

/-- Different exact reduced denominators cancel on a common complete period.
The support hypothesis concerns the genuine f, not a substituted character. -/
theorem unit_supported_mixed_convolution_zero {K q l : ℕ}
    [NeZero K] [NeZero q] [NeZero l]
    (hq : q ∣ K) (hl : l ∣ K) (hql : q ≠ l)
    (f : ZMod l → ℂ) (hf : ∀ b, ¬ IsUnit b → ZMod.dft f b = 0)
    (m : ZMod K) :
    (∑ x : ZMod K,
      unitCharacterSum q (ZMod.castHom hq (ZMod q) (m-x)) *
        f (ZMod.castHom hl (ZMod l) x)) = 0 := by
  have hscale : (l : ℂ) * (∑ x : ZMod K,
      unitCharacterSum q (ZMod.castHom hq (ZMod q) (m-x)) *
        f (ZMod.castHom hl (ZMod l) x)) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [show ∀ x : ZMod K,
      (l : ℂ) * (unitCharacterSum q (ZMod.castHom hq (ZMod q) (m-x)) *
        f (ZMod.castHom hl (ZMod l) x)) =
      unitCharacterSum q (ZMod.castHom hq (ZMod q) (m-x)) *
        ((l : ℂ) * f (ZMod.castHom hl (ZMod l) x)) by intro x; ring]
    simp_rw [← unit_supported_fourier_expansion f hf]
    unfold unitCharacterSum
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · simp only [ha, hb, if_true]
        have hz := liftedUnitCharacter_convolution_zero hq hl ha.unit hb.unit hql m
        have hw := congrArg (fun z : ℂ => z * ZMod.dft f b) hz
        simpa only [liftedUnitCharacter_apply, IsUnit.unit_spec, Finset.sum_mul,
          mul_assoc, mul_comm a, mul_comm b, zero_mul] using hw
      · simp [hb]
    · simp [ha]
  exact (mul_eq_zero.mp hscale).resolve_left (NeZero.ne (l : ℂ))

variable (r l : ℕ) [NeZero r] [NeZero l]
local instance productNeZero : NeZero (r*l) :=
  ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

/-- The literal V208 primitive-character/Ramanujan product has exact same-modulus projection. -/
theorem twisted_ramanujan_projection (hcop : Nat.Coprime r l)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (m : ZMod (r*l)) :
    (∑ x : ZMod (r*l), unitCharacterSum (r*l) (m-x) *
      twistedRamanujan r l χ x) =
    ((r*l : ℕ) : ℂ) * twistedRamanujan r l χ m := by
  exact unit_supported_ramanujan_projection (twistedRamanujan r l χ)
    (twistedRamanujan_dft_nonunit_zero r l hcop χ hχ) m

/-- Exact c_q versus actual primitive twist matrix on a positive common period.
This is not an incomplete-interval statement or the full outer conductor sum. -/
theorem twisted_ramanujan_complete_matrix {K q : ℕ} [NeZero K] [NeZero q]
    (hq : q ∣ K) (hrl : r*l ∣ K) (hcop : Nat.Coprime r l)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (m : ZMod K) :
    (∑ x : ZMod K,
      unitCharacterSum q (ZMod.castHom hq (ZMod q) (m-x)) *
        twistedRamanujan r l χ (ZMod.castHom hrl (ZMod (r*l)) x)) =
      if q = r*l then (K : ℂ) *
        twistedRamanujan r l χ (ZMod.castHom hrl (ZMod (r*l)) m) else 0 := by
  by_cases h : q = r*l
  · subst q
    rw [if_pos rfl]
    exact unit_supported_lifted_projection hrl (twistedRamanujan r l χ)
      (twistedRamanujan_dft_nonunit_zero r l hcop χ hχ) m
  · rw [if_neg h]
    exact unit_supported_mixed_convolution_zero hq hrl h (twistedRamanujan r l χ)
      (twistedRamanujan_dft_nonunit_zero r l hcop χ hχ) m

end GoldbachCircleMethodActualTwistedCompleteProjectionV18209
