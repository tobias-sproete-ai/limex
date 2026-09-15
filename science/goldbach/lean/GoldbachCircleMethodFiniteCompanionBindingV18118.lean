import GoldbachCircleMethodBoundedConductorReindexV18117

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117

namespace GoldbachCircleMethodFiniteCompanionBindingV18118

/-- Exact nested version of the product carrier; no rectangular extension
without its product indicator is permitted. -/
theorem sum_productIndex_to_nested (Q : ℕ)
    (F : (r : PositiveLevel Q) →
      {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive} → PositiveLevel Q → ℂ) :
    (∑ j : ProductIndex Q, F j.val.1 j.val.2.1 j.val.2.2) =
      ∑ r : PositiveLevel Q, ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        ∑ l : PositiveLevel Q, if r.val*l.val ≤ Q then F r χ l else 0 := by
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun j : ProductData Q => j.1.val*j.2.2.val ≤ Q))
    (by intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun j : ProductData Q => F j.1 j.2.1 j.2.2),
    Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  exact Fintype.sum_prod_type _

/-- The actual finite companion, with the original weight evaluated at r*l. -/
noncomputable def finiteCompanion {Q : ℕ} (r : PositiveLevel Q) (N : ℕ)
    (w : ℕ → ℂ) : ℂ :=
  ∑ l : PositiveLevel Q,
    if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val then
      ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
        unitCharacterSum l.val (N : ZMod l.val) / (l.val.totient : ℂ) *
          w (r.val*l.val)
    else 0

/-- The coupled cutoff is exactly the natural quotient cutoff, endpoints included. -/
theorem product_cutoff_iff_quotient {Q : ℕ} (r l : PositiveLevel Q) :
    r.val*l.val ≤ Q ↔ l.val ≤ Q/r.val := by
  rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne r.val)), Nat.mul_comm l.val r.val]

/-- Same companion with its canonical l<=Q/r cutoff, not an asymptotic replacement. -/
theorem finiteCompanion_quotient_cutoff {Q : ℕ} (r : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r N w =
      ∑ l : PositiveLevel Q,
        if l.val ≤ Q/r.val ∧ Nat.Coprime r.val l.val then
          ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
            unitCharacterSum l.val (N : ZMod l.val) / (l.val.totient : ℂ) *
              w (r.val*l.val)
        else 0 := by
  unfold finiteCompanion
  apply Finset.sum_congr rfl
  intro l _
  simp only [product_cutoff_iff_quotient]

/-- Complete finite weighted Ramanujan-to-L_r identity at every rough input U.
No distribution estimate, smoothness hypothesis or character-average bound enters. -/
theorem weighted_ramanujan_companion_expansion (Q N U : ℕ) (w : ℕ → ℂ)
    (hU : ∀ q : PositiveLevel Q, IsUnit (U : ZMod q.val)) :
    (∑ q : PositiveLevel Q, w q.val *
      unitCharacterSum q.val ((N : ZMod q.val)-(U : ZMod q.val))) =
      ∑ r : PositiveLevel Q,
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          ((r.val : ℂ)/(r.val.totient : ℂ)) *
            χ.val (N : ZMod r.val) * star (χ.val (U : ZMod r.val)) *
              finiteCompanion r N w := by
  rw [weighted_ramanujan_product_expansion Q N U w hU]
  simp only [productComplement]
  rw [sum_productIndex_to_nested Q (fun r χ l =>
    w (r.val*l.val) * ((r.val : ℂ)/(r.val.totient : ℂ)) *
      (if Nat.Coprime r.val l.val then
        ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
          unitCharacterSum l.val (N : ZMod l.val) / (l.val.totient : ℂ)
      else 0) * χ.val (N : ZMod r.val) * star (χ.val (U : ZMod r.val)))]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro χ _
  rw [finiteCompanion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hp : r.val*l.val ≤ Q
  · simp only [hp, if_true, true_and]
    split_ifs <;> ring
  · simp only [hp, if_false, false_and, mul_zero]

end GoldbachCircleMethodFiniteCompanionBindingV18118
