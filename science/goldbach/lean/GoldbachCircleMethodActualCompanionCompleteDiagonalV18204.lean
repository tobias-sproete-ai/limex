import GoldbachCircleMethodMixedRamanujanOrthogonalityV18203
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodActualCompanionCompleteDiagonalV18204

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodMixedRamanujanOrthogonalityV18203

/-- The literal scalar coefficient; both coupled cutoff and coprimality are retained. -/
noncomputable def literalCoefficient {Q : ℕ} (r l : PositiveLevel Q)
    (w : ℕ → ℂ) : ℂ :=
  if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val then
    ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) / (l.val.totient : ℂ) *
      w (r.val*l.val)
  else 0

/-- Definitional binding, not a replacement companion. -/
theorem periodicCompanion_expansion {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r : PositiveLevel Q) (w : ℕ → ℂ) (x : ZMod K) :
    periodicCompanion r w x =
      ∑ l : PositiveLevel Q, literalCoefficient r l w *
        unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x) := by
  unfold periodicCompanion finiteCompanion literalCoefficient
  apply Finset.sum_congr rfl
  intro l _
  rw [cast_val_eq_reduction (hK l)]
  split_ifs <;> ring

/-- Complete-period matrix entries: same denominator gives K*c_q, all others vanish. -/
theorem ramanujan_complete_matrix {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (q l : PositiveLevel Q) (m : ZMod K) :
    (∑ x : ZMod K,
      unitCharacterSum q.val (ZMod.castHom (hK q) (ZMod q.val) (m-x)) *
      unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x)) =
      if q = l then (K : ℂ) *
        unitCharacterSum q.val (ZMod.castHom (hK q) (ZMod q.val) m)
      else 0 := by
  by_cases h : q = l
  · subst l
    simp only [if_true]
    exact lifted_ramanujan_self_convolution (hK q) m
  · rw [if_neg h]
    apply actual_unitCharacterSum_mixed_convolution_zero (hK q) (hK l)
    intro hv
    exact h (Subtype.ext hv)

/-- The exact diagonal for two actual companions on a complete common period.
    The weights depend only on the denominator, never on the spatial input x. -/
theorem actual_companion_complete_diagonal {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, periodicCompanion r v (m-x) * periodicCompanion s w x) =
      (K : ℂ) * ∑ l : PositiveLevel Q,
        literalCoefficient r l v * literalCoefficient s l w *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m) := by
  simp_rw [periodicCompanion_expansion hK, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ q : PositiveLevel Q,
      (∑ x : ZMod K, ∑ l : PositiveLevel Q,
        (literalCoefficient r q v *
          unitCharacterSum q.val (ZMod.castHom (hK q) (ZMod q.val) (m-x))) *
        (literalCoefficient s l w *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x))) =
      (K : ℂ) * (literalCoefficient r q v * literalCoefficient s q w *
        unitCharacterSum q.val (ZMod.castHom (hK q) (ZMod q.val) m)) := by
    intro q
    rw [Finset.sum_comm]
    simp_rw [show ∀ l : PositiveLevel Q, ∀ x : ZMod K,
      (literalCoefficient r q v * unitCharacterSum q.val (ZMod.castHom (hK q) (ZMod q.val) (m-x))) *
      (literalCoefficient s l w * unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x)) =
      (literalCoefficient r q v * literalCoefficient s l w) *
      (unitCharacterSum q.val (ZMod.castHom (hK q) (ZMod q.val) (m-x)) *
       unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x)) by intros; ring]
    simp_rw [← Finset.mul_sum, ramanujan_complete_matrix hK]
    simp only [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp_rw [hterm]

/-- The same diagonal with all K natural representatives; subtraction remains modular. -/
theorem actual_companion_complete_diagonal_range {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ n ∈ Finset.range K,
      finiteCompanion r (m-(n : ZMod K)).val v * finiteCompanion s n w) =
      (K : ℂ) * ∑ l : PositiveLevel Q,
        literalCoefficient r l v * literalCoefficient s l w *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m) := by
  rw [← actual_companion_complete_diagonal hK r s v w m,
    ← sum_range_residues_complex K
      (fun x => periodicCompanion r v (m-x) * periodicCompanion s w x)]
  apply Finset.sum_congr rfl
  intro n _
  rw [periodicCompanion_natCast hK]
  rfl

/-- Division by the positive period yields the exact normalized diagonal. -/
theorem normalized_actual_companion_complete_diagonal {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, periodicCompanion r v (m-x) * periodicCompanion s w x) /
        (K : ℂ) =
      ∑ l : PositiveLevel Q, literalCoefficient r l v * literalCoefficient s l w *
        unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m) := by
  rw [actual_companion_complete_diagonal hK]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (NeZero.ne K))

end GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
