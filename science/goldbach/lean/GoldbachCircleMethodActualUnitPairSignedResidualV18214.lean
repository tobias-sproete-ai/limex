import GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
import GoldbachCircleMethodActualUnitPairWeightedReserveV18195
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodActualUnitPairSignedResidualV18214
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodActualUnitPairWeightedReserveV18195
open GoldbachCircleMethodExceptionalModelDiagonalV18107
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213

/-- The literal V194 two-unit carrier with two fixed complex scalar weights. -/
noncomputable def unitPairBracket (r : ℕ) [NeZero r] (m : ℤ)
    (χ : DirichletCharacter ℂ r) (t₁ t₂ : ℂ) : ℂ :=
  ∑ x ∈ unitPairResidues r m, (1-t₁*χ x)*(1-t₂*χ ((m : ZMod r)-x))

/-- Outside the actual two-unit carrier the character product vanishes exactly. -/
theorem unit_pair_product_restrict (r : ℕ) [NeZero r] (m : ℤ)
    (χ : DirichletCharacter ℂ r) :
    (∑ x ∈ unitPairResidues r m, χ x*χ ((m : ZMod r)-x)) =
      ∑ x : ZMod r, χ x*χ ((m : ZMod r)-x) := by
  unfold unitPairResidues
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : IsUnit x
  · by_cases hmx : IsUnit ((m : ZMod r)-x)
    · simp only [hx, hmx, and_self, if_true]
    · simp [hmx, MulChar.map_nonunit χ hmx]
  · simp [hx, MulChar.map_nonunit χ hx]

/-- Restrict the accepted primitive self-convolution, with inverse=self explicit. -/
theorem actual_unit_pair_product (r : ℕ) [NeZero r] (m : ℤ)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hInv : χ⁻¹ = χ) :
    (∑ x ∈ unitPairResidues r m, χ x*χ ((m : ZMod r)-x)) =
      χ (-1)*unitCharacterSum r (m : ZMod r) := by
  rw [unit_pair_product_restrict]
  exact primitive_quadratic_self_convolution r χ hχ hInv (m : ZMod r)

/-- Exact actual bracket; the constant is the actual carrier cardinality. -/
theorem actual_unit_pair_bracket (r : ℕ) [NeZero r] (m : ℤ)
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hInv : χ⁻¹ = χ)
    (t₁ t₂ : ℂ) :
    unitPairBracket r m χ t₁ t₂ =
      (unitPairCount r m : ℂ) -
        (t₁+t₂)*((ArithmeticFunction.moebius r : ℤ) : ℂ)*χ (m : ZMod r) +
        t₁*t₂*χ (-1)*unitCharacterSum r (m : ZMod r) := by
  have hexpand : unitPairBracket r m χ t₁ t₂ =
      (unitPairCount r m : ℂ) -
      t₁*(∑ x ∈ unitPairResidues r m, χ x) -
      t₂*(∑ x ∈ unitPairResidues r m, χ ((m : ZMod r)-x)) +
      t₁*t₂*(∑ x ∈ unitPairResidues r m, χ x*χ ((m : ZMod r)-x)) := by
    unfold unitPairBracket unitPairCount
    calc
      _ = ∑ x ∈ unitPairResidues r m,
          (1-t₁*χ x-t₂*χ ((m : ZMod r)-x) +
            t₁*t₂*(χ x*χ ((m : ZMod r)-x))) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
  rw [hexpand, actual_first_marginal r m χ hχ, actual_second_marginal r m χ hχ,
    actual_unit_pair_product r m χ hχ hInv]
  ring

/-- The integer target for V194/V195 is the same canonical residue reduction. -/
theorem actual_unit_pair_target_readback {K r : ℕ} [NeZero K]
    (hr : r ∣ K) (m : ZMod K) :
    ((m.val : ℤ) : ZMod r) = ZMod.castHom hr (ZMod r) m := by
  simpa only [Int.cast_natCast] using cast_val_eq_reduction hr m

/-- Accounting residual tied to actual P, B and the V194 carrier cardinality.
This definition supplies no sign or estimate. -/
noncomputable def signedDiagonalResidual {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r : PositiveLevel Q)
    (v w : ℕ → ℂ) (m : ZMod K) : ℂ :=
  principalDiagonal hK v w m -
    ((r.val : ℂ)/(r.val.totient : ℂ)^2) *
      (unitPairCount r.val (m.val : ℤ) : ℂ) * coupledDiagonal hK r v w m

/-- The original frozen model splits exactly into its actual signed residual
and the actual unit-pair bracket. No positive-factor inference is made. -/
theorem actual_frozen_model_unit_pair_residual {Q K : ℕ} [NeZero K]
    (hQ : 1 ≤ Q) (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : χ.val⁻¹ = χ.val) (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (m : ZMod K) :
    (∑ x : ZMod K, frozenCoefficient hQ r χ v t₁ (m-x) *
      frozenCoefficient hQ r χ w t₂ x) / (K : ℂ) =
    signedDiagonalResidual hK r v w m +
      ((r.val : ℂ)/(r.val.totient : ℂ)^2) * coupledDiagonal hK r v w m *
        unitPairBracket r.val (m.val : ℤ) χ.val t₁ t₂ := by
  rw [actual_frozen_model_complete_diagonal hQ hK r χ hInv,
    actual_unit_pair_bracket r.val (m.val : ℤ) χ.val χ.property hInv,
    actual_unit_pair_target_readback (hK r) m]
  unfold signedDiagonalResidual
  ring

end GoldbachCircleMethodActualUnitPairSignedResidualV18214
