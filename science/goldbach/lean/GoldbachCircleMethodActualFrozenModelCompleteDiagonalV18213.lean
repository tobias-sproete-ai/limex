import GoldbachCircleMethodActualWindowCCDiagonalV18212
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
open GoldbachCircleMethodActualWindowCCDiagonalV18212

/-- The actual principal finite diagonal, not a free scalar input. -/
noncomputable def principalDiagonal {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (v w : ℕ → ℂ) (m : ZMod K) : ℂ :=
  ∑ q : PositiveLevel Q,
    (((ArithmeticFunction.moebius q.val : ℤ) : ℂ)^2)/(q.val.totient : ℂ)^2 *
      unitCharacterSum q.val (ZMod.castHom (hK q) (ZMod q.val) m) * v q.val * w q.val

/-- The same actual coupled finite diagonal from V210 and V212, without sign claims. -/
noncomputable def coupledDiagonal {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r : PositiveLevel Q)
    (v w : ℕ → ℂ) (m : ZMod K) : ℂ :=
  ∑ l : PositiveLevel Q, if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val then
    (((ArithmeticFunction.moebius l.val : ℤ) : ℂ)^2)/(l.val.totient : ℂ)^2 *
      unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m) *
      v (r.val*l.val) * w (r.val*l.val)
  else 0

/-- Fixed scalar adjustment of the unchanged original A and C, not a spatial power. -/
noncomputable def frozenCoefficient {Q K : ℕ} [NeZero K]
    (hQ : 1 ≤ Q) (r : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v : ℕ → ℂ) (t : ℂ) (x : ZMod K) : ℂ :=
  periodicCompanion (oneLevel hQ) v x - t * windowCoefficient r x.val v χ

/-- Exact substitution x -> m-x on the full residue group. -/
theorem complete_convolution_comm {K : ℕ} [NeZero K]
    (f g : ZMod K → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, f (m-x)*g x) = ∑ x : ZMod K, g (m-x)*f x := by
  let e : ZMod K ≃ ZMod K :=
    { toFun := fun x => m-x
      invFun := fun x => m-x
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  calc
    _ = ∑ x : ZMod K, g (m-e x)*f (e x) := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [e]
      simp [mul_comm]
    _ = _ := e.sum_comp (fun x => g (m-x)*f x)

/-- Exchanging denominator weights leaves the actual coupled sum unchanged. -/
theorem coupledDiagonal_comm {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r : PositiveLevel Q)
    (v w : ℕ → ℂ) (m : ZMod K) :
    coupledDiagonal hK r v w m = coupledDiagonal hK r w v m := by
  unfold coupledDiagonal
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> ring

/-- Principal specialization of the accepted original A*A identity. -/
theorem actual_principal_complete_diagonal {Q K : ℕ} [NeZero K]
    (hQ : 1 ≤ Q) (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, periodicCompanion (oneLevel hQ) v (m-x) *
      periodicCompanion (oneLevel hQ) w x) / (K : ℂ) =
    principalDiagonal hK v w m := by
  rw [normalized_actual_companion_complete_diagonal hK]
  unfold principalDiagonal
  apply Finset.sum_congr rfl
  intro q _
  rw [principal_literalCoefficient hQ, principal_literalCoefficient hQ]
  ring

/-- A*C with the original coupled sum named definitionally. -/
theorem actual_ac_bound_diagonal {Q K : ℕ} [NeZero K]
    (hQ : 1 ≤ Q) (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, periodicCompanion (oneLevel hQ) v (m-x) *
      windowCoefficient r x.val w χ) / (K : ℂ) =
    ((r.val : ℂ)*((ArithmeticFunction.moebius r.val : ℤ) : ℂ)/(r.val.totient : ℂ)^2) *
      χ.val (ZMod.castHom (hK r) (ZMod r.val) m) * coupledDiagonal hK r v w m :=
  normalized_actual_principal_window_complete_cross hQ hK r χ v w m

/-- C*A follows by an actual residue permutation, not an assumed symmetry. -/
theorem actual_ca_bound_diagonal {Q K : ℕ} [NeZero K]
    (hQ : 1 ≤ Q) (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, windowCoefficient r (m-x).val v χ *
      periodicCompanion (oneLevel hQ) w x) / (K : ℂ) =
    ((r.val : ℂ)*((ArithmeticFunction.moebius r.val : ℤ) : ℂ)/(r.val.totient : ℂ)^2) *
      χ.val (ZMod.castHom (hK r) (ZMod r.val) m) * coupledDiagonal hK r v w m := by
  rw [complete_convolution_comm (fun x : ZMod K => windowCoefficient r x.val v χ)
    (periodicCompanion (oneLevel hQ) w) m]
  rw [actual_ac_bound_diagonal hQ hK, coupledDiagonal_comm hK r w v]

/-- C*C retains the explicit inverse=self condition and has no mu(r) prefactor. -/
theorem actual_cc_bound_diagonal {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : χ.val⁻¹ = χ.val) (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, windowCoefficient r (m-x).val v χ *
      windowCoefficient r x.val w χ) / (K : ℂ) =
    ((r.val : ℂ)/(r.val.totient : ℂ)^2)*χ.val (-1) *
      unitCharacterSum r.val (ZMod.castHom (hK r) (ZMod r.val) m) *
      coupledDiagonal hK r v w m :=
  normalized_actual_window_complete_self_convolution hK r χ hInv v w m

/-- Finite bilinearity for two fixed scalar adjustments, with the two cross signs. -/
theorem complete_average_bilinear {K : ℕ} [NeZero K]
    (f g h k : ZMod K → ℂ) (t₁ t₂ : ℂ) (m : ZMod K) :
    (∑ x : ZMod K, (f (m-x)-t₁*g (m-x))*(h x-t₂*k x)) / (K : ℂ) =
    (∑ x : ZMod K, f (m-x)*h x)/(K : ℂ) -
    t₂*((∑ x : ZMod K, f (m-x)*k x)/(K : ℂ)) -
    t₁*((∑ x : ZMod K, g (m-x)*h x)/(K : ℂ)) +
    t₁*t₂*((∑ x : ZMod K, g (m-x)*k x)/(K : ℂ)) := by
  have hexpand :
      (∑ x : ZMod K, (f (m-x)-t₁*g (m-x))*(h x-t₂*k x)) =
      (∑ x : ZMod K, f (m-x)*h x) -
      t₂*(∑ x : ZMod K, f (m-x)*k x) -
      t₁*(∑ x : ZMod K, g (m-x)*h x) +
      t₁*t₂*(∑ x : ZMod K, g (m-x)*k x) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hexpand]
  ring

/-- Complete exact diagonal of the actual frozen A-tC model.
No positivity, variable spatial power, incomplete interval or outer family is asserted. -/
theorem actual_frozen_model_complete_diagonal {Q K : ℕ} [NeZero K]
    (hQ : 1 ≤ Q) (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : χ.val⁻¹ = χ.val) (v w : ℕ → ℂ) (t₁ t₂ : ℂ) (m : ZMod K) :
    (∑ x : ZMod K, frozenCoefficient hQ r χ v t₁ (m-x) *
      frozenCoefficient hQ r χ w t₂ x) / (K : ℂ) =
    principalDiagonal hK v w m +
      ((r.val : ℂ)/(r.val.totient : ℂ)^2) *
      (t₁*t₂*χ.val (-1)*unitCharacterSum r.val (ZMod.castHom (hK r) (ZMod r.val) m) -
        (t₁+t₂)*((ArithmeticFunction.moebius r.val : ℤ) : ℂ) *
          χ.val (ZMod.castHom (hK r) (ZMod r.val) m)) *
      coupledDiagonal hK r v w m := by
  unfold frozenCoefficient
  rw [complete_average_bilinear
    (periodicCompanion (oneLevel hQ) v) (fun x => windowCoefficient r x.val v χ)
    (periodicCompanion (oneLevel hQ) w) (fun x => windowCoefficient r x.val w χ)]
  rw [actual_principal_complete_diagonal hQ hK, actual_ac_bound_diagonal hQ hK,
    actual_ca_bound_diagonal hQ hK, actual_cc_bound_diagonal hK r χ hInv]
  ring

end GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
