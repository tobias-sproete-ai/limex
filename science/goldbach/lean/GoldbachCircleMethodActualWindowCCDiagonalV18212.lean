import GoldbachCircleMethodActualTwistSelfConvolutionV18211
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodActualWindowCCDiagonalV18212
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208
open GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
open GoldbachCircleMethodActualTwistSelfConvolutionV18211

local instance productNeZero (r l : ℕ) [NeZero r] [NeZero l] : NeZero (r*l) :=
  ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

/-- Expansion of the actual unchanged V121 coefficient, retaining literal admission. -/
theorem actual_window_expansion {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (w : ℕ → ℂ) (x : ZMod K) :
    windowCoefficient r x.val w χ =
    ((r.val : ℂ)/(r.val.totient : ℂ)) *
      ∑ l : PositiveLevel Q, literalCoefficient r l w *
        (χ.val (ZMod.castHom (hK r) (ZMod r.val) x) *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x)) := by
  rw [periodic_windowCoefficient_readback hK, periodicCompanion_expansion hK]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Bridge the accepted actual twist matrix to the original component reductions.
Product divisibility is derived only after both coupled cutoffs are admitted. -/
theorem admitted_window_block_matrix {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r l k : PositiveLevel Q)
    (hl : r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val)
    (hk : r.val*k.val ≤ Q ∧ Nat.Coprime r.val k.val)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : χ.val⁻¹ = χ.val) (m : ZMod K) :
    (∑ x : ZMod K,
      (χ.val (ZMod.castHom (hK r) (ZMod r.val) (m-x)) *
        unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) (m-x))) *
      (χ.val (ZMod.castHom (hK r) (ZMod r.val) x) *
        unitCharacterSum k.val (ZMod.castHom (hK k) (ZMod k.val) x))) =
    if l = k then ((K : ℂ)/(r.val : ℂ))*χ.val (-1) *
      unitCharacterSum r.val (ZMod.castHom (hK r) (ZMod r.val) m) *
      unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m)
    else 0 := by
  have hrl : r.val*l.val ∣ K := hK (boundedProductLevel r l hl.1)
  have hrk : r.val*k.val ∣ K := hK (boundedProductLevel r k hk.1)
  simp_rw [← twist_lift_readback (hK r) (hK l) hrl χ.val,
    ← twist_lift_readback (hK r) (hK k) hrk χ.val]
  have hm := twistedRamanujan_complete_matrix r.val l.val hrl hrk hl.2 hk.2
    χ.val χ.property hInv m
  simpa only [Subtype.val_inj] using hm

/-- Collapse the actual weighted row without inventing divisibility for excluded k. -/
theorem actual_weighted_twist_row {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r l : PositiveLevel Q)
    (hl : r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : χ.val⁻¹ = χ.val) (w : ℕ → ℂ) (m : ZMod K) :
    (∑ k : PositiveLevel Q, literalCoefficient r k w *
      ∑ x : ZMod K,
        (χ.val (ZMod.castHom (hK r) (ZMod r.val) (m-x)) *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) (m-x))) *
        (χ.val (ZMod.castHom (hK r) (ZMod r.val) x) *
          unitCharacterSum k.val (ZMod.castHom (hK k) (ZMod k.val) x))) =
    literalCoefficient r l w *
      (((K : ℂ)/(r.val : ℂ))*χ.val (-1) *
        unitCharacterSum r.val (ZMod.castHom (hK r) (ZMod r.val) m) *
        unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m)) := by
  rw [Finset.sum_eq_single l]
  · rw [admitted_window_block_matrix hK r l l hl hl χ hInv, if_pos rfl]
  · intro k _ hkl
    by_cases hk : r.val*k.val ≤ Q ∧ Nat.Coprime r.val k.val
    · rw [admitted_window_block_matrix hK r l k hl hk χ hInv, if_neg hkl.symm,
        mul_zero]
    · simp only [literalCoefficient, hk, if_false, zero_mul]
  · simp

/-- Exact coefficient algebra: C*C has r/phi(r)^2, not r*mu(r)/phi(r)^2. -/
theorem cc_diagonal_coefficient (r l K : ℕ) [NeZero r] [NeZero l]
    (v w : ℂ) :
    ((r : ℂ)/(r.totient : ℂ))^2 *
      (((ArithmeticFunction.moebius l : ℤ) : ℂ)/(l.totient : ℂ)*v) *
      (((ArithmeticFunction.moebius l : ℤ) : ℂ)/(l.totient : ℂ)*w) *
      ((K : ℂ)/(r : ℂ)) =
    (K : ℂ)*((r : ℂ)/(r.totient : ℂ)^2) *
      ((((ArithmeticFunction.moebius l : ℤ) : ℂ)^2)/(l.totient : ℂ)^2*v*w) := by
  have hr : (r : ℂ) ≠ 0 := NeZero.ne (r : ℂ)
  have hpr : (r.totient : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne r.totient)
  have hpl : (l.totient : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne l.totient)
  field_simp [hr,hpr,hpl]

/-- Full C*C convolution of the actual V121 coefficients on a complete common
period. Inverse=self is explicit; the original complex weight product is retained. -/
theorem actual_window_complete_self_convolution {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : χ.val⁻¹ = χ.val) (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, windowCoefficient r (m-x).val v χ *
      windowCoefficient r x.val w χ) =
    (K : ℂ)*((r.val : ℂ)/(r.val.totient : ℂ)^2)*χ.val (-1) *
      unitCharacterSum r.val (ZMod.castHom (hK r) (ZMod r.val) m) *
      ∑ l : PositiveLevel Q, if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val then
        (((ArithmeticFunction.moebius l.val : ℤ) : ℂ)^2)/(l.val.totient : ℂ)^2 *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m) *
          v (r.val*l.val) * w (r.val*l.val)
      else 0 := by
  let γ : ℂ := (r.val : ℂ)/(r.val.totient : ℂ)
  let F (l : PositiveLevel Q) (x : ZMod K) : ℂ :=
    χ.val (ZMod.castHom (hK r) (ZMod r.val) x) *
      unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x)
  have hexpand (u : ℕ → ℂ) (x : ZMod K) :
      windowCoefficient r x.val u χ = γ * ∑ l : PositiveLevel Q,
        literalCoefficient r l u * F l x := actual_window_expansion hK r χ u x
  have hsplit :
      (∑ x : ZMod K, windowCoefficient r (m-x).val v χ *
        windowCoefficient r x.val w χ) =
      ∑ l : PositiveLevel Q, γ^2*literalCoefficient r l v *
        (∑ k : PositiveLevel Q, literalCoefficient r k w *
          ∑ x : ZMod K, F l (m-x)*F k x) := by
    calc
      _ = ∑ x : ZMod K, ∑ l : PositiveLevel Q, ∑ k : PositiveLevel Q,
          (γ^2*literalCoefficient r l v) *
            (literalCoefficient r k w * (F l (m-x)*F k x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hexpand v (m-x), hexpand w x]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        simp only [Finset.mul_sum]
  rw [hsplit, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · have hrow := actual_weighted_twist_row hK r l hl χ hInv w m
    change (∑ k : PositiveLevel Q, literalCoefficient r k w *
      ∑ x : ZMod K, F l (m-x)*F k x) = _ at hrow
    rw [hrow, if_pos hl]
    dsimp only [γ]
    unfold literalCoefficient
    simp only [if_pos hl]
    have hc := cc_diagonal_coefficient r.val l.val K
      (v (r.val*l.val)) (w (r.val*l.val))
    calc
      _ = (((r.val : ℂ)/(r.val.totient : ℂ))^2 *
        (((ArithmeticFunction.moebius l.val : ℤ) : ℂ)/(l.val.totient : ℂ)*v (r.val*l.val)) *
        (((ArithmeticFunction.moebius l.val : ℤ) : ℂ)/(l.val.totient : ℂ)*w (r.val*l.val)) *
        ((K : ℂ)/(r.val : ℂ))) *
        (χ.val (-1) *
          unitCharacterSum r.val (ZMod.castHom (hK r) (ZMod r.val) m) *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m)) := by ring
      _ = _ := by rw [hc]; ring
  · simp only [literalCoefficient, hl, if_false, mul_zero, zero_mul]

/-- Normalized complete-period C*C identity; no positive norm square is asserted. -/
theorem normalized_actual_window_complete_self_convolution {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (hInv : χ.val⁻¹ = χ.val) (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, windowCoefficient r (m-x).val v χ *
      windowCoefficient r x.val w χ) / (K : ℂ) =
    ((r.val : ℂ)/(r.val.totient : ℂ)^2)*χ.val (-1) *
      unitCharacterSum r.val (ZMod.castHom (hK r) (ZMod r.val) m) *
      ∑ l : PositiveLevel Q, if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val then
        (((ArithmeticFunction.moebius l.val : ℤ) : ℂ)^2)/(l.val.totient : ℂ)^2 *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m) *
          v (r.val*l.val) * w (r.val*l.val)
      else 0 := by
  rw [actual_window_complete_self_convolution hK r χ hInv v w m]
  have hK0 : (K : ℂ) ≠ 0 := NeZero.ne (K : ℂ)
  field_simp

end GoldbachCircleMethodActualWindowCCDiagonalV18212
