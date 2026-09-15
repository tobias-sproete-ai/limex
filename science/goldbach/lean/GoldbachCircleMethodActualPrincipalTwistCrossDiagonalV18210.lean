import GoldbachCircleMethodActualTwistedCompleteProjectionV18209
set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodActualCompanionCompleteDiagonalV18204
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208
open GoldbachCircleMethodActualTwistedCompleteProjectionV18209

local instance productNeZero (r l : ℕ) [NeZero r] [NeZero l] : NeZero (r*l) :=
  ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

/-- Construct the product level only AFTER its coupled cutoff has been proved. -/
def boundedProductLevel {Q : ℕ} (r l : PositiveLevel Q) (h : r.val*l.val ≤ Q) :
    PositiveLevel Q :=
  ⟨r.val*l.val, Finset.mem_Icc.mpr ⟨Nat.mul_pos (NeZero.pos r.val) (NeZero.pos l.val), h⟩⟩

/-- Actual character and Ramanujan reductions agree with the genuine product twist. -/
theorem twist_lift_readback {K r l : ℕ} [NeZero K] [NeZero r] [NeZero l]
    (hr : r ∣ K) (hl : l ∣ K) (hrl : r*l ∣ K)
    (χ : DirichletCharacter ℂ r) (x : ZMod K) :
    twistedRamanujan r l χ (ZMod.castHom hrl (ZMod (r*l)) x) =
      χ (ZMod.castHom hr (ZMod r) x) *
        unitCharacterSum l (ZMod.castHom hl (ZMod l) x) := by
  unfold twistedRamanujan
  have h1 := congrArg (fun f : ZMod K →+* ZMod r => f x)
    (ZMod.castHom_comp (Nat.dvd_mul_right r l) hrl)
  have h2 := congrArg (fun f : ZMod K →+* ZMod l => f x)
    (ZMod.castHom_comp (Nat.dvd_mul_left l r) hrl)
  simp only [RingHom.comp_apply] at h1 h2
  rw [h1, h2]

/-- The old conductor-one companion keeps the literal principal coefficient. -/
theorem principal_literalCoefficient {Q : ℕ} (hQ : 1 ≤ Q) (q : PositiveLevel Q)
    (v : ℕ → ℂ) :
    literalCoefficient (oneLevel hQ) q v =
      ((ArithmeticFunction.moebius q.val : ℤ) : ℂ) / (q.val.totient : ℂ) * v q.val := by
  have hq : q.val ≤ Q := (Finset.mem_Icc.mp q.property).2
  simp [literalCoefficient, oneLevel, hq]

/-- Exact principal companion versus one admitted literal twist, on a full period. -/
theorem principal_twisted_block_convolution {Q K : ℕ} [NeZero K]
    (hQ : 1 ≤ Q) (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r l : PositiveLevel Q) (hadm : r.val*l.val ≤ Q) (hcop : Nat.Coprime r.val l.val)
    (χ : DirichletCharacter ℂ r.val) (hχ : χ.IsPrimitive)
    (v : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, periodicCompanion (oneLevel hQ) v (m-x) *
      (χ (ZMod.castHom (hK r) (ZMod r.val) x) *
        unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x))) =
      (K : ℂ) *
      (((ArithmeticFunction.moebius (r.val*l.val) : ℤ) : ℂ) /
        ((r.val*l.val).totient : ℂ) * v (r.val*l.val)) *
      (χ (ZMod.castHom (hK r) (ZMod r.val) m) *
        unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m)) := by
  let t := boundedProductLevel r l hadm
  have ht : t.val = r.val*l.val := rfl
  have hprod : r.val*l.val ∣ K := hK t
  simp_rw [periodicCompanion_expansion hK, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ q : PositiveLevel Q,
      (∑ x : ZMod K,
        (literalCoefficient (oneLevel hQ) q v *
          unitCharacterSum q.val (ZMod.castHom (hK q) (ZMod q.val) (m-x))) *
        (χ (ZMod.castHom (hK r) (ZMod r.val) x) *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x))) =
      literalCoefficient (oneLevel hQ) q v *
        (if q.val = r.val*l.val then (K : ℂ) *
          (χ (ZMod.castHom (hK r) (ZMod r.val) m) *
            unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m)) else 0) := by
    intro q
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    simp_rw [← twist_lift_readback (hK r) (hK l) hprod χ]
    exact twisted_ramanujan_complete_matrix r.val l.val (hK q) hprod hcop χ hχ m
  simp_rw [hterm]
  rw [Finset.sum_eq_single t]
  · rw [ht, if_pos rfl, principal_literalCoefficient hQ]
    change (((ArithmeticFunction.moebius (r.val*l.val) : ℤ) : ℂ) /
      ((r.val*l.val).totient : ℂ) * v (r.val*l.val)) * _ = _
    ring
  · intro q _ hqt
    have hneq : q.val ≠ r.val*l.val := fun he => hqt (Subtype.ext (he.trans ht.symm))
    rw [if_neg hneq, mul_zero]
  · simp

/-- The canonical representative does not alter the actual V121 coefficient. -/
theorem periodic_windowCoefficient_readback {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K) (r : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (w : ℕ → ℂ) (x : ZMod K) :
    windowCoefficient r x.val w χ =
      ((r.val : ℂ)/(r.val.totient : ℂ)) *
        χ.val (ZMod.castHom (hK r) (ZMod r.val) x) * periodicCompanion r w x := by
  unfold windowCoefficient periodicCompanion
  rw [cast_val_eq_reduction (hK r)]

/-- Coprime arithmetic coefficient normalization, also for nonsquarefree r.
The two weights multiply; there is no conjugation or norm-square replacement. -/
theorem coprime_cross_coefficient (r l : ℕ) [NeZero r] [NeZero l]
    (hcop : Nat.Coprime r l) (v w : ℂ) :
    ((r : ℂ)/(r.totient : ℂ)) *
      (((ArithmeticFunction.moebius l : ℤ) : ℂ)/(l.totient : ℂ)*w) *
      (((ArithmeticFunction.moebius (r*l) : ℤ) : ℂ)/((r*l).totient : ℂ)*v) =
      ((r : ℂ)*((ArithmeticFunction.moebius r : ℤ) : ℂ)/(r.totient : ℂ)^2) *
      ((((ArithmeticFunction.moebius l : ℤ) : ℂ)^2)/(l.totient : ℂ)^2*v*w) := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    Nat.totient_mul hcop]
  push_cast
  have hr : (r.totient : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne r.totient)
  have hl : (l.totient : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne l.totient)
  field_simp [hr,hl]

/-- Complete-period A*C diagonal for the original principal companion and actual
V121 primitive-character windowCoefficient. All admission gates remain literal. -/
theorem actual_principal_window_complete_cross {Q K : ℕ} [NeZero K]
    (hQ : 1 ≤ Q) (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, periodicCompanion (oneLevel hQ) v (m-x) *
      windowCoefficient r x.val w χ) =
      (K : ℂ) *
      ((r.val : ℂ)*((ArithmeticFunction.moebius r.val : ℤ) : ℂ)/(r.val.totient : ℂ)^2) *
      χ.val (ZMod.castHom (hK r) (ZMod r.val) m) *
      ∑ l : PositiveLevel Q, if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val then
        (((ArithmeticFunction.moebius l.val : ℤ) : ℂ)^2)/(l.val.totient : ℂ)^2 *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m) *
          v (r.val*l.val) * w (r.val*l.val)
      else 0 := by
  have hexpand :
      (∑ x : ZMod K, periodicCompanion (oneLevel hQ) v (m-x) *
        windowCoefficient r x.val w χ) =
      ∑ l : PositiveLevel Q,
        ((r.val : ℂ)/(r.val.totient : ℂ)) * literalCoefficient r l w *
        ∑ x : ZMod K, periodicCompanion (oneLevel hQ) v (m-x) *
          (χ.val (ZMod.castHom (hK r) (ZMod r.val) x) *
            unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x)) := by
    calc
      _ = ∑ x : ZMod K, ∑ l : PositiveLevel Q,
          (((r.val : ℂ)/(r.val.totient : ℂ)) * literalCoefficient r l w) *
          (periodicCompanion (oneLevel hQ) v (m-x) *
            (χ.val (ZMod.castHom (hK r) (ZMod r.val) x) *
              unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) x))) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [periodic_windowCoefficient_readback hK,
          periodicCompanion_expansion hK r w]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
  rw [hexpand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hadm : r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · rw [if_pos hadm, principal_twisted_block_convolution hQ hK r l
      hadm.1 hadm.2 χ.val χ.property v m]
    have hc := coprime_cross_coefficient r.val l.val hadm.2
      (v (r.val*l.val)) (w (r.val*l.val))
    unfold literalCoefficient
    rw [if_pos hadm]
    calc
      _ = (K : ℂ) *
        (((r.val : ℂ)/(r.val.totient : ℂ)) *
          (((ArithmeticFunction.moebius l.val : ℤ) : ℂ)/(l.val.totient : ℂ) * w (r.val*l.val)) *
          (((ArithmeticFunction.moebius (r.val*l.val) : ℤ) : ℂ) /
            ((r.val*l.val).totient : ℂ) * v (r.val*l.val))) *
        (χ.val (ZMod.castHom (hK r) (ZMod r.val) m) *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m)) := by ring
      _ = _ := by rw [hc]; ring
  · simp only [literalCoefficient, hadm, if_false, mul_zero, zero_mul]

/-- Division by the actual positive complete period, not an assumed average oracle. -/
theorem normalized_actual_principal_window_complete_cross {Q K : ℕ} [NeZero K]
    (hQ : 1 ≤ Q) (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, periodicCompanion (oneLevel hQ) v (m-x) *
      windowCoefficient r x.val w χ) / (K : ℂ) =
      ((r.val : ℂ)*((ArithmeticFunction.moebius r.val : ℤ) : ℂ)/(r.val.totient : ℂ)^2) *
      χ.val (ZMod.castHom (hK r) (ZMod r.val) m) *
      ∑ l : PositiveLevel Q, if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val then
        (((ArithmeticFunction.moebius l.val : ℤ) : ℂ)^2)/(l.val.totient : ℂ)^2 *
          unitCharacterSum l.val (ZMod.castHom (hK l) (ZMod l.val) m) *
          v (r.val*l.val) * w (r.val*l.val)
      else 0 := by
  rw [actual_principal_window_complete_cross hQ hK r χ v w m]
  have hK0 : (K : ℂ) ≠ 0 := NeZero.ne (K : ℂ)
  field_simp

end GoldbachCircleMethodActualPrincipalTwistCrossDiagonalV18210
