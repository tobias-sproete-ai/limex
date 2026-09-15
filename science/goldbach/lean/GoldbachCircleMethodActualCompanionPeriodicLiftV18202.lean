import GoldbachCircleMethodRadicalLocalCoefficientV18201

set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodActualCompanionPeriodicLiftV18202

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866

/-- The literal companion, evaluated on the canonical representative of a
positive common-period residue. No replacement Fourier model is introduced. -/
noncomputable def periodicCompanion {Q K : ℕ} [NeZero K]
    (r : PositiveLevel Q) (w : ℕ → ℂ) (x : ZMod K) : ℂ :=
  finiteCompanion r x.val w

/-- Reduction to a divisor modulus is the existing ring homomorphism. -/
theorem cast_val_eq_reduction {K l : ℕ} [NeZero K] (hl : l ∣ K) (x : ZMod K) :
    (x.val : ZMod l) = ZMod.castHom hl (ZMod l) x := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

/-- Exact agreement with every natural input, under common-period divisibility. -/
theorem periodicCompanion_natCast {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r : PositiveLevel Q) (w : ℕ → ℂ) (N : ℕ) :
    periodicCompanion r w (N : ZMod K) = finiteCompanion r N w := by
  unfold periodicCompanion finiteCompanion
  apply Finset.sum_congr rfl
  intro l _
  rw [cast_val_eq_reduction (hK l)]
  simp only [map_natCast]

/-- The actual natural-input companion has the declared common period. -/
theorem finiteCompanion_periodic {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r : PositiveLevel Q) (w : ℕ → ℂ) :
    Function.Periodic (fun N => finiteCompanion r N w) K := by
  intro N
  change finiteCompanion r (N+K) w = finiteCompanion r N w
  rw [← periodicCompanion_natCast hK r w (N+K),
    ← periodicCompanion_natCast hK r w N]
  simp only [Nat.cast_add, ZMod.natCast_self, add_zero]

/-- The second convolution input is modular subtraction, not truncated
subtraction of canonical natural representatives. -/
theorem periodicCompanion_sub_expansion {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r : PositiveLevel Q) (w : ℕ → ℂ) (m n : ZMod K) :
    periodicCompanion r w (m-n) =
      ∑ l : PositiveLevel Q,
        if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val then
          ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
            unitCharacterSum l.val
              (ZMod.castHom (hK l) (ZMod l.val) m -
               ZMod.castHom (hK l) (ZMod l.val) n) / (l.val.totient : ℂ) *
                w (r.val*l.val)
        else 0 := by
  unfold periodicCompanion finiteCompanion
  apply Finset.sum_congr rfl
  intro l _
  rw [cast_val_eq_reduction (hK l), map_sub]

/-- The common-period premise is explicitly inhabited; the factorial witness
is used only for existence, never as a short-interval approximation. -/
theorem commonPeriod_exists (Q : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∀ l : PositiveLevel Q, l.val ∣ K := by
  refine ⟨Q.factorial, Nat.factorial_pos Q, ?_⟩
  intro l
  exact Nat.dvd_factorial (Nat.pos_of_ne_zero (NeZero.ne l.val))
    (Finset.mem_Icc.mp l.property).2

/-- Complex-valued complete-residue enumeration, preserving all K points. -/
theorem sum_range_residues_complex (K : ℕ) [NeZero K] (g : ZMod K → ℂ) :
    (∑ n ∈ Finset.range K, g (n : ZMod K)) = ∑ x : ZMod K, g x := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ZMod K))
  · intro n _
    exact Finset.mem_univ _
  · intro n hn m hm h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hn),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hm)] using hv
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
  · intro n _
    rfl

/-- The complete cyclic convolution of two literal companions agrees with
canonical residue enumeration. This is not an incomplete-interval transfer. -/
theorem complete_companion_convolution_range {Q K : ℕ} [NeZero K]
    (hK : ∀ l : PositiveLevel Q, l.val ∣ K)
    (r s : PositiveLevel Q) (v w : ℕ → ℂ) (m : ZMod K) :
    (∑ x : ZMod K, periodicCompanion r v x * periodicCompanion s w (m-x)) =
      ∑ n ∈ Finset.range K, finiteCompanion r n v *
        finiteCompanion s (m-(n : ZMod K)).val w := by
  rw [← sum_range_residues_complex K
    (fun x => periodicCompanion r v x * periodicCompanion s w (m-x))]
  apply Finset.sum_congr rfl
  intro n _
  rw [periodicCompanion_natCast hK]
  rfl

open GoldbachCircleMethodSmallConductorPairReserveV18108
open GoldbachCircleMethodPrimitiveRamanujanProjectionV18103

/-- Exact Fourier support of the original Ramanujan kernel at one modulus. -/
theorem ramanujan_dft (q : ℕ) [NeZero q] (a : ZMod q) :
    ZMod.dft (unitCharacterSum q) a = (q : ℂ) * unitIndicator q a := by
  have hf : unitCharacterSum q =
      (fun x : ZMod q => ZMod.dft (unitIndicator q) (-x)) := by
    funext x
    rw [unit_indicator_dft, neg_neg]
  rw [hf, ZMod.dft_comp_neg, ZMod.dft_dft]
  simp only [neg_neg, smul_eq_mul]

/-- The normalized same-modulus cyclic Ramanujan convolution is idempotent.
Mixed denominators on a common period still need a separate orthogonality proof. -/
theorem ramanujan_self_convolution (q : ℕ) [NeZero q] (m : ZMod q) :
    (∑ x : ZMod q, unitCharacterSum q (m-x) * unitCharacterSum q x) =
      (q : ℂ) * unitCharacterSum q m := by
  rw [ramanujan_convolution_dft]
  simp only [ramanujan_dft, unitCharacterSum, unitIndicator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

/-- Exact repetition of a complete complex-valued residue block. -/
theorem repeated_residue_periods_complex (q t : ℕ) [NeZero q] (g : ZMod q → ℂ) :
    (∑ n ∈ Finset.range (t*q), g (n : ZMod q)) =
      (t : ℂ) * ∑ x : ZMod q, g x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [sum_range_residues_complex]
    push_cast
    ring

/-- A divisor reduction repeats each residue exactly K/q times. -/
theorem sum_reduction_exact {K q : ℕ} [NeZero K] [NeZero q]
    (hq : q ∣ K) (g : ZMod q → ℂ) :
    (∑ x : ZMod K, g (ZMod.castHom hq (ZMod q) x)) =
      ((K/q : ℕ) : ℂ) * ∑ y : ZMod q, g y := by
  rw [← sum_range_residues_complex K]
  simp only [map_natCast]
  calc
    _ = ∑ n ∈ Finset.range ((K/q)*q), g (n : ZMod q) := by
      rw [Nat.div_mul_cancel hq]
    _ = _ := repeated_residue_periods_complex q (K/q) g

/-- Same-denominator Ramanujan diagonal on any positive common period.
This does not assert cancellation between different denominators. -/
theorem lifted_ramanujan_self_convolution {K q : ℕ} [NeZero K] [NeZero q]
    (hq : q ∣ K) (m : ZMod K) :
    (∑ x : ZMod K,
      unitCharacterSum q (ZMod.castHom hq (ZMod q) (m-x)) *
      unitCharacterSum q (ZMod.castHom hq (ZMod q) x)) =
      (K : ℂ) * unitCharacterSum q (ZMod.castHom hq (ZMod q) m) := by
  simp only [map_sub]
  rw [sum_reduction_exact hq
    (fun y => unitCharacterSum q (ZMod.castHom hq (ZMod q) m-y) *
      unitCharacterSum q y), ramanujan_self_convolution]
  rw [← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hq]

end GoldbachCircleMethodActualCompanionPeriodicLiftV18202
