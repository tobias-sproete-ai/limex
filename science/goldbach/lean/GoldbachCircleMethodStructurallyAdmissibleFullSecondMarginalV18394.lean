import GoldbachCircleMethodCanonicalFullSecondOffDivisorQuarticV18393
import GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-!
# Goldbach V1.8.394: structurally admissible full second marginal

The three low product channels left outside the pairwise-period estimate can
occur only at active conductor one or two.  The admissible active-slot contract
already excludes conductor one.  This module proves directly that every
Dirichlet character modulo two is principal, hence none is primitive.  An
admissible primitive active slot therefore has conductor at least three, where
V1.8.392 makes the complete low-frequency target contribution exactly zero.

Consequently the literal full second marginal of the original finite coupled
diagonal equals its off-divisor part and inherits the V1.8.393 `Q^4` bound.
No reserve absorption or Goldbach statement is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodStructurallyAdmissibleFullSecondMarginalV18394

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledSecondMarginalSourceBindingV18391
open GoldbachCircleMethodCanonicalFullSecondOffDivisorQuarticV18393
open GoldbachCircleMethodCoupledSecondLowFrequencyClassificationV18392
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The unit group modulo two is trivial, so every Dirichlet character at
level two is the principal character. -/
theorem dirichletCharacter_mod_two_eq_one
    (chi : DirichletCharacter ℂ 2) : chi = 1 := by
  apply MulChar.ext
  intro u
  have hu_ne : (u : ZMod 2) ≠ 0 := Units.ne_zero u
  have hu_val_ne : u.val.val ≠ 0 := (ZMod.val_ne_zero u.val).mpr hu_ne
  have hu_val_lt : u.val.val < 2 := ZMod.val_lt u.val
  have hu_val : u.val.val = 1 := by omega
  have hu : u = 1 := by
    apply Units.ext
    exact (ZMod.val_eq_one (by omega) u.val).mp hu_val
  subst u
  change chi (1 : ZMod 2) = (1 : DirichletCharacter ℂ 2) (1 : ZMod 2)
  simp

/-- No level-two Dirichlet character can be primitive. -/
theorem no_primitive_dirichletCharacter_mod_two
    (chi : DirichletCharacter ℂ 2) : ¬ chi.IsPrimitive := by
  intro hprim
  have hchi : chi = 1 := dirichletCharacter_mod_two_eq_one chi
  have hcond : chi.conductor = 2 := hprim
  rw [hchi, DirichletCharacter.conductor_one] at hcond
  omega

/-- A primitive character whose conductor is greater than one has conductor
at least three; the only delicate finite level is two. -/
theorem three_le_of_primitive_and_one_lt
    (r : ℕ) [NeZero r]
    (chi : DirichletCharacter ℂ r)
    (hprim : chi.IsPrimitive) (hr : 1 < r) : 3 ≤ r := by
  by_contra hthree
  have hr2 : r = 2 := by omega
  subst r
  exact no_primitive_dirichletCharacter_mod_two chi hprim

/-- Every structurally admissible active slot has conductor at least three. -/
theorem admissible_active_conductor_three_le {Q : ℕ}
    (e : StructurallyAdmissibleActiveSlot Q) :
    3 ≤ e.val.1.val :=
  three_le_of_primitive_and_one_lt e.val.1.val e.val.2.val
    e.val.2.property e.property.1

/-- The low-frequency second marginal vanishes for every structurally
admissible active slot. -/
theorem admissible_lowFrequencyCoupledSecondMarginalTargetSum_eq_zero
    {Q : ℕ} (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) :
    lowFrequencyCoupledSecondMarginalTargetSum
      e.val.1 v w B A T b = 0 :=
  lowFrequencyCoupledSecondMarginalTargetSum_eq_zero_of_three_le
    e.val.1 (admissible_active_conductor_three_le e) v w B A T b

/-- Literal full second-marginal contribution from the original finite
coupled diagonal, including the active-level normalization and `chi(-1)`. -/
noncomputable def normalizedActualCoupledSecondMarginal
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) : ℂ :=
  ((e.val.1.val : ℂ) / ((e.val.1.val.totient : ℂ) ^ 2)) *
    e.val.2.val (-1) *
      actualCoupledSecondMarginalTargetSum
        hK e.val.1 v w B A T b

/-- On an admissible active slot, the full literal second marginal is exactly
the already controlled off-divisor term. -/
theorem normalizedActualCoupledSecondMarginal_eq_offDivisor
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (B A T : ℕ) (b : ℝ) :
    normalizedActualCoupledSecondMarginal hK e v w B A T b =
      normalizedOffDivisorCoupledSecondMarginal
        e.val.1 e.val.2.val v w B A T b := by
  unfold normalizedActualCoupledSecondMarginal
    normalizedOffDivisorCoupledSecondMarginal
  rw [actualCoupledSecondMarginalTargetSum_eq_low_add_off,
    admissible_lowFrequencyCoupledSecondMarginalTargetSum_eq_zero e,
    zero_add]

/-- End-to-end `Q^4` estimate for the full literal second marginal of every
structurally admissible active slot. -/
theorem normalized_actual_coupled_second_marginal_norm_le_quartic
    {Q K : ℕ} [NeZero K]
    (hKperiod : ∀ q : PositiveLevel Q, q.val ∣ K)
    (e : StructurallyAdmissibleActiveSlot Q)
    (v w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ n, ‖v n‖ ≤ M) (hw : ∀ n, ‖w n‖ ≤ M)
    (B A Kgrow S : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hBA : B ≤ A)
    (hNonempty : 2 * (B / 2 + 1) ≤ A)
    (hKgrow : 1 ≤ Kgrow)
    (hGrowingLast : A + 2 * (Kgrow - 1) ≤
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B)
    (hS : 1 ≤ S)
    (hShrinkingFirst :
      GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368.blockPairTurningTarget B ≤
        A + 2 * Kgrow)
    (hFinal : A + 2 * Kgrow + 2 * (S - 1) ≤ 2 * B) :
    ‖normalizedActualCoupledSecondMarginal
        hKperiod e v w B A (Kgrow + S) b‖ ≤
      2 * (B : ℝ) * (3 + 4 * b) * (Q : ℝ) ^ 4 * M ^ 2 := by
  rw [normalizedActualCoupledSecondMarginal_eq_offDivisor]
  exact normalized_off_divisor_coupled_second_marginal_norm_le_quartic
    e.val.1 e.val.2.val v w M hM hv hw B A Kgrow S b hb hB hBA
      hNonempty hKgrow hGrowingLast hS hShrinkingFirst hFinal

end GoldbachCircleMethodStructurallyAdmissibleFullSecondMarginalV18394
