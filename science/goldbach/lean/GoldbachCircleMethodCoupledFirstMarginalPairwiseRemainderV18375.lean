import GoldbachCircleMethodCoupledFirstMarginalParityDichotomyV18374
import GoldbachCircleMethodExactPrincipalBoundaryCostV18126

/-!
# Goldbach V1.8.375: pairwise-period remainder for the coupled first marginal

The odd-conductor branch of V1.8.374 has zero mean on the exact pairwise
period `r*l`.  Quotient/remainder decomposition therefore removes every full
period.  The surviving prefix has length below `r*l`, while the Ramanujan
factor has norm at most `phi(l)`.  This gives the explicit boundary cost
`r*l*phi(l)` without a global common LCM.

No sum over companion levels and no reserve absorption is claimed here.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCoupledFirstMarginalPairwiseRemainderV18375

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodExactPrincipalBoundaryCostV18126
open GoldbachCircleMethodCoupledFirstMarginalPairwisePeriodV18373

variable (r l : ℕ) [NeZero r] [NeZero l]

local instance productNeZero : NeZero (r * l) :=
  ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

omit [NeZero r] in
/-- Pointwise norm of the source-matched mixed character--Ramanujan factor. -/
theorem coupled_first_marginal_term_norm_le
    (chi : DirichletCharacter ℂ r) (N : ℕ) :
    ‖(((ArithmeticFunction.moebius r : ℤ) : ℂ) * chi (N : ZMod r)) *
        unitCharacterSum l (N : ZMod l)‖ ≤ (l.totient : ℝ) := by
  rw [norm_mul, norm_mul]
  have hmu : ‖((ArithmeticFunction.moebius r : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := r))
  have hleft :
      ‖((ArithmeticFunction.moebius r : ℤ) : ℂ)‖ * ‖chi (N : ZMod r)‖ ≤ 1 := by
    exact (mul_le_mul hmu (chi.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  exact (mul_le_mul hleft (unit_character_norm_le_totient l (N : ZMod l))
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Every incomplete consecutive-even-target prefix on the odd-conductor
branch is bounded by one pairwise-period boundary. -/
theorem coupled_first_marginal_prefix_norm_le
    (hcop : Nat.Coprime r l)
    (chi : DirichletCharacter ℂ r) (hne : chi ≠ 1)
    (A T : ℕ) (h2 : Nat.Coprime 2 r) :
    ‖∑ i ∈ Finset.range T,
      (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
          chi ((A + 2 * i : ℕ) : ZMod r)) *
        unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l)‖ ≤
      ((r * l : ℕ) : ℝ) * (l.totient : ℝ) := by
  let g : ZMod (r * l) → ℂ := fun x =>
    (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
        chi ((A : ZMod r) + ((2 : ℕ) : ZMod r) *
          ZMod.castHom (Nat.dvd_mul_right r l) (ZMod r) x)) *
      unitCharacterSum l
        ((A : ZMod l) + ((2 : ℕ) : ZMod l) *
          ZMod.castHom (Nat.dvd_mul_left l r) (ZMod l) x)
  have hfull : (∑ x : ZMod (r * l), g x) = 0 := by
    simpa only [g] using
      even_target_character_ramanujan_complete_period_eq_zero
        r l hcop chi hne A h2
  have hdecomp := residue_interval_decomposition g 0 T
  have hrem :
      (∑ i ∈ Finset.range T, g (i : ZMod (r * l))) =
        ∑ i ∈ Finset.range (T % (r * l)), g (i : ZMod (r * l)) := by
    simpa [hfull] using hdecomp
  have hsource :
      (∑ i ∈ Finset.range T,
        (((ArithmeticFunction.moebius r : ℤ) : ℂ) *
            chi ((A + 2 * i : ℕ) : ZMod r)) *
          unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l)) =
        ∑ i ∈ Finset.range T, g (i : ZMod (r * l)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [g, map_natCast, Nat.cast_add, Nat.cast_mul]
  rw [hsource, hrem]
  calc
    ‖∑ i ∈ Finset.range (T % (r * l)), g (i : ZMod (r * l))‖ ≤
        ∑ i ∈ Finset.range (T % (r * l)), ‖g (i : ZMod (r * l))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (T % (r * l)), (l.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [g, map_natCast, Nat.cast_add, Nat.cast_mul] using
        coupled_first_marginal_term_norm_le r l chi (A + 2 * i)
    _ = ((T % (r * l) : ℕ) : ℝ) * (l.totient : ℝ) := by simp
    _ ≤ ((r * l : ℕ) : ℝ) * (l.totient : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.le_of_lt
          (Nat.mod_lt T (Nat.pos_of_ne_zero (NeZero.ne (r * l))))
      · positivity

end GoldbachCircleMethodCoupledFirstMarginalPairwiseRemainderV18375
