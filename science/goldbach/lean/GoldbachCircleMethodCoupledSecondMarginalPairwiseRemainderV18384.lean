import GoldbachCircleMethodCoupledSecondMarginalPairwisePeriodV18383
import GoldbachCircleMethodExactPrincipalBoundaryCostV18126

/-!
# Goldbach V1.8.384: pairwise remainder for the coupled second marginal

At coprime levels the actual Ramanujan product is exactly the Ramanujan sum at
the product modulus.  V1.8.383 then cancels every complete consecutive-even
target period, while quotient/remainder decomposition retains only one strict
pairwise-period boundary.

No common LCM, target-weight transport, aggregation over levels, or reserve
absorption is introduced.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCoupledSecondMarginalPairwiseRemainderV18384

open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodActualCompanionPeriodicLiftV18202
open GoldbachCircleMethodCoupledSecondMarginalPairwisePeriodV18383
open GoldbachCircleMethodExactPrincipalBoundaryCostV18126
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodRamanujanCharacterProductV1843

variable (r l : ℕ) [NeZero r] [NeZero l]

local instance productNeZero : NeZero (r * l) :=
  ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l)⟩

/-- Exact multiplicativity of the actual V66 Ramanujan values at a natural
target. -/
theorem unitCharacterSum_mul_of_coprime
    (hcop : Nat.Coprime r l) (N : ℕ) :
    unitCharacterSum r (N : ZMod r) * unitCharacterSum l (N : ZMod l) =
      unitCharacterSum (r * l) (N : ZMod (r * l)) := by
  rw [← finiteFourierRamanujan_eq_unitCharacterSum r N (NeZero.ne r),
    ← finiteFourierRamanujan_eq_unitCharacterSum l N (NeZero.ne l),
    ← finiteFourierRamanujan_eq_unitCharacterSum (r * l) N
      (Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne l))]
  exact (finiteFourierRamanujan_mul_of_coprime
    (NeZero.ne r) (NeZero.ne l) hcop N).symm

/-- The actual coprime Ramanujan product cancels over its pairwise period
along consecutive even targets, provided the product modulus is greater than
two. -/
theorem coupled_second_marginal_complete_period_eq_zero
    (hcop : Nat.Coprime r l) (hprod : 2 < r * l) (A : ℕ) :
    ∑ i ∈ Finset.range (r * l),
      unitCharacterSum r ((A + 2 * i : ℕ) : ZMod r) *
        unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l) = 0 := by
  simp_rw [unitCharacterSum_mul_of_coprime r l hcop]
  exact even_step_unitCharacterSum_complete_period_eq_zero (r * l) hprod A

/-- Pointwise norm of the actual Ramanujan product. -/
theorem coupled_second_marginal_term_norm_le (N : ℕ) :
    ‖unitCharacterSum r (N : ZMod r) *
        unitCharacterSum l (N : ZMod l)‖ ≤
      (r.totient : ℝ) * (l.totient : ℝ) := by
  rw [norm_mul]
  exact mul_le_mul
    (unit_character_norm_le_totient r (N : ZMod r))
    (unit_character_norm_le_totient l (N : ZMod l))
    (norm_nonneg _) (Nat.cast_nonneg _)

/-- Every incomplete consecutive-even-target prefix is bounded by one
pairwise-period boundary.  All complete periods cancel exactly. -/
theorem coupled_second_marginal_prefix_norm_le
    (hcop : Nat.Coprime r l) (hprod : 2 < r * l) (A T : ℕ) :
    ‖∑ i ∈ Finset.range T,
      unitCharacterSum r ((A + 2 * i : ℕ) : ZMod r) *
        unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l)‖ ≤
      ((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ)) := by
  let g : ZMod (r * l) → ℂ := fun x =>
    unitCharacterSum (r * l)
      ((A : ZMod (r * l)) + ((2 : ℕ) : ZMod (r * l)) * x)
  have hfull : (∑ x : ZMod (r * l), g x) = 0 := by
    have hzero := even_step_unitCharacterSum_complete_period_eq_zero
      (r * l) hprod A
    have hzero' :
        (∑ i ∈ Finset.range (r * l), g (i : ZMod (r * l))) = 0 := by
      simpa only [g, Nat.cast_add, Nat.cast_mul] using hzero
    rw [sum_range_residues_complex] at hzero'
    exact hzero'
  have hdecomp := residue_interval_decomposition g 0 T
  have hrem :
      (∑ i ∈ Finset.range T, g (i : ZMod (r * l))) =
        ∑ i ∈ Finset.range (T % (r * l)),
          g (i : ZMod (r * l)) := by
    simpa [hfull] using hdecomp
  have hsource :
      (∑ i ∈ Finset.range T,
        unitCharacterSum r ((A + 2 * i : ℕ) : ZMod r) *
          unitCharacterSum l ((A + 2 * i : ℕ) : ZMod l)) =
        ∑ i ∈ Finset.range T, g (i : ZMod (r * l)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [unitCharacterSum_mul_of_coprime r l hcop]
    simp only [g, Nat.cast_add, Nat.cast_mul]
  rw [hsource, hrem]
  calc
    ‖∑ i ∈ Finset.range (T % (r * l)),
        g (i : ZMod (r * l))‖ ≤
        ∑ i ∈ Finset.range (T % (r * l)),
          ‖g (i : ZMod (r * l))‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (T % (r * l)),
        ((r.totient : ℝ) * (l.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hmul := coupled_second_marginal_term_norm_le r l (A + 2 * i)
      rw [unitCharacterSum_mul_of_coprime r l hcop] at hmul
      simpa only [g, Nat.cast_add, Nat.cast_mul] using hmul
    _ = ((T % (r * l) : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ)) := by simp
    _ ≤ ((r * l : ℕ) : ℝ) *
        ((r.totient : ℝ) * (l.totient : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.le_of_lt
          (Nat.mod_lt T (Nat.pos_of_ne_zero (NeZero.ne (r * l))))
      · positivity

end GoldbachCircleMethodCoupledSecondMarginalPairwiseRemainderV18384
