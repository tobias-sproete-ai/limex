import GoldbachCircleMethodTotientRatioPrimeFactorizationV18561

/-!
# Goldbach V1.8.562: local prime majorant for the totient fourth moment

Each local fourth-power factor `(p/(p-1))^4` is bounded by `1 + 30/p` for
every prime `p`.  The constant 30 is sharp for this elementary comparison at
`p=2`.  Multiplication over the finite prime support yields a positive
divisor-expandable majorant for the remaining collision ratio.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodTotientRatioLocalPrimeMajorantV18562

open GoldbachCircleMethodCollisionTotientRatioEnvelopeV18556
open GoldbachCircleMethodTotientRatioPrimeFactorizationV18561

/-- Elementary local comparison, with equality at `p=2`. -/
theorem local_totient_fourth_factor_le_one_add_thirty_div
    (p : ℕ) (hp : 2 ≤ p) :
    ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 4 ≤
      1 + (30 : ℝ) / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hpredNat : 0 < p - 1 := by omega
  have hpred : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hpredNat
  have hcastPred : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hpred 4)).2
  have hone : 1 + (30 : ℝ) / (p : ℝ) =
      ((p : ℝ) + 30) / (p : ℝ) := by
    field_simp
  rw [hone]
  have hreassoc :
      (((p : ℝ) + 30) / (p : ℝ)) * ((p - 1 : ℕ) : ℝ) ^ 4 =
        (((p : ℝ) + 30) * ((p - 1 : ℕ) : ℝ) ^ 4) / (p : ℝ) := by
    ring
  rw [hreassoc]
  apply (le_div_iff₀ hp0).2
  rw [hcastPred]
  have hbase : 0 ≤ (p : ℝ) - 1 := by linarith
  have hsq : 0 ≤ ((p : ℝ) - 1) ^ 2 := pow_nonneg hbase _
  have hcube : 0 ≤ ((p : ℝ) - 1) ^ 3 := pow_nonneg hbase _
  have hpoly : 0 ≤
      26 * ((p : ℝ) - 1) ^ 3 +
        16 * ((p : ℝ) - 1) ^ 2 +
        6 * ((p : ℝ) - 1) + 1 := by
    nlinarith
  have hfactor_nonneg :
      0 ≤ ((p : ℝ) - 2) *
        (26 * ((p : ℝ) - 1) ^ 3 +
          16 * ((p : ℝ) - 1) ^ 2 +
          6 * ((p : ℝ) - 1) + 1) := by
    exact mul_nonneg (by linarith) hpoly
  have hfactor_identity :
      ((p : ℝ) + 30) * ((p : ℝ) - 1) ^ 4 - (p : ℝ) ^ 5 =
        ((p : ℝ) - 2) *
          (26 * ((p : ℝ) - 1) ^ 3 +
            16 * ((p : ℝ) - 1) ^ 2 +
            6 * ((p : ℝ) - 1) + 1) := by ring
  have hmain :
      (p : ℝ) ^ 5 ≤ ((p : ℝ) + 30) * ((p : ℝ) - 1) ^ 4 := by
    nlinarith [hfactor_nonneg, hfactor_identity]
  calc
    (p : ℝ) ^ 4 * (p : ℝ) = (p : ℝ) ^ 5 := by ring
    _ ≤ ((p : ℝ) + 30) * ((p : ℝ) - 1) ^ 4 := hmain

/-- Finite prime-support majorant for the remaining fourth-power ratio. -/
theorem levelTotientRatio_pow_four_le_primeMajorantProduct
    (n : ℕ) (hn : n ≠ 0) :
    levelTotientRatio n ^ 4 ≤
      ∏ p ∈ n.primeFactors, (1 + (30 : ℝ) / (p : ℝ)) := by
  rw [levelTotientRatio_pow_four_eq_primeFactorProduct n hn]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    exact local_totient_fourth_factor_le_one_add_thirty_div p
      (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))

end GoldbachCircleMethodTotientRatioLocalPrimeMajorantV18562
