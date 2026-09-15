import GoldbachCircleMethodSignedFullPrefixV1850

/-! # V1.8.51: elementary coefficient bounds and a finite remainder adapter.
The operator is not replaced: J is an explicit argument, and its pointwise
error bound remains a premise until instantiated for the actual discrete integral.
-/
open scoped BigOperators
namespace GoldbachCircleMethodFiniteRemainderBudgetV1851
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodFullSquarefreePrefixFloorV1848
open GoldbachCircleMethodSignedFullPrefixV1850

theorem signedMajorCoefficient_abs_le_one (N q : ℕ) :
    |signedMajorCoefficient N q| ≤ 1 := by
  by_cases hq : Squarefree q
  · have hp := canonical_pair_mem (N := N) (mem_fullSquarefreePrefix.mpr ⟨le_rfl, hq⟩)
    obtain ⟨ha, hb, _, _, _⟩ := mem_coupledSquarefreePairs.mp hp
    have hpa : (1 : ℝ) ≤ Nat.totient (Nat.gcd q N) := by
      exact_mod_cast Nat.totient_pos.mpr ha.ne_zero.bot_lt
    have hpb : (1 : ℝ) ≤ Nat.totient (q / Nat.gcd q N) := by
      exact_mod_cast Nat.totient_pos.mpr hb.ne_zero.bot_lt
    have hm : |((ArithmeticFunction.moebius (q / Nat.gcd q N) : ℤ) : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hb
    rw [signedMajorCoefficient_eq_muSquared,
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq]
    norm_num only [Int.cast_one, one_mul]
    have hsplit := realFourierCoefficient_pair hp (R := q) le_rfl
    rw [canonical_product] at hsplit
    rw [hsplit, abs_mul, abs_div, abs_div, abs_one, hm,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Nat.totient (Nat.gcd q N)),
      abs_of_nonneg (sq_nonneg (Nat.totient (q / Nat.gcd q N) : ℝ))]
    have ha1 : (1 : ℝ) / Nat.totient (Nat.gcd q N) ≤ 1 :=
      (div_le_one (by linarith)).mpr hpa
    have hb1 : (1 : ℝ) / (Nat.totient (q / Nat.gcd q N) : ℝ)^2 ≤ 1 :=
      (div_le_one (by positivity)).mpr (by nlinarith)
    exact mul_le_one₀ ha1 (by positivity) hb1
  · rw [signedMajorCoefficient_eq_zero_of_not_squarefree hq, abs_zero]
    norm_num

theorem sum_moduli_le_square (R : ℕ) :
    (∑ q ∈ Finset.Icc 1 R, (q : ℝ)) ≤ (R : ℝ)^2 := by
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 R, (R : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact_mod_cast (Finset.mem_Icc.mp hq).2
    _ = _ := by simp [pow_two]

theorem finite_remainder_bound (N R : ℕ) (J : ℕ → ℝ) (C ε : ℝ)
    (hε : 0 ≤ ε)
    (hJ : ∀ q ∈ Finset.Icc 1 R, |J q - C| ≤ ε * q) :
    |(∑ q ∈ Finset.Icc 1 R, signedMajorCoefficient N q * J q) -
       C * (∑ q ∈ Finset.Icc 1 R, signedMajorCoefficient N q)| ≤ ε * (R : ℝ)^2 := by
  have hid : (∑ q ∈ Finset.Icc 1 R, signedMajorCoefficient N q * J q) -
      C * (∑ q ∈ Finset.Icc 1 R, signedMajorCoefficient N q) =
      ∑ q ∈ Finset.Icc 1 R, signedMajorCoefficient N q * (J q - C) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hid]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 R, |signedMajorCoefficient N q * (J q - C)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 R, ε * (q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul]
      calc
        _ ≤ 1 * |J q - C| := mul_le_mul_of_nonneg_right
          (signedMajorCoefficient_abs_le_one N q) (abs_nonneg _)
        _ ≤ ε * (q : ℝ) := by simpa using hJ q hq
    _ = ε * (∑ q ∈ Finset.Icc 1 R, (q : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_moduli_le_square R) hε

theorem finite_reserve_from_pointwise_remainder {N R : ℕ}
    (hEven : Even N) (hR : 1 ≤ R) (J : ℕ → ℝ) (C ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hJ : ∀ q ∈ Finset.Icc 1 R, |J q - C| ≤ ε * q) :
    C * ((2 : ℝ)/7) - ε * (R : ℝ)^2 ≤
      ∑ q ∈ Finset.Icc 1 R, signedMajorCoefficient N q * J q := by
  have hsum := signed_full_prefix_gt_two_sevenths hEven hR
  have hmain := mul_le_mul_of_nonneg_left hsum.le hC
  have herr := (abs_le.mp (finite_remainder_bound N R J C ε hε hJ)).1
  linarith

end GoldbachCircleMethodFiniteRemainderBudgetV1851
