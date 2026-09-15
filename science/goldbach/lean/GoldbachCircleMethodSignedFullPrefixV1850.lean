import GoldbachCircleMethodFullPrefixPositiveFloorV1849

/-! # V1.8.50: negative target frequencies and all-modulus normalization.
The actual additive character is retained; non-squarefree terms vanish by Moebius.
No integral-to-coefficient identity is asserted here.
-/
open scoped BigOperators
namespace GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodFullSquarefreePrefixFloorV1848
open GoldbachCircleMethodFullPrefixPositiveFloorV1849

noncomputable def integerFourierRamanujan (q : ℕ) (n : ℤ) (hq : q ≠ 0) : ℂ := by
  letI : NeZero q := ⟨hq⟩
  classical
  exact ∑ a : ZMod q, if IsUnit a then ZMod.stdAddChar (a * (n : ZMod q)) else 0

theorem integerFourierRamanujan_natCast (q N : ℕ) (hq : q ≠ 0) :
    integerFourierRamanujan q (N : ℤ) hq = finiteFourierRamanujan q N hq := by
  simp [integerFourierRamanujan, finiteFourierRamanujan]

theorem integerFourierRamanujan_neg (q : ℕ) (n : ℤ) (hq : q ≠ 0) :
    integerFourierRamanujan q (-n) hq = integerFourierRamanujan q n hq := by
  let : NeZero q := ⟨hq⟩
  classical
  unfold integerFourierRamanujan
  exact Fintype.sum_bijective (fun a : ZMod q => -a) (Equiv.neg (ZMod q)).bijective
    _ _ (fun a => by simp [mul_neg, neg_mul])

theorem integerFourierRamanujan_neg_natCast (q N : ℕ) (hq : q ≠ 0) :
    integerFourierRamanujan q (-(N : ℤ)) hq = finiteFourierRamanujan q N hq := by
  rw [integerFourierRamanujan_neg, integerFourierRamanujan_natCast]

noncomputable def signedMajorCoefficient (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    (((ArithmeticFunction.moebius q : ℤ)^2 : ℤ) : ℝ) *
      (integerFourierRamanujan q (-(N : ℤ)) hq).re / (Nat.totient q : ℝ)^2

theorem signedMajorCoefficient_eq_muSquared (N q : ℕ) :
    signedMajorCoefficient N q =
      (((ArithmeticFunction.moebius q : ℤ)^2 : ℤ) : ℝ) * realFourierCoefficient N q := by
  by_cases hq : q = 0
  · simp [signedMajorCoefficient, realFourierCoefficient, hq]
  · simp [signedMajorCoefficient, realFourierCoefficient, hq,
      integerFourierRamanujan_neg_natCast, mul_div_assoc]

theorem signedMajorCoefficient_zero (N : ℕ) : signedMajorCoefficient N 0 = 0 := by
  simp [signedMajorCoefficient]

theorem signedMajorCoefficient_eq_zero_of_not_squarefree {N q : ℕ}
    (hq : ¬ Squarefree q) : signedMajorCoefficient N q = 0 := by
  rw [signedMajorCoefficient_eq_muSquared,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]
  norm_num

theorem full_range_eq_squarefree_prefix (N H : ℕ) :
    ∑ q ∈ Finset.range (H+1), signedMajorCoefficient N q =
      fullSquarefreeFourierPrefix N H := by
  unfold fullSquarefreeFourierPrefix fullSquarefreePrefix
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : Squarefree q
  · rw [if_pos hq, signedMajorCoefficient_eq_muSquared,
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq]
    norm_num
  · rw [if_neg hq, signedMajorCoefficient_eq_zero_of_not_squarefree hq]

theorem full_Icc_eq_squarefree_prefix (N H : ℕ) :
    ∑ q ∈ Finset.Icc 1 H, signedMajorCoefficient N q =
      fullSquarefreeFourierPrefix N H := by
  rw [← full_range_eq_squarefree_prefix]
  have hset : Finset.range (H+1) = insert 0 (Finset.Icc 1 H) := by
    ext q
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp), signedMajorCoefficient_zero, zero_add]

theorem signed_full_prefix_ge_kappa {N H : ℕ} (hEven : Even N) (hH : 1 ≤ H) :
    2 - Real.exp (Real.pi^2/24) ≤ ∑ q ∈ Finset.Icc 1 H, signedMajorCoefficient N q := by
  rw [full_Icc_eq_squarefree_prefix]
  exact fullSquarefreeFourierPrefix_ge_kappa hEven hH

theorem signed_full_prefix_gt_two_sevenths {N H : ℕ}
    (hEven : Even N) (hH : 1 ≤ H) :
    (2 : ℝ)/7 < ∑ q ∈ Finset.Icc 1 H, signedMajorCoefficient N q := by
  rw [full_Icc_eq_squarefree_prefix]
  exact fullSquarefreeFourierPrefix_gt_two_sevenths hEven hH

end GoldbachCircleMethodSignedFullPrefixV1850
