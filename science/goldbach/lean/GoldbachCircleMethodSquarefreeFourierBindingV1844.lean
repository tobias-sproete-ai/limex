import GoldbachCircleMethodRamanujanCharacterProductV1843

/-!
# V1.8.44: squarefree Fourier coefficient binding

This module transfers the genuine finite Fourier value across finite subsets of the existing
bad-prime carrier. It does not enlarge that carrier to an unrestricted Ramanujan prefix.
-/

open scoped BigOperators

namespace GoldbachCircleMethodSquarefreeFourierBindingV1844

open GoldbachCircleMethodFinitePrimeProductFloorV1838
open GoldbachCircleMethodSquarefreeCoefficientBindingV1839
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodRamanujanCharacterProductV1843

private theorem badPrime_data {N R p : ℕ} (hp : p ∈ badPrimes N R) :
    p.Prime ∧ ¬p ∣ N := (Finset.mem_filter.mp hp).2

/-- On every finite subset of the existing bad-prime carrier, the genuine Fourier sum equals
the Möbius coefficient of the subset product. -/
theorem finiteFourierRamanujan_subsetProduct_eq_moebius {N R : ℕ} {s : Finset ℕ}
    (hs : s ⊆ badPrimes N R) :
    finiteFourierRamanujan (∏ p ∈ s, p) N
        (Finset.prod_ne_zero_iff.mpr fun _p hp => (badPrime_data (hs hp)).1.ne_zero) =
      ((ArithmeticFunction.moebius (∏ p ∈ s, p) : ℤ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simpa using finiteFourierRamanujan_one N
  | @insert p s hp ih =>
      have hpData := badPrime_data (hs (Finset.mem_insert_self p s))
      have hsSub : s ⊆ badPrimes N R := fun a ha => hs (Finset.mem_insert_of_mem ha)
      have hprod0 : (∏ a ∈ s, a) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun a ha => (badPrime_data (hsSub ha)).1.ne_zero
      have hcop : Nat.Coprime p (∏ a ∈ s, a) := by
        rw [Nat.coprime_prod_right_iff]
        intro a ha
        exact (Nat.coprime_primes hpData.1 (badPrime_data (hsSub ha)).1).mpr
          (fun hpa => hp (hpa ▸ ha))
      have hNcop : Nat.Coprime N p :=
        (hpData.1.coprime_iff_not_dvd.mpr hpData.2).symm
      simp only [Finset.prod_insert hp]
      rw [finiteFourierRamanujan_mul_of_coprime hpData.1.ne_zero hprod0 hcop N,
        finiteFourierRamanujan_eq_moebius_of_prime hpData.1 hNcop, ih hsSub]
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
      norm_cast

/-- Exact pointwise Fourier/Möbius identification on the existing bounded arithmetic carrier. -/
theorem finiteFourierRamanujan_eq_moebius_of_mem {N R H d : ℕ}
    (hd : d ∈ boundedArithmeticDivisors N R H) :
    finiteFourierRamanujan d N (Finset.mem_filter.mp hd).2.1.ne_zero =
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  have hdData := (Finset.mem_filter.mp hd).2
  have hsub : d.primeFactors ⊆ badPrimes N R := hdData.2.2
  simpa only [Nat.prod_primeFactors_of_squarefree hdData.1] using
    (finiteFourierRamanujan_subsetProduct_eq_moebius (N := N) hsub)

/-- The real Fourier coefficient sum over the attached existing divisor carrier. -/
noncomputable def boundedFourierCoefficientSum (N R H : ℕ) : ℝ :=
  ∑ d : {d // d ∈ boundedArithmeticDivisors N R H},
    (finiteFourierRamanujan d.1 N
      (Finset.mem_filter.mp d.2).2.1.ne_zero).re /
        (((Nat.totient d.1 : ℕ) : ℝ) ^ 2)

/-- On exactly the V1.8.39 carrier, taking real parts replaces the Fourier coefficient by
the real Möbius coefficient, with no enlargement to all `d ≤ H`. -/
theorem boundedFourierCoefficientSum_eq_moebius_totient (N R H : ℕ) :
    boundedFourierCoefficientSum N R H =
      ∑ d : {d // d ∈ boundedArithmeticDivisors N R H},
        (((ArithmeticFunction.moebius d.1 : ℤ) : ℝ) /
          (((Nat.totient d.1 : ℕ) : ℝ) ^ 2)) := by
  unfold boundedFourierCoefficientSum
  apply Fintype.sum_congr
  intro d
  rw [finiteFourierRamanujan_eq_moebius_of_mem d.2]
  norm_num

/-- The same exact carrier with the classical squarefree `μ(d)^2` normalization. -/
noncomputable def boundedMuSquaredFourierCoefficientSum (N R H : ℕ) : ℝ :=
  ∑ d : {d // d ∈ boundedArithmeticDivisors N R H},
    (((ArithmeticFunction.moebius d.1 : ℤ) ^ 2 : ℤ) : ℝ) *
      (finiteFourierRamanujan d.1 N
        (Finset.mem_filter.mp d.2).2.1.ne_zero).re /
          (((Nat.totient d.1 : ℕ) : ℝ) ^ 2)

/-- On the squarefree V1.8.39 carrier, `μ(d)^2 c_d(N)` reduces exactly to `μ(d)`. -/
theorem boundedMuSquaredFourierCoefficientSum_eq_moebius_totient (N R H : ℕ) :
    boundedMuSquaredFourierCoefficientSum N R H =
      ∑ d : {d // d ∈ boundedArithmeticDivisors N R H},
        (((ArithmeticFunction.moebius d.1 : ℤ) : ℝ) /
          (((Nat.totient d.1 : ℕ) : ℝ) ^ 2)) := by
  unfold boundedMuSquaredFourierCoefficientSum
  apply Fintype.sum_congr
  intro d
  rw [finiteFourierRamanujan_eq_moebius_of_mem d.2,
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (Finset.mem_filter.mp d.2).2.1]
  norm_num

end GoldbachCircleMethodSquarefreeFourierBindingV1844
