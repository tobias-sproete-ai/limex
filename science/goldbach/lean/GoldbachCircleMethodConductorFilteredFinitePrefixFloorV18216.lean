import GoldbachCircleMethodRestrictedFilteredCarrierReindexV18215
import GoldbachCircleMethodFullPrefixPositiveFloorV1849

/-!
# V1.8.216: conductor-filtered finite prefix floor

This module derives only a finite lower floor for the conductor-filtered squarefree
Fourier prefix.  The V1.8.215 factorization is specialized transparently to `R := H`;
the inner carrier therefore remains the literal
`boundedArithmeticDivisors (N * r) H (H / a)` carrier.

There is no Abel transfer, weighted-operator estimate, reserve, exceptional-set bound,
or Goldbach conclusion here.
-/

set_option autoImplicit false

open scoped BigOperators

namespace GoldbachCircleMethodConductorFilteredFinitePrefixFloorV18216

open GoldbachCircleMethodFinitePrimeProductFloorV1838
open GoldbachCircleMethodSquarefreeCoefficientBindingV1839
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodFullPrefixPositiveFloorV1849
open GoldbachCircleMethodRestrictedFilteredCarrierReindexV18215

theorem even_mul_right {N r : ℕ} (hEven : Even N) : Even (N * r) := by
  obtain ⟨k, hk⟩ := hEven
  refine ⟨k * r, ?_⟩
  calc
    N * r = (k + k) * r := by rw [hk]
    _ = k * r + k * r := by rw [add_mul]

theorem one_mem_restrictedDividingSquarefreePrefix
    (N r : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    1 ∈ restrictedDividingSquarefreePrefix N r H := by
  rw [mem_restrictedDividingSquarefreePrefix]
  exact ⟨hH, squarefree_one, one_dvd N, Nat.coprime_one_left r⟩

theorem restricted_divisor_mass_ge_one
    (N r : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    (1 : ℝ) ≤
      ∑ a ∈ restrictedDividingSquarefreePrefix N r H,
        1 / (Nat.totient a : ℝ) := by
  have h := Finset.single_le_sum
    (f := fun a : ℕ => (1 : ℝ) / (Nat.totient a : ℝ))
    (fun a _ => by positivity)
    (one_mem_restrictedDividingSquarefreePrefix N r hH)
  simpa using h

theorem restrictedSquarefreeFourierPrefix_ge_kappa_times_divisor_mass
    {N r H : ℕ} (hEven : Even N) (hr : 0 < r) (hH : 1 ≤ H) :
    (2 - Real.exp (Real.pi ^ 2 / 24)) *
        (∑ a ∈ restrictedDividingSquarefreePrefix N r H,
          1 / (Nat.totient a : ℝ)) ≤
      restrictedSquarefreeFourierPrefix N r H := by
  have hHpos : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
  have hEvenNr : Even (N * r) := even_mul_right hEven
  rw [restrictedSquarefreeFourierPrefix_eq_factorized
    hEven hr hHpos (R := H) le_rfl, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have haData := (mem_restrictedDividingSquarefreePrefix.mp ha)
  have haPos : 0 < a := haData.2.1.ne_zero.bot_lt
  have hcut : 1 ≤ H / a := (Nat.le_div_iff_mul_le haPos).mpr (by simpa using haData.1)
  have hfloor := boundedSignedPrimeSum_ge_two_sub_exp
    (N := N * r) (R := H) hEvenNr hcut
  rw [boundedSignedPrimeSum_eq_moebius_totient_sum] at hfloor
  have hweight : 0 ≤ (1 / (Nat.totient a : ℝ)) := by positivity
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfloor hweight

theorem restrictedSquarefreeFourierPrefix_ge_kappa
    {N r H : ℕ} (hEven : Even N) (hr : 0 < r) (hH : 1 ≤ H) :
    2 - Real.exp (Real.pi ^ 2 / 24) ≤
      restrictedSquarefreeFourierPrefix N r H := by
  have hmass := restricted_divisor_mass_ge_one N r hH
  have hfloor := restrictedSquarefreeFourierPrefix_ge_kappa_times_divisor_mass
    hEven hr hH
  have hmul := mul_le_mul_of_nonneg_left hmass (le_of_lt kappa_pos)
  simpa only [mul_one] using hmul.trans hfloor

theorem restrictedSquarefreeFourierPrefix_gt_two_sevenths
    {N r H : ℕ} (hEven : Even N) (hr : 0 < r) (hH : 1 ≤ H) :
    (2 : ℝ) / 7 < restrictedSquarefreeFourierPrefix N r H :=
  kappa_gt_two_sevenths.trans_le
    (restrictedSquarefreeFourierPrefix_ge_kappa hEven hr hH)

end GoldbachCircleMethodConductorFilteredFinitePrefixFloorV18216
