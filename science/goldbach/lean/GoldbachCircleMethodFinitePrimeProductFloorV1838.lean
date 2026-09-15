import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# V1.8.38: finite prime-product floor

This file proves a finite arithmetic precursor only.  In particular, it does not identify the
subset expansion below with any Ramanujan sum or with a module-truncated singular series.
-/

open scoped BigOperators

namespace GoldbachCircleMethodFinitePrimeProductFloorV1838

/-- Primes at most `R` which do not divide `N`. -/
def badPrimes (N R : ℕ) : Finset ℕ :=
  (Finset.range (R + 1)).filter fun p => p.Prime ∧ ¬p ∣ N

/-- The finite local loss weight attached to a prime. -/
noncomputable def primeWeight (p : ℕ) : ℝ :=
  1 / (((p - 1 : ℕ) : ℝ) ^ 2)

/-- Odd-prime indexing used to compare the finite carrier with the Basel series. -/
def oddPrimeIndex (p : ℕ) : ℕ :=
  (p - 1) / 2

/-- For even `N`, every prime in `badPrimes N R` is odd. -/
theorem badPrime_mem_odd {N R p : ℕ} (hEven : Even N)
    (hp : p ∈ badPrimes N R) : Odd p := by
  have hpData : p.Prime ∧ ¬p ∣ N := (Finset.mem_filter.mp hp).2
  apply hpData.1.odd_of_ne_two
  intro hpTwo
  apply hpData.2
  simpa [hpTwo] using hEven.two_dvd

private theorem oddPrimeIndex_injOn {N R : ℕ} (hEven : Even N) :
    Set.InjOn oddPrimeIndex (badPrimes N R : Set ℕ) := by
  intro p hp q hq hIndex
  obtain ⟨a, ha⟩ := badPrime_mem_odd hEven hp
  obtain ⟨b, hb⟩ := badPrime_mem_odd hEven hq
  simp only [oddPrimeIndex] at hIndex
  omega

private theorem primeWeight_eq_quarter_index {N R p : ℕ} (hEven : Even N)
    (hp : p ∈ badPrimes N R) :
    primeWeight p = (1 / 4 : ℝ) * (1 / ((oddPrimeIndex p : ℝ) ^ 2)) := by
  obtain ⟨k, hk⟩ := badPrime_mem_odd hEven hp
  have hSub : p - 1 = 2 * k := by omega
  have hIndex : oddPrimeIndex p = k := by
    simp only [oddPrimeIndex]
    omega
  rw [hIndex]
  simp only [primeWeight, hSub, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem primeWeight_nonneg (p : ℕ) : 0 ≤ primeWeight p := by
  unfold primeWeight
  positivity

/-- Finite bad-prime weights are bounded by one quarter of the kernel-checked Basel sum. -/
theorem badPrimeWeight_sum_le_pi_sq_div_24 {N R : ℕ} (hEven : Even N) :
    ∑ p ∈ badPrimes N R, primeWeight p ≤ Real.pi ^ 2 / 24 := by
  let indexSet := (badPrimes N R).image oddPrimeIndex
  have hIndexSum :
      ∑ n ∈ indexSet, (1 : ℝ) / (n : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
    rw [← hasSum_zeta_two.tsum_eq]
    exact hasSum_zeta_two.summable.sum_le_tsum indexSet (fun n _ => by positivity)
  have hRewrite :
      (∑ p ∈ badPrimes N R, primeWeight p) =
        (1 / 4 : ℝ) * ∑ n ∈ indexSet, (1 : ℝ) / (n : ℝ) ^ 2 := by
    calc
      (∑ p ∈ badPrimes N R, primeWeight p) =
          ∑ p ∈ badPrimes N R,
            (1 / 4 : ℝ) * (1 / ((oddPrimeIndex p : ℝ) ^ 2)) := by
              apply Finset.sum_congr rfl
              intro p hp
              exact primeWeight_eq_quarter_index hEven hp
      _ = (1 / 4 : ℝ) *
          ∑ p ∈ badPrimes N R, (1 : ℝ) / ((oddPrimeIndex p : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
      _ = (1 / 4 : ℝ) *
          ∑ n ∈ indexSet, (1 : ℝ) / (n : ℝ) ^ 2 := by
            unfold indexSet
            rw [Finset.sum_image (oddPrimeIndex_injOn hEven)]
  rw [hRewrite]
  nlinarith

/-- The finite product of local loss factors is bounded by the exponential Basel majorant. -/
theorem badPrimeProduct_le_exp_pi_sq_div_24 {N R : ℕ} (hEven : Even N) :
    ∏ p ∈ badPrimes N R, (1 + primeWeight p) ≤ Real.exp (Real.pi ^ 2 / 24) := by
  calc
    ∏ p ∈ badPrimes N R, (1 + primeWeight p) ≤
        Real.exp (∑ p ∈ badPrimes N R, primeWeight p) := by
          exact Real.prod_one_add_le_exp_sum (badPrimes N R) primeWeight_nonneg
    _ ≤ Real.exp (Real.pi ^ 2 / 24) := by
          exact Real.exp_le_exp.mpr (badPrimeWeight_sum_le_pi_sq_div_24 hEven)

/-- Absolute product weight of a finite prime subset. -/
noncomputable def subsetWeight (s : Finset ℕ) : ℝ :=
  ∏ p ∈ s, primeWeight p

/-- Signed product weight of a finite prime subset. -/
noncomputable def signedSubsetWeight (s : Finset ℕ) : ℝ :=
  ∏ p ∈ s, -primeWeight p

/-- Product-bounded subsets of the exact bad-prime carrier. -/
def boundedBadPrimeSubsets (N R H : ℕ) : Finset (Finset ℕ) :=
  (badPrimes N R).powerset.filter fun s => (∏ p ∈ s, p) ≤ H

/-- The finite signed subset sum used as an arithmetic precursor. -/
noncomputable def boundedSignedPrimeSum (N R H : ℕ) : ℝ :=
  ∑ s ∈ boundedBadPrimeSubsets N R H, signedSubsetWeight s

private theorem subsetWeight_nonneg (s : Finset ℕ) : 0 ≤ subsetWeight s := by
  unfold subsetWeight
  exact Finset.prod_nonneg fun p _ => primeWeight_nonneg p

private theorem abs_signedSubsetWeight (s : Finset ℕ) :
    |signedSubsetWeight s| = subsetWeight s := by
  induction s using Finset.induction_on with
  | empty => simp [signedSubsetWeight, subsetWeight]
  | @insert p s hp ih =>
      simp only [signedSubsetWeight, subsetWeight] at ih ⊢
      rw [Finset.prod_insert hp, Finset.prod_insert hp, abs_mul, ih]
      rw [abs_neg, abs_of_nonneg (primeWeight_nonneg p)]

private theorem empty_mem_boundedBadPrimeSubsets {N R H : ℕ} (hH : 1 ≤ H) :
    ∅ ∈ boundedBadPrimeSubsets N R H := by
  simp [boundedBadPrimeSubsets, hH]

private theorem bounded_erase_subset_powerset_erase {N R H : ℕ} :
    (boundedBadPrimeSubsets N R H).erase ∅ ⊆ (badPrimes N R).powerset.erase ∅ := by
  intro s hs
  have hsBounded := (Finset.mem_erase.mp hs).2
  have hsPower : s ∈ (badPrimes N R).powerset := by
    exact (Finset.mem_filter.mp (by
      simpa only [boundedBadPrimeSubsets] using hsBounded)).1
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hs).1, hsPower⟩

private theorem boundedSignedPrimeSum_ge_two_sub_product {N R H : ℕ} (hH : 1 ≤ H) :
    2 - (∏ p ∈ badPrimes N R, (1 + primeWeight p)) ≤
      boundedSignedPrimeSum N R H := by
  let selected := boundedBadPrimeSubsets N R H
  let allNonempty := (badPrimes N R).powerset.erase ∅
  have hEmptySelected : ∅ ∈ selected := empty_mem_boundedBadPrimeSubsets hH
  have hTermwise :
      -(∑ s ∈ selected.erase ∅, subsetWeight s) ≤
        ∑ s ∈ selected.erase ∅, signedSubsetWeight s := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun s _ => by
      rw [← abs_signedSubsetWeight s]
      exact neg_abs_le (signedSubsetWeight s)
  have hSubset : selected.erase ∅ ⊆ allNonempty := by
    exact bounded_erase_subset_powerset_erase
  have hAbsoluteSum :
      ∑ s ∈ selected.erase ∅, subsetWeight s ≤
        ∑ s ∈ allNonempty, subsetWeight s := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun s _ _ => subsetWeight_nonneg s)
  have hSelectedSplit :
      boundedSignedPrimeSum N R H =
        1 + ∑ s ∈ selected.erase ∅, signedSubsetWeight s := by
    unfold boundedSignedPrimeSum
    change (∑ s ∈ selected, signedSubsetWeight s) = _
    rw [← Finset.sum_erase_add _ _ hEmptySelected]
    simp [signedSubsetWeight]
    ring
  have hAllSplit :
      (∏ p ∈ badPrimes N R, (1 + primeWeight p)) =
        1 + ∑ s ∈ allNonempty, subsetWeight s := by
    rw [Finset.prod_one_add]
    change (∑ s ∈ (badPrimes N R).powerset, subsetWeight s) = _
    calc
      (∑ s ∈ (badPrimes N R).powerset, subsetWeight s) =
          (∑ s ∈ (badPrimes N R).powerset.erase ∅, subsetWeight s) +
            subsetWeight ∅ :=
              (Finset.sum_erase_add (a := (∅ : Finset ℕ)) _ _ (by simp)).symm
      _ = 1 + ∑ s ∈ allNonempty, subsetWeight s := by
            simp [allNonempty, subsetWeight, add_comm]
  rw [hSelectedSplit, hAllSplit]
  linarith

/-- The product-bounded signed subset sum has the finite lower floor.

This theorem makes no identification with a Ramanujan prefix. -/
theorem boundedSignedPrimeSum_ge_two_sub_exp {N R H : ℕ} (hEven : Even N)
    (hH : 1 ≤ H) :
    2 - Real.exp (Real.pi ^ 2 / 24) ≤ boundedSignedPrimeSum N R H := by
  exact le_trans (sub_le_sub_left (badPrimeProduct_le_exp_pi_sq_div_24 hEven) 2)
    (boundedSignedPrimeSum_ge_two_sub_product hH)

end GoldbachCircleMethodFinitePrimeProductFloorV1838
