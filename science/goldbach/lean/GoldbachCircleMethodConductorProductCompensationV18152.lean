import GoldbachCircleMethodPositiveEulerLogBoundV18151
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodPositiveEulerBudgetV18150
open GoldbachCircleMethodPositiveEulerLogBoundV18151
namespace GoldbachCircleMethodConductorProductCompensationV18152

noncomputable def conductorLocal (p σ : ℝ) : ℝ :=
  p/(p-1)*(1/p^σ)

noncomputable def conductorWeight (r : ℕ) (σ : ℝ) : ℝ :=
  (1/(r : ℝ)^σ)*((r : ℝ)/(r.totient : ℝ))

theorem totient_ratio_prime_product {r : ℕ} (hr : 0 < r) :
    (r : ℝ)/(r.totient : ℝ) =
      ∏ p ∈ r.primeFactors, (p : ℝ)/((p : ℝ)-1) := by
  have hφ : 0 < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr
  have hd : 0 < ∏ p ∈ r.primeFactors, ((p : ℝ)-1) := by
    apply Finset.prod_pos
    intro p hp
    have hh : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  have hn : (r.totient : ℝ)*(∏ p ∈ r.primeFactors, (p : ℝ)) =
      (r : ℝ)*(∏ p ∈ r.primeFactors, ((p-1 : ℕ) : ℝ)) := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors r)
    simpa only [Nat.cast_mul, Nat.cast_prod] using hh
  have he : (∏ p ∈ r.primeFactors, ((p-1 : ℕ) : ℝ)) =
      ∏ p ∈ r.primeFactors, ((p : ℝ)-1) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le,Nat.cast_one]
  rw [he] at hn
  rw [Finset.prod_div_distrib,div_eq_div_iff hφ.ne' hd.ne']
  simpa only [mul_comm] using hn.symm

theorem reciprocal_conductor_power_le_radical {r : ℕ} (hr : 0 < r)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    1/(r : ℝ)^σ ≤ ∏ p ∈ r.primeFactors, 1/(p : ℝ)^σ := by
  have hrR : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  have hrad : 0 < ∏ p ∈ r.primeFactors, (p : ℝ) :=
    Finset.prod_pos (fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos)
  have hle : (∏ p ∈ r.primeFactors, (p : ℝ)) ≤ (r : ℝ) := by
    have hh := Nat.cast_le (α := ℝ).mpr (Nat.le_of_dvd hr (Nat.prod_primeFactors_dvd r))
    simpa only [Nat.cast_prod] using hh
  have hb := Real.rpow_le_rpow_of_nonpos hrad hle (neg_nonpos.mpr hσ)
  rw [Real.rpow_neg hrR.le,Real.rpow_neg hrad.le] at hb
  calc
    _ ≤ ((∏ p ∈ r.primeFactors, (p : ℝ))^σ)⁻¹ := by simpa only [one_div] using hb
    _ = ∏ p ∈ r.primeFactors, 1/(p : ℝ)^σ := by
      rw [← Real.finsetProd_rpow r.primeFactors (fun p => (p : ℝ))
        (fun p _ => Nat.cast_nonneg p),← Finset.prod_inv_distrib]
      simp only [one_div]

theorem conductorWeight_le_local_product {r : ℕ} (hr : 0 < r)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    conductorWeight r σ ≤ ∏ p ∈ r.primeFactors, conductorLocal (p : ℝ) σ := by
  have hrφ : 0 ≤ (r : ℝ)/(r.totient : ℝ) := by positivity
  have hb := mul_le_mul_of_nonneg_right (reciprocal_conductor_power_le_radical hr hσ) hrφ
  unfold conductorWeight conductorLocal
  calc
    _ ≤ (∏ p ∈ r.primeFactors, 1/(p : ℝ)^σ)*((r : ℝ)/(r.totient : ℝ)) := hb
    _ = ∏ p ∈ r.primeFactors, (p : ℝ)/((p : ℝ)-1)*(1/(p : ℝ)^σ) := by
      rw [totient_ratio_prime_product hr,← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      exact mul_comm _ _

theorem conductorWeight_nonneg (r : ℕ) (σ : ℝ) :
    0 ≤ conductorWeight r σ := by
  unfold conductorWeight
  positivity

theorem conductorLocal_nonneg {p : ℝ} (hp : 1 < p) (σ : ℝ) :
    0 ≤ conductorLocal p σ := by
  unfold conductorLocal
  exact mul_nonneg (div_nonneg (by linarith) (by linarith))
    (div_nonneg zero_le_one (Real.rpow_pos_of_pos (by linarith) _).le)

theorem conductorLocal_le_positiveLocal {p : ℝ} (hp : 1 < p)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    conductorLocal p σ ≤ positiveLocal p σ :=
  positiveLocal_conductor_compensation hp hσ

/-- The finite conductor cost is dominated without r^epsilon or loglog loss. -/
theorem conductorWeight_le_positive_prime_product {r : ℕ} (hr : 0 < r)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    conductorWeight r σ ≤ ∏ p ∈ r.primeFactors, positiveLocal (p : ℝ) σ := by
  exact (conductorWeight_le_local_product hr hσ).trans
    (Finset.prod_le_prod
      (fun p hp => conductorLocal_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) σ)
      (fun p hp => conductorLocal_le_positiveLocal
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) hσ))

end GoldbachCircleMethodConductorProductCompensationV18152
