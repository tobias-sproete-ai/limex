import GoldbachCircleMethodBadPrimeUniformFrequencyV18169
import Mathlib.Data.Nat.Factorization.Induction

set_option autoImplicit false
open scoped BigOperators Classical ArithmeticFunction.Omega
open GoldbachCircleMethodRadicalArithmeticClassV18159
namespace GoldbachCircleMethodHenriotArithmeticGrowthClassV18170

/-- Global finite growth, not only the prime-power case from V159. -/
theorem weight_le_two_pow_omega {R : ℝ} (hR : 1 < R) (ξ : ℝ) (n : ℕ) :
    divisorRadicalWeight R ξ n ≤ (2 : ℝ)^(Ω n) := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp [divisorRadicalWeight]
  | prime_pow p k hp =>
      rw [ArithmeticFunction.cardFactors_apply_prime_pow hp]
      exact divisorRadicalWeight_prime_power_growth hR ξ hp
  | coprime a b ha hb hab iha ihb =>
      rw [divisorRadicalWeight_coprime_mul R ξ hab,
        ArithmeticFunction.cardFactors_mul (by omega) (by omega), pow_add]
      exact mul_le_mul iha ihb (divisorRadicalWeight_nonneg hR ξ b) (by positivity)

noncomputable def pairWeight (R ξ η : ℝ) (s t : ℕ) : ℝ :=
  divisorRadicalWeight R ξ s*divisorRadicalWeight R η t

theorem pairWeight_nonneg {R : ℝ} (hR : 1 < R) (ξ η : ℝ) (s t : ℕ) :
    0 ≤ pairWeight R ξ η s t :=
  mul_nonneg (divisorRadicalWeight_nonneg hR ξ s) (divisorRadicalWeight_nonneg hR η t)

theorem pairWeight_cross_coprime_mul (R ξ η : ℝ) {a₁ a₂ b₁ b₂ : ℕ}
    (hcop : (a₁*a₂).Coprime (b₁*b₂)) :
    pairWeight R ξ η (a₁*b₁) (a₂*b₂) =
      pairWeight R ξ η a₁ a₂*pairWeight R ξ η b₁ b₂ := by
  have h1 : a₁.Coprime b₁ := Nat.Coprime.of_dvd
    (dvd_mul_right a₁ a₂) (dvd_mul_right b₁ b₂) hcop
  have h2 : a₂.Coprime b₂ := Nat.Coprime.of_dvd
    (dvd_mul_left a₂ a₁) (dvd_mul_left b₂ b₁) hcop
  unfold pairWeight
  rw [divisorRadicalWeight_coprime_mul R ξ h1,
    divisorRadicalWeight_coprime_mul R η h2]
  ring

theorem pairWeight_exponential_bound {R : ℝ} (hR : 1 < R) (ξ η : ℝ)
    {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    pairWeight R ξ η s t ≤ (2 : ℝ)^(Ω (s*t)) := by
  unfold pairWeight
  rw [ArithmeticFunction.cardFactors_mul hs.ne' ht.ne', pow_add]
  exact mul_le_mul (weight_le_two_pow_omega hR ξ s) (weight_le_two_pow_omega hR η t)
    (divisorRadicalWeight_nonneg hR η t) (by positivity)

/-- A fixed divisor bound is the only external input in this subpower step. -/
theorem pairWeight_subpower_bound (B ε : ℝ) (hB : 0 ≤ B)
    (hdivisor : ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ B*(n : ℝ)^ε)
    {R : ℝ} (hR : 1 < R) (ξ η : ℝ) {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    pairWeight R ξ η s t ≤ B^2*((s*t : ℕ) : ℝ)^ε := by
  have hsbound := (divisorRadicalWeight_le_divisors hR ξ s).trans (hdivisor s hs)
  have htbound := (divisorRadicalWeight_le_divisors hR η t).trans (hdivisor t ht)
  have hh := mul_le_mul hsbound htbound (divisorRadicalWeight_nonneg hR η t)
    (mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg s) ε))
  unfold pairWeight
  calc
    _ ≤ (B*(s : ℝ)^ε)*(B*(t : ℝ)^ε) := hh
    _ = _ := by rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg s) (Nat.cast_nonneg t)]; ring

/-- Exact two-coordinate source growth inequality under the cross-product
coprimality condition. B is fixed independently of R and both frequencies. -/
theorem henriot_growth_class_bound (B ε : ℝ) (hB : 1 ≤ B)
    (hdivisor : ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ B*(n : ℝ)^ε)
    {R : ℝ} (hR : 1 < R) (ξ η : ℝ)
    {a₁ a₂ b₁ b₂ : ℕ} (ha1 : 0 < a₁) (ha2 : 0 < a₂)
    (hcop : (a₁*a₂).Coprime (b₁*b₂)) :
    pairWeight R ξ η (a₁*b₁) (a₂*b₂) ≤
      min ((2 : ℝ)^(Ω (a₁*a₂))) (B^2*((a₁*a₂ : ℕ) : ℝ)^ε)*
        pairWeight R ξ η b₁ b₂ := by
  rw [pairWeight_cross_coprime_mul R ξ η hcop]
  apply mul_le_mul_of_nonneg_right _ (pairWeight_nonneg hR ξ η b₁ b₂)
  exact le_min (pairWeight_exponential_bound hR ξ η ha1 ha2)
    (pairWeight_subpower_bound B ε (zero_le_one.trans hB) hdivisor hR ξ η ha1 ha2)

end GoldbachCircleMethodHenriotArithmeticGrowthClassV18170

