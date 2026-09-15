import GoldbachCircleMethodActiveCharacterRadicalErrorV18158

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodActualCompanionRadicalIntegralV18154
namespace GoldbachCircleMethodRadicalArithmeticClassV18159

theorem radicalLocal_pos {R : ℝ} (hR : 1 < R) (ξ : ℝ)
    {p : ℕ} (hp : p.Prime) : 0 < radicalLocal R ξ p := by
  unfold radicalLocal
  apply lt_min zero_lt_one
  apply div_pos _ (Real.log_pos hR)
  apply mul_pos (by positivity)
  exact Real.log_pos (by exact_mod_cast hp.one_lt)

theorem radicalEnvelope_pos {R : ℝ} (hR : 1 < R) (ξ : ℝ) (N : ℕ) :
    0 < radicalEnvelope R ξ N :=
  Finset.prod_pos (fun _ hp => radicalLocal_pos hR ξ (Nat.prime_of_mem_primeFactors hp))

theorem radicalEnvelope_one (R ξ : ℝ) : radicalEnvelope R ξ 1 = 1 := by
  simp [radicalEnvelope]

theorem radicalEnvelope_coprime_mul (R ξ : ℝ) {m n : ℕ} (hcop : m.Coprime n) :
    radicalEnvelope R ξ (m*n) = radicalEnvelope R ξ m * radicalEnvelope R ξ n := by
  unfold radicalEnvelope
  rw [hcop.primeFactors_mul,Finset.prod_union hcop.disjoint_primeFactors]

theorem radicalEnvelope_prime_power (R ξ : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    radicalEnvelope R ξ (p^k) = radicalLocal R ξ p := by
  simp only [radicalEnvelope,Nat.primeFactors_prime_pow hk.ne' hp,Finset.prod_singleton]

noncomputable def divisorRadicalWeight (R ξ : ℝ) (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ)*radicalEnvelope R ξ n

theorem divisorRadicalWeight_nonneg {R : ℝ} (hR : 1 < R) (ξ : ℝ) (n : ℕ) :
    0 ≤ divisorRadicalWeight R ξ n :=
  mul_nonneg (Nat.cast_nonneg _) (radicalEnvelope_nonneg hR ξ n)

theorem divisorRadicalWeight_le_divisors {R : ℝ} (hR : 1 < R) (ξ : ℝ) (n : ℕ) :
    divisorRadicalWeight R ξ n ≤ (n.divisors.card : ℝ) :=
  mul_le_of_le_one_right (Nat.cast_nonneg _) (radicalEnvelope_le_one hR ξ n)

theorem divisorRadicalWeight_coprime_mul (R ξ : ℝ) {m n : ℕ} (hcop : m.Coprime n) :
    divisorRadicalWeight R ξ (m*n) =
      divisorRadicalWeight R ξ m * divisorRadicalWeight R ξ n := by
  unfold divisorRadicalWeight
  rw [hcop.card_divisors_mul,Nat.cast_mul,radicalEnvelope_coprime_mul R ξ hcop]
  ring

theorem card_divisors_prime_power {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p^k).divisors.card = k+1 := by
  rw [Nat.divisors_prime_pow hp]
  rw [Finset.card_map,Finset.card_range]

theorem divisorRadicalWeight_prime_power (R ξ : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    divisorRadicalWeight R ξ (p^k) = (k+1 : ℕ)*radicalLocal R ξ p := by
  unfold divisorRadicalWeight
  rw [card_divisors_prime_power hp,radicalEnvelope_prime_power R ξ hp hk]

theorem successor_le_two_pow (k : ℕ) : k+1 ≤ 2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

theorem divisorRadicalWeight_prime_power_growth {R : ℝ} (hR : 1 < R)
    (ξ : ℝ) {p k : ℕ} (hp : p.Prime) :
    divisorRadicalWeight R ξ (p^k) ≤ (2 : ℝ)^k := by
  calc
    _ ≤ ((p^k).divisors.card : ℝ) := divisorRadicalWeight_le_divisors hR ξ _
    _ = (k+1 : ℕ) := by rw [card_divisors_prime_power hp]
    _ ≤ _ := by exact_mod_cast successor_le_two_pow k

/-- Prime powers are retained: the repaired weight is strictly positive
on p^k for every k>=1, not squarefree-only support. -/
theorem divisorRadicalWeight_prime_power_pos {R : ℝ} (hR : 1 < R)
    (ξ : ℝ) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    0 < divisorRadicalWeight R ξ (p^k) := by
  rw [divisorRadicalWeight_prime_power R ξ hp hk]
  exact mul_pos (by positivity) (radicalLocal_pos hR ξ hp)

end GoldbachCircleMethodRadicalArithmeticClassV18159
