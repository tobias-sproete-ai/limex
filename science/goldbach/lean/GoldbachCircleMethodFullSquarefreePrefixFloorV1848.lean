import GoldbachCircleMethodFullSquarefreeCoefficientV1847

/-!
# V1.8.48: full squarefree prefix, exact nested sum and fiberwise floor
The numeric sign of kappa and the analytic Major-Arc operator are not claimed here.
-/
open scoped BigOperators
namespace GoldbachCircleMethodFullSquarefreePrefixFloorV1848
open GoldbachCircleMethodFinitePrimeProductFloorV1838
open GoldbachCircleMethodSquarefreeCoefficientBindingV1839
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodFullSquarefreeCoefficientV1847

noncomputable def realFourierCoefficient (N q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    (finiteFourierRamanujan q N hq).re / (Nat.totient q : ℝ) ^ 2

noncomputable def fullSquarefreeFourierPrefix (N H : ℕ) : ℝ :=
  ∑ q ∈ fullSquarefreePrefix H, realFourierCoefficient N q

theorem realFourierCoefficient_pair {a b N R H : ℕ}
    (h : (a,b) ∈ coupledSquarefreePairs N H) (hHR : H ≤ R) :
    realFourierCoefficient N (a*b) =
      (1 / (Nat.totient a : ℝ)) *
        (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (Nat.totient b : ℝ)^2) := by
  have hab0 := (mem_fullSquarefreePrefix.mp (pair_product_mem h)).2.ne_zero
  simp only [realFourierCoefficient, dif_neg hab0]
  exact pair_real_coefficient_split h hHR

/-- Pure finite reindexing with the exact a-dependent cutoff, for arbitrary coefficients. -/
theorem coupled_sum_eq_nested {α : Type*} [AddCommMonoid α]
    (N R H : ℕ) (hHR : H ≤ R) (f : ℕ → ℕ → α) :
    ∑ t ∈ coupledSquarefreePairs N H, f t.1 t.2 =
      ∑ a ∈ dividingSquarefreePrefix N H,
        ∑ b ∈ boundedArithmeticDivisors N R (H/a), f a b := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun t : ℕ × ℕ => (⟨t.1,t.2⟩ : Sigma fun _ : ℕ => ℕ))
    (fun t : Sigma fun _ : ℕ => ℕ => (t.1,t.2))
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact Finset.mem_sigma.mpr ((coupled_pair_iff_existing_fiber hHR).mp ht)
  · intro t ht
    exact (coupled_pair_iff_existing_fiber hHR).mpr (Finset.mem_sigma.mp ht)
  · intro t _
    rfl
  · intro t _
    rfl
  · intro t _
    rfl

theorem fullSquarefreeFourierPrefix_eq_nested (N R H : ℕ) (hHR : H ≤ R) :
    fullSquarefreeFourierPrefix N H =
      ∑ a ∈ dividingSquarefreePrefix N H,
        (1 / (Nat.totient a : ℝ)) *
          ∑ b ∈ boundedArithmeticDivisors N R (H/a),
            (((ArithmeticFunction.moebius b : ℤ) : ℝ) /
              (Nat.totient b : ℝ)^2) := by
  unfold fullSquarefreeFourierPrefix
  rw [fullSquarefreePrefix_sum_split N H]
  calc
    _ = ∑ t ∈ coupledSquarefreePairs N H,
        (1 / (Nat.totient t.1 : ℝ)) *
          (((ArithmeticFunction.moebius t.2 : ℤ) : ℝ) /
            (Nat.totient t.2 : ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact realFourierCoefficient_pair ht hHR
    _ = _ := by
      rw [coupled_sum_eq_nested N R H hHR (fun a b =>
        (1 / (Nat.totient a : ℝ)) *
          (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (Nat.totient b : ℝ)^2))]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]

/-- The established coprime floor is composed separately on every existing fiber H/a. -/
theorem fullSquarefreeFourierPrefix_ge_kappa_times_divisor_mass
    {N R H : ℕ} (hEven : Even N) (hHR : H ≤ R) :
    (2 - Real.exp (Real.pi^2/24)) *
        (∑ a ∈ dividingSquarefreePrefix N H, 1 / (Nat.totient a : ℝ)) ≤
      fullSquarefreeFourierPrefix N H := by
  rw [fullSquarefreeFourierPrefix_eq_nested N R H hHR, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  obtain ⟨haFull, _⟩ := Finset.mem_filter.mp ha
  obtain ⟨haH, haSq⟩ := mem_fullSquarefreePrefix.mp haFull
  have haPos : 0 < a := haSq.ne_zero.bot_lt
  have hcut : 1 ≤ H / a := (Nat.le_div_iff_mul_le haPos).mpr (by simpa using haH)
  have hfloor := boundedSignedPrimeSum_ge_two_sub_exp (N := N) (R := R) hEven hcut
  rw [boundedSignedPrimeSum_eq_moebius_totient_sum] at hfloor
  have hweight : 0 ≤ 1 / (Nat.totient a : ℝ) := by positivity
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfloor hweight

/-- Explicit conventional mu-squared normalization on this squarefree prefix. -/
theorem fullSquarefreePrefix_muSquared_normalization (N H : ℕ) :
    ∑ q ∈ fullSquarefreePrefix H,
      (((ArithmeticFunction.moebius q : ℤ)^2 : ℤ) : ℝ) *
        realFourierCoefficient N q = fullSquarefreeFourierPrefix N H := by
  unfold fullSquarefreeFourierPrefix
  apply Finset.sum_congr rfl
  intro q hq
  rw [ArithmeticFunction.moebius_sq_eq_one_of_squarefree
    (mem_fullSquarefreePrefix.mp hq).2]
  norm_num

end GoldbachCircleMethodFullSquarefreePrefixFloorV1848
