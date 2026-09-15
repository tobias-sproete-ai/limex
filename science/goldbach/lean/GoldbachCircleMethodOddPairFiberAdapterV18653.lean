import GoldbachCircleMethodExplicitJordanParitySplitV18652
import GoldbachAnalyticOddFrequencySharpBoundV1872

/-!
# V1.8.653: bounded odd pair fiber into the sharp odd-frequency coefficient

This append-only module identifies the finite two-dimensional pair fiber in
the box `0 <= a,b <= M` with its one-dimensional left-coordinate fiber.  For
`t <= 2*M` it then embeds that fiber, with no endpoint loss, into the exact
signed-diagonal coefficient `A_N (2*M) (2*M-t)` from V1.8.7.1.

For odd `t`, V1.8.7.2 therefore gives the kernel-checked sharp bound

`truncatedLambdaPairMass M t <= 2 * log(2*M)^2`.

This is only a coefficient bound for an odd pair-sum fiber.  It does not yet
sum the explicit Ramanujan--sinc kernel over odd shifts, it gives no estimate
for the even channel, and it proves no Goldbach statement.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt Classical
open GoldbachCircleMethodActualOneSidedKernelLeakageV18648
open GoldbachCircleMethodExplicitJordanParitySplitV18652
open GoldbachAnalyticOddFrequencySupportV187
open GoldbachAnalyticOddFrequencyBoundV1871
open GoldbachAnalyticOddFrequencySharpBoundV1872

namespace GoldbachCircleMethodOddPairFiberAdapterV18653

/-- The literal pair fiber in the original closed box `0 <= a,b <= M`. -/
private def truncatedPairCarrier (M t : Nat) : Finset (Nat × Nat) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun ab => ab.1 + ab.2 = t)

/-- The exact finite von-Mangoldt pair mass on the sum fiber `a+b=t` inside
the original V1.8.648 box. -/
noncomputable def truncatedLambdaPairMass (M t : Nat) : Real :=
  ∑ ab ∈ truncatedPairCarrier M t, lambdaPairWeight ab

/-- The same truncated fiber, parametrized by its left coordinate. -/
private def truncatedLeftCarrier (M t : Nat) : Finset Nat :=
  (Finset.range M.succ).filter (fun a => a ≤ t ∧ t - a ≤ M)

/-- The full bounded diagonal fiber for a base box `[0,B]`. -/
private def diagonalLeftCarrier (B t : Nat) : Finset Nat :=
  (Finset.range B.succ).filter (fun a => a ≤ t)

/-- Exact finite fiber reduction.  The inverse sends `a` to `(a,t-a)`;
natural subtraction is safe because membership records `a <= t`. -/
theorem truncatedLambdaPairMass_eq_leftFiber (M t : Nat) :
    truncatedLambdaPairMass M t =
      ∑ a ∈ truncatedLeftCarrier M t,
        ArithmeticFunction.vonMangoldt a *
          ArithmeticFunction.vonMangoldt (t - a) := by
  classical
  unfold truncatedLambdaPairMass truncatedPairCarrier truncatedLeftCarrier
  apply Finset.sum_bij (fun ab _hab => ab.1)
  · intro ab hab
    rcases Finset.mem_filter.mp hab with ⟨habProduct, hab⟩
    rcases Finset.mem_product.mp habProduct with ⟨ha, hb⟩
    rw [Finset.mem_filter]
    rw [Finset.mem_range] at ha hb ⊢
    constructor
    · exact ha
    · constructor <;> omega
  · intro ab hab cd hcd hac
    rcases Finset.mem_filter.mp hab with ⟨habProduct, hab⟩
    rcases Finset.mem_filter.mp hcd with ⟨hcdProduct, hcd⟩
    rcases Finset.mem_product.mp habProduct with ⟨ha, hb⟩
    rcases Finset.mem_product.mp hcdProduct with ⟨hc, hd⟩
    apply Prod.ext
    · exact hac
    · omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rcases ha with ⟨haM, hat, htaM⟩
    refine ⟨(a, t - a), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr haM,
          Finset.mem_range.mpr (Nat.lt_succ_iff.mpr htaM)⟩
    · exact Nat.add_sub_of_le hat
  · intro ab hab
    rcases Finset.mem_filter.mp hab with ⟨habProduct, hab⟩
    unfold lambdaPairWeight
    congr 2
    omega

/-- For `t <= B`, the signed coefficient at frequency `B-t` is exactly the
full nonnegative diagonal fiber `a+b=t` in `[0,B]`. -/
theorem A_N_sub_eq_diagonalLeftFiber {B t : Nat} (htB : t ≤ B) :
    A_N B ((B - t : Nat) : Int) =
      ∑ a ∈ diagonalLeftCarrier B t,
        ArithmeticFunction.vonMangoldt a *
          ArithmeticFunction.vonMangoldt (t - a) := by
  classical
  unfold A_N diagonalLeftCarrier
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have haB : a ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  by_cases hat : a ≤ t
  · have hExpr : frequencyRightExpression B a ((B - t : Nat) : Int) =
        (t - a : Nat) := by
      unfold frequencyRightExpression
      omega
    have hRight : frequencyRightIndex B a ((B - t : Nat) : Int) = t - a := by
      unfold frequencyRightIndex
      rw [hExpr]
      simp
    have hAdmissible : frequencyRightAdmissible B a ((B - t : Nat) : Int) := by
      constructor
      · rw [hExpr]
        exact Int.natCast_nonneg _
      · rw [hRight]
        omega
    rw [if_pos hAdmissible, if_pos hat, hRight]
  · have hNotAdmissible :
        ¬ frequencyRightAdmissible B a ((B - t : Nat) : Int) := by
      intro hAdmissible
      have hEquation := frequencyRightIndex_equation hAdmissible
      have hCastSub : ((B - t : Nat) : Int) = (B : Int) - (t : Int) := by
        omega
      rw [hCastSub] at hEquation
      have hRightNonneg : 0 ≤ (frequencyRightIndex B a ((B - t : Nat) : Int) : Int) :=
        Int.natCast_nonneg _
      omega
    rw [if_neg hNotAdmissible, if_neg hat]

/-- The closed `M`-box fiber injects into the full `2*M` diagonal.  No pair
is invented and all omitted terms are nonnegative. -/
theorem truncatedLambdaPairMass_le_A_N_two_mul_sub
    {M t : Nat} (ht : t ≤ 2 * M) :
    truncatedLambdaPairMass M t ≤ A_N (2 * M) (((2 * M) - t : Nat) : Int) := by
  rw [truncatedLambdaPairMass_eq_leftFiber]
  rw [A_N_sub_eq_diagonalLeftFiber ht]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    simp only [truncatedLeftCarrier, diagonalLeftCarrier,
      Finset.mem_filter, Finset.mem_range] at ha ⊢
    rcases ha with ⟨haM, hat, htaM⟩
    exact ⟨by omega, hat⟩
  · intro a ha _haNotTruncated
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      ArithmeticFunction.vonMangoldt_nonneg

/-- Sharp odd-fiber consequence inherited from V1.8.7.2 at the exact base
`2*M`.  Oddness forces the natural frequency `2*M-t` to be positive. -/
theorem truncatedLambdaPairMass_odd_le_two_log_sq
    {M t : Nat} (hM2 : 2 ≤ M) (htOdd : Odd t) (ht : t ≤ 2 * M) :
    truncatedLambdaPairMass M t ≤
      2 * Real.log ((2 * M : Nat) : Real) ^ 2 := by
  have hBase4 : 4 ≤ 2 * M := by omega
  have hBaseEven : Even (2 * M) := by
    exact even_two_mul M
  have hkOdd : Odd (2 * M - t) :=
    even_sub_odd_frequency_is_odd ht hBaseEven htOdd
  have hkPos : 1 ≤ 2 * M - t := by
    rcases hkOdd with ⟨u, hu⟩
    omega
  have hkBase : 2 * M - t ≤ 2 * M := Nat.sub_le _ _
  exact (truncatedLambdaPairMass_le_A_N_two_mul_sub ht).trans
    (A_N_positive_odd_le_two_log_sq
      hBase4 hBaseEven hkOdd hkPos hkBase)

end GoldbachCircleMethodOddPairFiberAdapterV18653
