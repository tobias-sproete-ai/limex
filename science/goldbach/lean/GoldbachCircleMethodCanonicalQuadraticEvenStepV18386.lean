import GoldbachCircleMethodCanonicalTargetQuadraticWeightBindingV18385
import GoldbachCircleMethodCanonicalTargetWeightEvenStepV18369

/-!
# Goldbach V1.8.386: even-step variation of the canonical quadratic weight

The exact quadratic target coefficient is rewritten on each side of the
canonical turning target.  Advancing the even target by two changes at most
two carrier endpoints and shifts every retained complementary power weight by
two.  The resulting single-step variation is bounded by `2 + 4*b`.

This is a source-derived estimate.  No abstract target-variation hypothesis,
pairwise Abel aggregation, reserve absorption, or Goldbach conclusion is used.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalQuadraticEvenStepV18386

open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodCanonicalTargetQuadraticWeightBindingV18385
open GoldbachCircleMethodCanonicalTargetWeightEvenStepV18369
open GoldbachCircleMethodCanonicalTargetWeightPiecewiseGeometryV18368
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

/-- Canonical quadratic-weight normal form on the growing side. -/
theorem canonicalTargetQuadraticWeight_eq_growing_sum
    (B N : ℕ) (b : ℝ) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hTurn : N ≤ blockPairTurningTarget B) :
    canonicalTargetQuadraticWeight B N b =
      ∑ n ∈ Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)),
        powerWeight b (N - n) * powerWeight b n := by
  unfold canonicalTargetQuadraticWeight
  rw [pairFirstCarrier_eq_Icc_growing B N hB hBN hTurn]

/-- Canonical quadratic-weight normal form on the shrinking side. -/
theorem canonicalTargetQuadraticWeight_eq_shrinking_sum
    (B N : ℕ) (b : ℝ) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hTurn : blockPairTurningTarget B ≤ N) :
    canonicalTargetQuadraticWeight B N b =
      ∑ n ∈ Finset.Icc (N - B) B,
        powerWeight b (N - n) * powerWeight b n := by
  unfold canonicalTargetQuadraticWeight
  rw [pairFirstCarrier_eq_Icc_shrinking B N hB hBN hTurn]

/-- A product of two source-block power weights has absolute value at most
one. -/
theorem powerWeight_product_abs_le_one
    (B m n : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hm : m ∈ blockCarrier B) (hn : n ∈ blockCarrier B) :
    |powerWeight b m * powerWeight b n| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul
    (power_weight_abs_le_one B m b hb hm)
    (power_weight_abs_le_one B n b hb hn)
    (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

/-- Moving one factor by two inside the source block changes the product by
at most `4*b/B`. -/
theorem powerWeight_product_shift_two_abs_le
    (B m n : ℕ) (b : ℝ) (hB : 2 ≤ B) (hb : 0 ≤ b)
    (hm : m ∈ blockCarrier B) (hm2 : m + 2 ∈ blockCarrier B)
    (hn : n ∈ blockCarrier B) :
    |powerWeight b (m + 2) * powerWeight b n -
        powerWeight b m * powerWeight b n| ≤
      4 * b / (B : ℝ) := by
  rw [← sub_mul, abs_mul]
  have hvar := power_weight_variation B hB b hb m (m + 2) hm hm2
  have hdist : |(((m + 2 : ℕ) : ℝ) - (m : ℝ))| = 2 := by
    push_cast
    norm_num
  rw [hdist] at hvar
  calc
    |powerWeight b (m + 2) - powerWeight b m| * |powerWeight b n| ≤
        ((2 * b / (B : ℝ)) * 2) * 1 :=
      mul_le_mul hvar (power_weight_abs_le_one B n b hb hn)
        (abs_nonneg _) (by positivity)
    _ = 4 * b / (B : ℝ) := by ring

/-- Exact growing-side even-step decomposition: two new endpoints plus the
shift of every retained complementary factor. -/
theorem canonicalTargetQuadraticWeight_add_two_growing_sub
    (B N : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hNonempty : 2 * (B / 2 + 1) ≤ N)
    (hTurn : N + 2 ≤ blockPairTurningTarget B) :
    canonicalTargetQuadraticWeight B (N + 2) b -
        canonicalTargetQuadraticWeight B N b =
      (∑ n ∈ Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)),
        (powerWeight b (N + 2 - n) - powerWeight b (N - n)) *
          powerWeight b n) +
      powerWeight b (N + 2 - (N - (B / 2 + 1) + 1)) *
          powerWeight b (N - (B / 2 + 1) + 1) +
      powerWeight b (N + 2 - (N - (B / 2 + 1) + 2)) *
          powerWeight b (N - (B / 2 + 1) + 2) := by
  rw [canonicalTargetQuadraticWeight_eq_growing_sum B N b hB hBN (by omega),
    canonicalTargetQuadraticWeight_eq_growing_sum B (N + 2) b hB
      (by omega) hTurn]
  have hsub : N + 2 - (B / 2 + 1) = N - (B / 2 + 1) + 2 := by omega
  rw [hsub, sum_Icc_add_two_top (B / 2 + 1)
    (N - (B / 2 + 1)) (by omega)
    (fun n => powerWeight b (N + 2 - n) * powerWeight b n)]
  have hsum :
      (∑ n ∈ Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)),
          powerWeight b (N + 2 - n) * powerWeight b n) -
        (∑ n ∈ Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)),
          powerWeight b (N - n) * powerWeight b n) =
        ∑ n ∈ Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)),
          (powerWeight b (N + 2 - n) - powerWeight b (N - n)) *
            powerWeight b n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  linear_combination hsum

/-- On the growing side, one even target step costs at most `2 + 4*b`. -/
theorem canonicalTargetQuadraticWeight_add_two_growing_abs_le
    (B N : ℕ) (b : ℝ)
    (hB : 2 ≤ B) (hBN : B ≤ N) (hb : 0 ≤ b)
    (hNonempty : 2 * (B / 2 + 1) ≤ N)
    (hTurn : N + 2 ≤ blockPairTurningTarget B) :
    |canonicalTargetQuadraticWeight B (N + 2) b -
        canonicalTargetQuadraticWeight B N b| ≤ 2 + 4 * b := by
  have hTurnExpanded : N + 2 ≤ B + B / 2 + 1 := by
    simpa only [blockPairTurningTarget] using hTurn
  rw [canonicalTargetQuadraticWeight_add_two_growing_sub
    B N b (by omega) hBN hNonempty hTurn]
  let S : ℝ := ∑ n ∈ Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)),
    (powerWeight b (N + 2 - n) - powerWeight b (N - n)) * powerWeight b n
  let u₁ : ℝ :=
    powerWeight b (N + 2 - (N - (B / 2 + 1) + 1)) *
      powerWeight b (N - (B / 2 + 1) + 1)
  let u₂ : ℝ :=
    powerWeight b (N + 2 - (N - (B / 2 + 1) + 2)) *
      powerWeight b (N - (B / 2 + 1) + 2)
  change |S + u₁ + u₂| ≤ 2 + 4 * b
  have htri : |S + u₁ + u₂| ≤ |S| + |u₁| + |u₂| := by
    calc
      _ ≤ |S + u₁| + |u₂| := abs_add_le _ _
      _ ≤ (|S| + |u₁|) + |u₂| := by
        gcongr
        exact abs_add_le _ _
  have hS : |S| ≤ 4 * b := by
    calc
      |S| ≤ ∑ n ∈ Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)),
          |(powerWeight b (N + 2 - n) - powerWeight b (N - n)) *
            powerWeight b n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)),
          (4 * b / (B : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnI := Finset.mem_Icc.mp hn
        have hnBlock : n ∈ blockCarrier B := by
          simp only [blockCarrier, Finset.mem_Ioc]
          omega
        have hmBlock : N - n ∈ blockCarrier B := by
          simp only [blockCarrier, Finset.mem_Ioc]
          omega
        have hm2Block : N - n + 2 ∈ blockCarrier B := by
          simp only [blockCarrier, Finset.mem_Ioc]
          omega
        have hsub : N + 2 - n = N - n + 2 := by omega
        rw [hsub]
        simpa only [sub_mul] using powerWeight_product_shift_two_abs_le
          B (N - n) n b hB hb hmBlock hm2Block hnBlock
      _ = ((Finset.Icc (B / 2 + 1) (N - (B / 2 + 1))).card : ℝ) *
          (4 * b / (B : ℝ)) := by simp
      _ ≤ (B : ℝ) * (4 * b / (B : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · have hcard : (blockCarrier B).card ≤ B := by
            simp only [blockCarrier, Nat.card_Ioc]
            exact Nat.sub_le B (B / 2)
          exact_mod_cast ((Finset.card_le_card (show
            Finset.Icc (B / 2 + 1) (N - (B / 2 + 1)) ⊆ blockCarrier B by
              intro n hn
              simp only [blockCarrier, Finset.mem_Ioc]
              have hnI := Finset.mem_Icc.mp hn
              omega)).trans hcard)
        · positivity
      _ = 4 * b := by
        have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
        field_simp
  have hu₁ : |u₁| ≤ 1 := by
    unfold u₁
    have hc : N + 2 - (N - (B / 2 + 1) + 1) = B / 2 + 2 := by omega
    rw [hc]
    apply powerWeight_product_abs_le_one B _ _ b hb
    · simp only [blockCarrier, Finset.mem_Ioc]
      omega
    · simp only [blockCarrier, Finset.mem_Ioc]
      omega
  have hu₂ : |u₂| ≤ 1 := by
    unfold u₂
    have hc : N + 2 - (N - (B / 2 + 1) + 2) = B / 2 + 1 := by omega
    rw [hc]
    apply powerWeight_product_abs_le_one B _ _ b hb
    · simp only [blockCarrier, Finset.mem_Ioc]
      omega
    · simp only [blockCarrier, Finset.mem_Ioc]
      omega
  linarith

/-- Exact shrinking-side even-step decomposition: two bottom endpoints leave,
while every retained complementary factor advances by two. -/
theorem canonicalTargetQuadraticWeight_add_two_shrinking_sub
    (B N : ℕ) (b : ℝ)
    (hB : 1 ≤ B) (hBN : B ≤ N)
    (hTurn : blockPairTurningTarget B ≤ N)
    (hUpper : N + 2 ≤ 2 * B) :
    canonicalTargetQuadraticWeight B N b -
        canonicalTargetQuadraticWeight B (N + 2) b =
      powerWeight b (N - (N - B)) * powerWeight b (N - B) +
      powerWeight b (N - (N - B + 1)) * powerWeight b (N - B + 1) +
      (∑ n ∈ Finset.Icc (N - B + 2) B,
        (powerWeight b (N - n) - powerWeight b (N + 2 - n)) *
          powerWeight b n) := by
  rw [canonicalTargetQuadraticWeight_eq_shrinking_sum B N b hB hBN hTurn,
    canonicalTargetQuadraticWeight_eq_shrinking_sum B (N + 2) b hB
      (by omega) (by omega)]
  have hsub : N + 2 - B = N - B + 2 := by omega
  rw [hsub, sum_Icc_eq_two_bottom_add (N - B) B (by omega)
    (fun n => powerWeight b (N - n) * powerWeight b n)]
  have hsum :
      (∑ n ∈ Finset.Icc (N - B + 2) B,
          powerWeight b (N - n) * powerWeight b n) -
        (∑ n ∈ Finset.Icc (N - B + 2) B,
          powerWeight b (N + 2 - n) * powerWeight b n) =
        ∑ n ∈ Finset.Icc (N - B + 2) B,
          (powerWeight b (N - n) - powerWeight b (N + 2 - n)) *
            powerWeight b n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  linear_combination hsum

/-- On the shrinking side, one even target step costs at most `2 + 4*b`. -/
theorem canonicalTargetQuadraticWeight_add_two_shrinking_abs_le
    (B N : ℕ) (b : ℝ)
    (hB : 2 ≤ B) (hBN : B ≤ N) (hb : 0 ≤ b)
    (hTurn : blockPairTurningTarget B ≤ N)
    (hUpper : N + 2 ≤ 2 * B) :
    |canonicalTargetQuadraticWeight B (N + 2) b -
        canonicalTargetQuadraticWeight B N b| ≤ 2 + 4 * b := by
  rw [abs_sub_comm,
    canonicalTargetQuadraticWeight_add_two_shrinking_sub
      B N b (by omega) hBN hTurn hUpper]
  have hTurnExpanded : B + B / 2 + 1 ≤ N := by
    simpa only [blockPairTurningTarget] using hTurn
  let u₁ : ℝ := powerWeight b (N - (N - B)) * powerWeight b (N - B)
  let u₂ : ℝ :=
    powerWeight b (N - (N - B + 1)) * powerWeight b (N - B + 1)
  let S : ℝ := ∑ n ∈ Finset.Icc (N - B + 2) B,
    (powerWeight b (N - n) - powerWeight b (N + 2 - n)) * powerWeight b n
  change |u₁ + u₂ + S| ≤ 2 + 4 * b
  have htri : |u₁ + u₂ + S| ≤ |u₁| + |u₂| + |S| := by
    calc
      _ ≤ |u₁ + u₂| + |S| := abs_add_le _ _
      _ ≤ (|u₁| + |u₂|) + |S| := by
        gcongr
        exact abs_add_le _ _
  have hu₁ : |u₁| ≤ 1 := by
    unfold u₁
    apply powerWeight_product_abs_le_one B _ _ b hb
    · simp only [blockCarrier, Finset.mem_Ioc]
      omega
    · simp only [blockCarrier, Finset.mem_Ioc]
      omega
  have hu₂ : |u₂| ≤ 1 := by
    unfold u₂
    apply powerWeight_product_abs_le_one B _ _ b hb
    · simp only [blockCarrier, Finset.mem_Ioc]
      omega
    · simp only [blockCarrier, Finset.mem_Ioc]
      omega
  have hS : |S| ≤ 4 * b := by
    calc
      |S| ≤ ∑ n ∈ Finset.Icc (N - B + 2) B,
          |(powerWeight b (N - n) - powerWeight b (N + 2 - n)) *
            powerWeight b n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Icc (N - B + 2) B,
          (4 * b / (B : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnI := Finset.mem_Icc.mp hn
        have hnBlock : n ∈ blockCarrier B := by
          simp only [blockCarrier, Finset.mem_Ioc]
          omega
        have hmBlock : N - n ∈ blockCarrier B := by
          simp only [blockCarrier, Finset.mem_Ioc]
          omega
        have hm2Block : N - n + 2 ∈ blockCarrier B := by
          simp only [blockCarrier, Finset.mem_Ioc]
          omega
        have hsub : N + 2 - n = N - n + 2 := by omega
        rw [hsub]
        simpa only [sub_mul, abs_sub_comm] using powerWeight_product_shift_two_abs_le
          B (N - n) n b hB hb hmBlock hm2Block hnBlock
      _ = ((Finset.Icc (N - B + 2) B).card : ℝ) *
          (4 * b / (B : ℝ)) := by simp
      _ ≤ (B : ℝ) * (4 * b / (B : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
        · have hcard : (blockCarrier B).card ≤ B := by
            simp only [blockCarrier, Nat.card_Ioc]
            exact Nat.sub_le B (B / 2)
          exact_mod_cast ((Finset.card_le_card (show
            Finset.Icc (N - B + 2) B ⊆ blockCarrier B by
              intro n hn
              simp only [blockCarrier, Finset.mem_Ioc]
              have hnI := Finset.mem_Icc.mp hn
              omega)).trans hcard)
        · positivity
      _ = 4 * b := by
        have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
        field_simp
  linarith

end GoldbachCircleMethodCanonicalQuadraticEvenStepV18386
