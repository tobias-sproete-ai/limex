import GoldbachAnalyticOddFrequencyBoundV1871

/-!
# Sharp odd-frequency bound, V1.8.7.2

This module closes only the odd-frequency estimate stated in V1.8.6.  Active
summands are split according to the unique even coordinate, and each side is
injected into the finite positive exponent support of powers of two from
V1.8.7.  Even frequencies and all circle-method estimates remain outside the
scope of this module.
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace GoldbachAnalyticOddFrequencySharpBoundV1872

open GoldbachAnalyticOddFrequencySupportV187
open GoldbachAnalyticOddFrequencyBoundV1871

/-- The unguarded product associated with the uniquely reconstructed right
coordinate. -/
noncomputable def pairWeight (N n : Nat) (k : Int) : Real :=
  ArithmeticFunction.vonMangoldt n *
    ArithmeticFunction.vonMangoldt (frequencyRightIndex N n k)

/-- Indices whose bounded signed-diagonal summand is actually nonzero. -/
noncomputable def activeSupport (N : Nat) (k : Int) : Finset Nat := by
  classical
  exact (Finset.range N.succ).filter fun n =>
    frequencyRightAdmissible N n k ∧ pairWeight N n k ≠ 0

/-- Active indices with an even left coordinate. -/
noncomputable def leftEvenSupport (N : Nat) (k : Int) : Finset Nat := by
  classical
  exact (activeSupport N k).filter fun n => Even n

/-- Active indices with an odd left coordinate; at an odd target their right
coordinate is the unique even coordinate. -/
noncomputable def rightEvenSupport (N : Nat) (k : Int) : Finset Nat := by
  classical
  exact (activeSupport N k).filter fun n => ¬ Even n

theorem mem_activeSupport_iff {N n : Nat} {k : Int} :
    n ∈ activeSupport N k ↔
      n ∈ Finset.range N.succ ∧
        frequencyRightAdmissible N n k ∧ pairWeight N n k ≠ 0 := by
  classical
  simp [activeSupport]

theorem mem_leftEvenSupport_iff {N n : Nat} {k : Int} :
    n ∈ leftEvenSupport N k ↔ n ∈ activeSupport N k ∧ Even n := by
  classical
  simp [leftEvenSupport]

theorem mem_rightEvenSupport_iff {N n : Nat} {k : Int} :
    n ∈ rightEvenSupport N k ↔ n ∈ activeSupport N k ∧ ¬ Even n := by
  classical
  simp [rightEvenSupport]

/-- Removing zero and inadmissible summands does not change the exact
coefficient. -/
theorem A_N_eq_sum_activeSupport (N : Nat) (k : Int) :
    A_N N k = ∑ n ∈ activeSupport N k, pairWeight N n k := by
  classical
  rw [A_N, activeSupport]
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hAdmissible : frequencyRightAdmissible N n k
  · by_cases hWeight : pairWeight N n k = 0
    · rw [if_pos hAdmissible]
      change pairWeight N n k =
        (if frequencyRightAdmissible N n k ∧ pairWeight N n k ≠ 0
          then pairWeight N n k else 0)
      rw [if_neg (by simp [hWeight]), hWeight]
    · rw [if_pos hAdmissible]
      change pairWeight N n k =
        (if frequencyRightAdmissible N n k ∧ pairWeight N n k ≠ 0
          then pairWeight N n k else 0)
      rw [if_pos ⟨hAdmissible, hWeight⟩]
  · simp [hAdmissible, pairWeight]

/-- Exact parity partition of the active coefficient. -/
theorem sum_activeSupport_eq_left_add_right (N : Nat) (k : Int) :
    (∑ n ∈ activeSupport N k, pairWeight N n k) =
      (∑ n ∈ leftEvenSupport N k, pairWeight N n k) +
      ∑ n ∈ rightEvenSupport N k, pairWeight N n k := by
  classical
  rw [leftEvenSupport, rightEvenSupport]
  exact (Finset.sum_filter_add_sum_filter_not
    (activeSupport N k) (fun n => Even n) (pairWeight N · k)).symm

/-- Every active left-even index at a positive odd frequency is represented
by a positive exponent from the finite V1.8.7 support set. -/
theorem leftEvenSupport_has_exponent
    {N k n : Nat} (hN0 : N ≠ 0) (hkN : k ≤ N)
    (hNEven : Even N) (hkOdd : Odd k)
    (hn : n ∈ leftEvenSupport N (k : Int)) :
    ∃ a : Nat, a ∈ twoPowerExponentsUpTo N ∧ n = 2 ^ a := by
  rcases mem_leftEvenSupport_iff.mp hn with ⟨hnActive, hnEven⟩
  rcases mem_activeSupport_iff.mp hnActive with
    ⟨hnRange, hAdmissible, hWeight⟩
  rcases positive_odd_frequency_active_summand_has_two_power_coordinate
      hkN hNEven hkOdd hAdmissible hWeight with hLeft | hRight
  · rcases hLeft with ⟨a, haPos, hnPow, hRightOdd⟩
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
    refine ⟨a, (mem_twoPowerExponentsUpTo_iff hN0).2 ⟨haPos, ?_⟩, hnPow⟩
    simpa [← hnPow] using hnN
  · rcases hRight with ⟨a, haPos, hRightPow, hnOdd⟩
    exact ((Nat.not_even_iff_odd.mpr hnOdd) hnEven).elim

/-- Every active right-even index at a positive odd frequency is represented
by a positive exponent from the same finite V1.8.7 support set. -/
theorem rightEvenSupport_has_exponent
    {N k n : Nat} (hN0 : N ≠ 0) (hkN : k ≤ N)
    (hNEven : Even N) (hkOdd : Odd k)
    (hn : n ∈ rightEvenSupport N (k : Int)) :
    ∃ a : Nat, a ∈ twoPowerExponentsUpTo N ∧
      frequencyRightIndex N n (k : Int) = 2 ^ a := by
  rcases mem_rightEvenSupport_iff.mp hn with ⟨hnActive, hnNotEven⟩
  rcases mem_activeSupport_iff.mp hnActive with
    ⟨hnRange, hAdmissible, hWeight⟩
  rcases positive_odd_frequency_active_summand_has_two_power_coordinate
      hkN hNEven hkOdd hAdmissible hWeight with hLeft | hRight
  · rcases hLeft with ⟨a, haPos, hnPow, hRightOdd⟩
    have hnEven : Even n := by
      rw [hnPow]
      exact (Nat.even_pow' haPos.ne').mpr (by norm_num)
    exact (hnNotEven hnEven).elim
  · rcases hRight with ⟨a, haPos, hRightPow, hnOdd⟩
    refine ⟨a, (mem_twoPowerExponentsUpTo_iff hN0).2 ⟨haPos, ?_⟩,
      hRightPow⟩
    simpa [← hRightPow] using hAdmissible.2

/-- The left-even support has at most `Nat.log 2 N` elements. -/
theorem card_leftEvenSupport_le_natLog
    {N k : Nat} (hN0 : N ≠ 0) (hkN : k ≤ N)
    (hNEven : Even N) (hkOdd : Odd k) :
    (leftEvenSupport N (k : Int)).card ≤ Nat.log 2 N := by
  rw [← card_twoPowerExponentsUpTo N]
  apply Finset.card_le_card_of_injOn (fun n => Nat.log 2 n)
  · intro n hn
    rcases leftEvenSupport_has_exponent hN0 hkN hNEven hkOdd hn with
      ⟨a, haMem, hnPow⟩
    simpa [hnPow, Nat.log_pow Nat.one_lt_two] using haMem
  · intro n₁ hn₁ n₂ hn₂ hLog
    rcases leftEvenSupport_has_exponent hN0 hkN hNEven hkOdd hn₁ with
      ⟨a₁, ha₁Mem, hn₁Pow⟩
    rcases leftEvenSupport_has_exponent hN0 hkN hNEven hkOdd hn₂ with
      ⟨a₂, ha₂Mem, hn₂Pow⟩
    have ha : a₁ = a₂ := by
      simpa [hn₁Pow, hn₂Pow, Nat.log_pow Nat.one_lt_two] using hLog
    calc
      n₁ = 2 ^ a₁ := hn₁Pow
      _ = 2 ^ a₂ := by rw [ha]
      _ = n₂ := hn₂Pow.symm

/-- The right-even support has at most `Nat.log 2 N` elements. -/
theorem card_rightEvenSupport_le_natLog
    {N k : Nat} (hN0 : N ≠ 0) (hkN : k ≤ N)
    (hNEven : Even N) (hkOdd : Odd k) :
    (rightEvenSupport N (k : Int)).card ≤ Nat.log 2 N := by
  rw [← card_twoPowerExponentsUpTo N]
  apply Finset.card_le_card_of_injOn
    (fun n => Nat.log 2 (frequencyRightIndex N n (k : Int)))
  · intro n hn
    rcases rightEvenSupport_has_exponent hN0 hkN hNEven hkOdd hn with
      ⟨a, haMem, hRightPow⟩
    simpa [hRightPow, Nat.log_pow Nat.one_lt_two] using haMem
  · intro n₁ hn₁ n₂ hn₂ hLog
    rcases rightEvenSupport_has_exponent hN0 hkN hNEven hkOdd hn₁ with
      ⟨a₁, ha₁Mem, hRight₁Pow⟩
    rcases rightEvenSupport_has_exponent hN0 hkN hNEven hkOdd hn₂ with
      ⟨a₂, ha₂Mem, hRight₂Pow⟩
    have ha : a₁ = a₂ := by
      simpa [hRight₁Pow, hRight₂Pow, Nat.log_pow Nat.one_lt_two] using hLog
    have hRight : frequencyRightIndex N n₁ (k : Int) =
        frequencyRightIndex N n₂ (k : Int) := by
      calc
        frequencyRightIndex N n₁ (k : Int) = 2 ^ a₁ := hRight₁Pow
        _ = 2 ^ a₂ := by rw [ha]
        _ = frequencyRightIndex N n₂ (k : Int) := hRight₂Pow.symm
    have hAdmissible₁ :=
      (mem_activeSupport_iff.mp (mem_rightEvenSupport_iff.mp hn₁).1).2.1
    have hAdmissible₂ :=
      (mem_activeSupport_iff.mp (mem_rightEvenSupport_iff.mp hn₂).1).2.1
    have hEquation₁ := frequencyRightIndex_equation hAdmissible₁
    have hEquation₂ := frequencyRightIndex_equation hAdmissible₂
    omega

/-- Each active left-even summand is at most `log 2 * log N`. -/
theorem leftEvenSupport_weight_le
    {N n : Nat} {k : Int} (hn : n ∈ leftEvenSupport N k) :
    pairWeight N n k ≤ Real.log 2 * Real.log (N : Real) := by
  rcases mem_leftEvenSupport_iff.mp hn with ⟨hnActive, hnEven⟩
  rcases mem_activeSupport_iff.mp hnActive with
    ⟨hnRange, hAdmissible, hWeight⟩
  have hFactors := mul_ne_zero_iff.mp hWeight
  have hLeftWeight := even_vonMangoldt_support_weight_eq_log_two
    hnEven hFactors.1
  have hRightBound :=
    GoldbachPrimePowerDefectBoundV161.vonMangoldt_le_log_nat_of_le
      hAdmissible.2
  rw [pairWeight, hLeftWeight]
  exact mul_le_mul_of_nonneg_left hRightBound
    (Real.log_natCast_nonneg 2)

/-- Each active right-even summand is at most `log 2 * log N`. -/
theorem rightEvenSupport_weight_le
    {N k n : Nat} (hkN : k ≤ N) (hNEven : Even N) (hkOdd : Odd k)
    (hn : n ∈ rightEvenSupport N (k : Int)) :
    pairWeight N n (k : Int) ≤ Real.log 2 * Real.log (N : Real) := by
  rcases mem_rightEvenSupport_iff.mp hn with ⟨hnActive, hnNotEven⟩
  rcases mem_activeSupport_iff.mp hnActive with
    ⟨hnRange, hAdmissible, hWeight⟩
  have hnOdd : Odd n := Nat.not_even_iff_odd.mp hnNotEven
  have hPair : n + frequencyRightIndex N n (k : Int) = N - k := by
    have hEquation := frequencyRightIndex_equation hAdmissible
    omega
  rcases minus_odd_frequency_pair_has_exactly_one_even_coordinate
      hkN hNEven hkOdd hPair with hLeft | hRight
  · exact ((Nat.not_even_iff_odd.mpr hnOdd) hLeft.1).elim
  · have hFactors := mul_ne_zero_iff.mp hWeight
    have hRightWeight := even_vonMangoldt_support_weight_eq_log_two
      hRight.2 hFactors.2
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
    have hLeftBound :=
      GoldbachPrimePowerDefectBoundV161.vonMangoldt_le_log_nat_of_le hnN
    rw [pairWeight, hRightWeight]
    calc
      ArithmeticFunction.vonMangoldt n * Real.log 2 ≤
          Real.log (N : Real) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hLeftBound (Real.log_natCast_nonneg 2)
      _ = Real.log 2 * Real.log (N : Real) := by ring

/-- Explicit intermediate estimate before converting the exponent count into
a real logarithm. -/
theorem A_N_positive_odd_le_two_natLog_mul_logTwo_mul_log
    {N k : Nat} (hN4 : 4 ≤ N) (hNEven : Even N)
    (hkOdd : Odd k) (_hkPos : 1 ≤ k) (hkN : k ≤ N) :
    A_N N (k : Int) ≤
      2 * (Nat.log 2 N : Real) * Real.log 2 * Real.log (N : Real) := by
  have hN0 : N ≠ 0 := by omega
  have hConstantNonneg :
      0 ≤ Real.log 2 * Real.log (N : Real) :=
    mul_nonneg (Real.log_natCast_nonneg 2) (Real.log_natCast_nonneg N)
  have hLeftCard := card_leftEvenSupport_le_natLog
    hN0 hkN hNEven hkOdd
  have hRightCard := card_rightEvenSupport_le_natLog
    hN0 hkN hNEven hkOdd
  have hLeftSum :
      (∑ n ∈ leftEvenSupport N (k : Int), pairWeight N n (k : Int)) ≤
        (Nat.log 2 N : Real) *
          (Real.log 2 * Real.log (N : Real)) := by
    calc
      (∑ n ∈ leftEvenSupport N (k : Int), pairWeight N n (k : Int)) ≤
          (leftEvenSupport N (k : Int)).card •
            (Real.log 2 * Real.log (N : Real)) :=
        Finset.sum_le_card_nsmul _ _ _ fun n hn =>
          leftEvenSupport_weight_le hn
      _ = ((leftEvenSupport N (k : Int)).card : Real) *
          (Real.log 2 * Real.log (N : Real)) := by simp
      _ ≤ (Nat.log 2 N : Real) *
          (Real.log 2 * Real.log (N : Real)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hLeftCard)
          hConstantNonneg
  have hRightSum :
      (∑ n ∈ rightEvenSupport N (k : Int), pairWeight N n (k : Int)) ≤
        (Nat.log 2 N : Real) *
          (Real.log 2 * Real.log (N : Real)) := by
    calc
      (∑ n ∈ rightEvenSupport N (k : Int), pairWeight N n (k : Int)) ≤
          (rightEvenSupport N (k : Int)).card •
            (Real.log 2 * Real.log (N : Real)) :=
        Finset.sum_le_card_nsmul _ _ _ fun n hn =>
          rightEvenSupport_weight_le hkN hNEven hkOdd hn
      _ = ((rightEvenSupport N (k : Int)).card : Real) *
          (Real.log 2 * Real.log (N : Real)) := by simp
      _ ≤ (Nat.log 2 N : Real) *
          (Real.log 2 * Real.log (N : Real)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hRightCard)
          hConstantNonneg
  rw [A_N_eq_sum_activeSupport,
    sum_activeSupport_eq_left_add_right]
  calc
    (∑ n ∈ leftEvenSupport N (k : Int), pairWeight N n (k : Int)) +
        ∑ n ∈ rightEvenSupport N (k : Int), pairWeight N n (k : Int) ≤
      (Nat.log 2 N : Real) * (Real.log 2 * Real.log (N : Real)) +
        (Nat.log 2 N : Real) * (Real.log 2 * Real.log (N : Real)) :=
      add_le_add hLeftSum hRightSum
    _ = 2 * (Nat.log 2 N : Real) * Real.log 2 *
        Real.log (N : Real) := by ring

/-- The exponent-count/logarithm bridge needed to remove `Nat.log 2 N`. -/
theorem natLog_mul_logTwo_le_log {N : Nat} (hN4 : 4 ≤ N) :
    (Nat.log 2 N : Real) * Real.log 2 ≤ Real.log (N : Real) := by
  have hN0 : N ≠ 0 := by omega
  have hPowNat : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
  have hPowReal : (2 : Real) ^ Nat.log 2 N ≤ (N : Real) := by
    exact_mod_cast hPowNat
  have hLog := Real.log_le_log (by positivity) hPowReal
  simpa [Real.log_pow] using hLog

/-- Sharp V1.8.6 estimate for a positive odd frequency in the declared
range. -/
theorem A_N_positive_odd_le_two_log_sq
    {N k : Nat} (hN4 : 4 ≤ N) (hNEven : Even N)
    (hkOdd : Odd k) (hkPos : 1 ≤ k) (hkN : k ≤ N) :
    A_N N (k : Int) ≤ 2 * Real.log (N : Real) ^ 2 := by
  have hIntermediate :=
    A_N_positive_odd_le_two_natLog_mul_logTwo_mul_log
      hN4 hNEven hkOdd hkPos hkN
  have hBridge := natLog_mul_logTwo_le_log hN4
  have hLogNonneg : 0 ≤ Real.log (N : Real) := Real.log_natCast_nonneg N
  calc
    A_N N (k : Int) ≤
        2 * (Nat.log 2 N : Real) * Real.log 2 * Real.log (N : Real) :=
      hIntermediate
    _ ≤ 2 * Real.log (N : Real) * Real.log (N : Real) := by
      nlinarith
    _ = 2 * Real.log (N : Real) ^ 2 := by ring

/-! ## Symmetric negative odd-frequency estimate -/

theorem negative_leftEvenSupport_has_exponent
    {N k n : Nat} (hN0 : N ≠ 0) (hNEven : Even N) (hkOdd : Odd k)
    (hn : n ∈ leftEvenSupport N (-(k : Int))) :
    ∃ a : Nat, a ∈ twoPowerExponentsUpTo N ∧ n = 2 ^ a := by
  rcases mem_leftEvenSupport_iff.mp hn with ⟨hnActive, hnEven⟩
  rcases mem_activeSupport_iff.mp hnActive with
    ⟨hnRange, hAdmissible, hWeight⟩
  rcases negative_odd_frequency_active_summand_has_two_power_coordinate
      hNEven hkOdd hAdmissible hWeight with hLeft | hRight
  · rcases hLeft with ⟨a, haPos, hnPow, hRightOdd⟩
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
    refine ⟨a, (mem_twoPowerExponentsUpTo_iff hN0).2 ⟨haPos, ?_⟩, hnPow⟩
    simpa [← hnPow] using hnN
  · rcases hRight with ⟨a, haPos, hRightPow, hnOdd⟩
    exact ((Nat.not_even_iff_odd.mpr hnOdd) hnEven).elim

theorem negative_rightEvenSupport_has_exponent
    {N k n : Nat} (hN0 : N ≠ 0) (hNEven : Even N) (hkOdd : Odd k)
    (hn : n ∈ rightEvenSupport N (-(k : Int))) :
    ∃ a : Nat, a ∈ twoPowerExponentsUpTo N ∧
      frequencyRightIndex N n (-(k : Int)) = 2 ^ a := by
  rcases mem_rightEvenSupport_iff.mp hn with ⟨hnActive, hnNotEven⟩
  rcases mem_activeSupport_iff.mp hnActive with
    ⟨hnRange, hAdmissible, hWeight⟩
  rcases negative_odd_frequency_active_summand_has_two_power_coordinate
      hNEven hkOdd hAdmissible hWeight with hLeft | hRight
  · rcases hLeft with ⟨a, haPos, hnPow, hRightOdd⟩
    have hnEven : Even n := by
      rw [hnPow]
      exact (Nat.even_pow' haPos.ne').mpr (by norm_num)
    exact (hnNotEven hnEven).elim
  · rcases hRight with ⟨a, haPos, hRightPow, hnOdd⟩
    refine ⟨a, (mem_twoPowerExponentsUpTo_iff hN0).2 ⟨haPos, ?_⟩,
      hRightPow⟩
    simpa [← hRightPow] using hAdmissible.2

theorem card_negative_leftEvenSupport_le_natLog
    {N k : Nat} (hN0 : N ≠ 0) (hNEven : Even N) (hkOdd : Odd k) :
    (leftEvenSupport N (-(k : Int))).card ≤ Nat.log 2 N := by
  rw [← card_twoPowerExponentsUpTo N]
  apply Finset.card_le_card_of_injOn (fun n => Nat.log 2 n)
  · intro n hn
    rcases negative_leftEvenSupport_has_exponent hN0 hNEven hkOdd hn with
      ⟨a, haMem, hnPow⟩
    simpa [hnPow, Nat.log_pow Nat.one_lt_two] using haMem
  · intro n₁ hn₁ n₂ hn₂ hLog
    rcases negative_leftEvenSupport_has_exponent hN0 hNEven hkOdd hn₁ with
      ⟨a₁, ha₁Mem, hn₁Pow⟩
    rcases negative_leftEvenSupport_has_exponent hN0 hNEven hkOdd hn₂ with
      ⟨a₂, ha₂Mem, hn₂Pow⟩
    have ha : a₁ = a₂ := by
      simpa [hn₁Pow, hn₂Pow, Nat.log_pow Nat.one_lt_two] using hLog
    calc
      n₁ = 2 ^ a₁ := hn₁Pow
      _ = 2 ^ a₂ := by rw [ha]
      _ = n₂ := hn₂Pow.symm

theorem card_negative_rightEvenSupport_le_natLog
    {N k : Nat} (hN0 : N ≠ 0) (hNEven : Even N) (hkOdd : Odd k) :
    (rightEvenSupport N (-(k : Int))).card ≤ Nat.log 2 N := by
  rw [← card_twoPowerExponentsUpTo N]
  apply Finset.card_le_card_of_injOn
    (fun n => Nat.log 2 (frequencyRightIndex N n (-(k : Int))))
  · intro n hn
    rcases negative_rightEvenSupport_has_exponent hN0 hNEven hkOdd hn with
      ⟨a, haMem, hRightPow⟩
    simpa [hRightPow, Nat.log_pow Nat.one_lt_two] using haMem
  · intro n₁ hn₁ n₂ hn₂ hLog
    rcases negative_rightEvenSupport_has_exponent hN0 hNEven hkOdd hn₁ with
      ⟨a₁, ha₁Mem, hRight₁Pow⟩
    rcases negative_rightEvenSupport_has_exponent hN0 hNEven hkOdd hn₂ with
      ⟨a₂, ha₂Mem, hRight₂Pow⟩
    have ha : a₁ = a₂ := by
      simpa [hRight₁Pow, hRight₂Pow, Nat.log_pow Nat.one_lt_two] using hLog
    have hRight : frequencyRightIndex N n₁ (-(k : Int)) =
        frequencyRightIndex N n₂ (-(k : Int)) := by
      calc
        frequencyRightIndex N n₁ (-(k : Int)) = 2 ^ a₁ := hRight₁Pow
        _ = 2 ^ a₂ := by rw [ha]
        _ = frequencyRightIndex N n₂ (-(k : Int)) := hRight₂Pow.symm
    have hAdmissible₁ :=
      (mem_activeSupport_iff.mp (mem_rightEvenSupport_iff.mp hn₁).1).2.1
    have hAdmissible₂ :=
      (mem_activeSupport_iff.mp (mem_rightEvenSupport_iff.mp hn₂).1).2.1
    have hEquation₁ := frequencyRightIndex_equation hAdmissible₁
    have hEquation₂ := frequencyRightIndex_equation hAdmissible₂
    omega

theorem negative_rightEvenSupport_weight_le
    {N k n : Nat} (hNEven : Even N) (hkOdd : Odd k)
    (hn : n ∈ rightEvenSupport N (-(k : Int))) :
    pairWeight N n (-(k : Int)) ≤
      Real.log 2 * Real.log (N : Real) := by
  rcases mem_rightEvenSupport_iff.mp hn with ⟨hnActive, hnNotEven⟩
  rcases mem_activeSupport_iff.mp hnActive with
    ⟨hnRange, hAdmissible, hWeight⟩
  have hnOdd : Odd n := Nat.not_even_iff_odd.mp hnNotEven
  have hPair : n + frequencyRightIndex N n (-(k : Int)) = N + k := by
    have hEquation := frequencyRightIndex_equation hAdmissible
    omega
  rcases plus_odd_frequency_pair_has_exactly_one_even_coordinate
      hNEven hkOdd hPair with hLeft | hRight
  · exact ((Nat.not_even_iff_odd.mpr hnOdd) hLeft.1).elim
  · have hFactors := mul_ne_zero_iff.mp hWeight
    have hRightWeight := even_vonMangoldt_support_weight_eq_log_two
      hRight.2 hFactors.2
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
    have hLeftBound :=
      GoldbachPrimePowerDefectBoundV161.vonMangoldt_le_log_nat_of_le hnN
    rw [pairWeight, hRightWeight]
    calc
      ArithmeticFunction.vonMangoldt n * Real.log 2 ≤
          Real.log (N : Real) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hLeftBound (Real.log_natCast_nonneg 2)
      _ = Real.log 2 * Real.log (N : Real) := by ring

theorem A_N_negative_odd_le_two_natLog_mul_logTwo_mul_log
    {N k : Nat} (hN4 : 4 ≤ N) (hNEven : Even N)
    (hkOdd : Odd k) (_hkPos : 1 ≤ k) (_hkN : k ≤ N) :
    A_N N (-(k : Int)) ≤
      2 * (Nat.log 2 N : Real) * Real.log 2 * Real.log (N : Real) := by
  have hN0 : N ≠ 0 := by omega
  have hConstantNonneg : 0 ≤ Real.log 2 * Real.log (N : Real) :=
    mul_nonneg (Real.log_natCast_nonneg 2) (Real.log_natCast_nonneg N)
  have hLeftCard := card_negative_leftEvenSupport_le_natLog
    hN0 hNEven hkOdd
  have hRightCard := card_negative_rightEvenSupport_le_natLog
    hN0 hNEven hkOdd
  have hLeftSum :
      (∑ n ∈ leftEvenSupport N (-(k : Int)), pairWeight N n (-(k : Int))) ≤
        (Nat.log 2 N : Real) *
          (Real.log 2 * Real.log (N : Real)) := by
    calc
      (∑ n ∈ leftEvenSupport N (-(k : Int)), pairWeight N n (-(k : Int))) ≤
          (leftEvenSupport N (-(k : Int))).card •
            (Real.log 2 * Real.log (N : Real)) :=
        Finset.sum_le_card_nsmul _ _ _ fun n hn =>
          leftEvenSupport_weight_le hn
      _ = ((leftEvenSupport N (-(k : Int))).card : Real) *
          (Real.log 2 * Real.log (N : Real)) := by simp
      _ ≤ (Nat.log 2 N : Real) *
          (Real.log 2 * Real.log (N : Real)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hLeftCard)
          hConstantNonneg
  have hRightSum :
      (∑ n ∈ rightEvenSupport N (-(k : Int)), pairWeight N n (-(k : Int))) ≤
        (Nat.log 2 N : Real) *
          (Real.log 2 * Real.log (N : Real)) := by
    calc
      (∑ n ∈ rightEvenSupport N (-(k : Int)), pairWeight N n (-(k : Int))) ≤
          (rightEvenSupport N (-(k : Int))).card •
            (Real.log 2 * Real.log (N : Real)) :=
        Finset.sum_le_card_nsmul _ _ _ fun n hn =>
          negative_rightEvenSupport_weight_le hNEven hkOdd hn
      _ = ((rightEvenSupport N (-(k : Int))).card : Real) *
          (Real.log 2 * Real.log (N : Real)) := by simp
      _ ≤ (Nat.log 2 N : Real) *
          (Real.log 2 * Real.log (N : Real)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hRightCard)
          hConstantNonneg
  rw [A_N_eq_sum_activeSupport, sum_activeSupport_eq_left_add_right]
  calc
    (∑ n ∈ leftEvenSupport N (-(k : Int)), pairWeight N n (-(k : Int))) +
        ∑ n ∈ rightEvenSupport N (-(k : Int)), pairWeight N n (-(k : Int)) ≤
      (Nat.log 2 N : Real) * (Real.log 2 * Real.log (N : Real)) +
        (Nat.log 2 N : Real) * (Real.log 2 * Real.log (N : Real)) :=
      add_le_add hLeftSum hRightSum
    _ = 2 * (Nat.log 2 N : Real) * Real.log 2 *
        Real.log (N : Real) := by ring

theorem A_N_negative_odd_le_two_log_sq
    {N k : Nat} (hN4 : 4 ≤ N) (hNEven : Even N)
    (hkOdd : Odd k) (hkPos : 1 ≤ k) (hkN : k ≤ N) :
    A_N N (-(k : Int)) ≤ 2 * Real.log (N : Real) ^ 2 := by
  have hIntermediate :=
    A_N_negative_odd_le_two_natLog_mul_logTwo_mul_log
      hN4 hNEven hkOdd hkPos hkN
  have hBridge := natLog_mul_logTwo_le_log hN4
  have hLogNonneg : 0 ≤ Real.log (N : Real) := Real.log_natCast_nonneg N
  calc
    A_N N (-(k : Int)) ≤
        2 * (Nat.log 2 N : Real) * Real.log 2 * Real.log (N : Real) :=
      hIntermediate
    _ ≤ 2 * Real.log (N : Real) * Real.log (N : Real) := by
      nlinarith
    _ = 2 * Real.log (N : Real) ^ 2 := by ring

end GoldbachAnalyticOddFrequencySharpBoundV1872
