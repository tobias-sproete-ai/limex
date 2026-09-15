import GoldbachCircleMethodCoprimeFourierFloorV1845

/-!
# V1.8.46: full squarefree carrier, with coupled cutoff

Finite arithmetic only. The full squarefree prefix is split uniquely as
q = a*b, where a divides N and b is coprime to N. No independent rectangular
cutoff, Fourier coefficient evaluation or Major-Arc reserve is asserted.
-/

open scoped BigOperators

namespace GoldbachCircleMethodFullSquarefreeCarrierV1846

open GoldbachCircleMethodSquarefreeCoefficientBindingV1839
open GoldbachCircleMethodFinitePrimeProductFloorV1838

def fullSquarefreePrefix (H : ℕ) : Finset ℕ :=
  (Finset.range (H + 1)).filter Squarefree

def coupledSquarefreePairs (N H : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (H + 1)) ×ˢ (Finset.range (H + 1))).filter fun t =>
    Squarefree t.1 ∧ Squarefree t.2 ∧ t.1 ∣ N ∧ Nat.Coprime t.2 N ∧
      t.1 * t.2 ≤ H

theorem mem_fullSquarefreePrefix {q H : ℕ} :
    q ∈ fullSquarefreePrefix H ↔ q ≤ H ∧ Squarefree q := by
  simp [fullSquarefreePrefix]

theorem mem_coupledSquarefreePairs {a b N H : ℕ} :
    (a, b) ∈ coupledSquarefreePairs N H ↔
      Squarefree a ∧ Squarefree b ∧ a ∣ N ∧ Nat.Coprime b N ∧ a * b ≤ H := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨ha, hb, haN, hbN, hab⟩
    have ha_le : a ≤ a * b := Nat.le_mul_of_pos_right a hb.ne_zero.bot_lt
    have hb_le : b ≤ a * b := Nat.le_mul_of_pos_left b ha.ne_zero.bot_lt
    apply Finset.mem_filter.mpr
    refine ⟨?_, ha, hb, haN, hbN, hab⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

theorem canonical_product (q N : ℕ) :
    Nat.gcd q N * (q / Nat.gcd q N) = q :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left q N)

theorem squarefree_complement_coprime {q N : ℕ} (hq : Squarefree q) :
    Nat.Coprime (q / Nat.gcd q N) N := by
  by_cases hN : N = 0
  · subst N
    simp only [Nat.gcd_zero_right, Nat.coprime_zero_right]
    exact Nat.div_self hq.ne_zero.bot_lt
  · exact Nat.coprime_div_gcd_of_squarefree hq hN

theorem canonical_pair_mem {q N H : ℕ} (hq : q ∈ fullSquarefreePrefix H) :
    (Nat.gcd q N, q / Nat.gcd q N) ∈ coupledSquarefreePairs N H := by
  obtain ⟨hqh, hsq⟩ := mem_fullSquarefreePrefix.mp hq
  have hprod : Squarefree (Nat.gcd q N * (q / Nat.gcd q N)) := by
    rw [canonical_product]
    exact hsq
  apply mem_coupledSquarefreePairs.mpr
  exact ⟨hprod.of_mul_left, hprod.of_mul_right, Nat.gcd_dvd_right q N,
    squarefree_complement_coprime hsq, by rwa [canonical_product]⟩

theorem pair_product_mem {a b N H : ℕ}
    (h : (a, b) ∈ coupledSquarefreePairs N H) :
    a * b ∈ fullSquarefreePrefix H := by
  obtain ⟨ha, hb, haN, hbN, hab⟩ := mem_coupledSquarefreePairs.mp h
  exact mem_fullSquarefreePrefix.mpr
    ⟨hab, (Nat.squarefree_mul (hbN.of_dvd_right haN).symm).mpr ⟨ha, hb⟩⟩

theorem pair_gcd_recovery {a b N H : ℕ}
    (h : (a, b) ∈ coupledSquarefreePairs N H) :
    Nat.gcd (a * b) N = a := by
  obtain ⟨_, _, haN, hbN, _⟩ := mem_coupledSquarefreePairs.mp h
  simpa only [Nat.mul_comm] using Nat.gcd_mul_of_coprime_of_dvd hbN haN

theorem pair_div_recovery {a b N H : ℕ}
    (h : (a, b) ∈ coupledSquarefreePairs N H) :
    (a * b) / Nat.gcd (a * b) N = b := by
  rw [pair_gcd_recovery h]
  exact Nat.mul_div_cancel_left b (mem_coupledSquarefreePairs.mp h).1.ne_zero.bot_lt

def fullSquarefreeSplitEquiv (N H : ℕ) :
    {q // q ∈ fullSquarefreePrefix H} ≃
      {t // t ∈ coupledSquarefreePairs N H} where
  toFun q := ⟨(Nat.gcd q.1 N, q.1 / Nat.gcd q.1 N), canonical_pair_mem q.2⟩
  invFun t := ⟨t.1.1 * t.1.2, pair_product_mem t.2⟩
  left_inv q := by
    apply Subtype.ext
    exact canonical_product q.1 N
  right_inv t := by
    apply Subtype.ext
    exact Prod.ext (pair_gcd_recovery t.2) (pair_div_recovery t.2)

theorem fullSquarefreePrefix_sum_split {α : Type*} [AddCommMonoid α]
    (N H : ℕ) (f : ℕ → α) :
    ∑ q ∈ fullSquarefreePrefix H, f q =
      ∑ t ∈ coupledSquarefreePairs N H, f (t.1 * t.2) := by
  exact Finset.sum_nbij'
    (fun q => (Nat.gcd q N, q / Nat.gcd q N)) (fun t => t.1 * t.2)
    (fun _ h => canonical_pair_mem h) (fun _ h => pair_product_mem h)
    (fun q _ => canonical_product q N)
    (fun _ h => Prod.ext (pair_gcd_recovery h) (pair_div_recovery h))
    (fun q _ => by rw [canonical_product])

theorem coupled_cutoff_iff {a b H : ℕ} (ha : 0 < a) :
    a * b ≤ H ↔ b ≤ H / a := by
  rw [Nat.le_div_iff_mul_le ha, Nat.mul_comm]

/-- Link the b-factor to the *existing* V1.8.39 carrier. The H ≤ R
hypothesis is explicit; no change is made to that carrier's definition. -/
theorem complement_mem_existing_carrier {a b N R H : ℕ}
    (h : (a, b) ∈ coupledSquarefreePairs N H) (hHR : H ≤ R) :
    b ∈ boundedArithmeticDivisors N R (H / a) := by
  obtain ⟨ha, hb, _, hbN, hab⟩ := mem_coupledSquarefreePairs.mp h
  have hb_le : b ≤ H := (Nat.le_mul_of_pos_left b ha.ne_zero.bot_lt).trans hab
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
    ((coupled_cutoff_iff ha.ne_zero.bot_lt).mp hab)), hb, hbN, ?_⟩
  intro p hp
  obtain ⟨hpp, hpb, _⟩ := Nat.mem_primeFactors.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
    ((Nat.le_of_dvd hb.ne_zero.bot_lt hpb).trans (hb_le.trans hHR))), hpp, ?_⟩
  exact hpp.coprime_iff_not_dvd.mp (hbN.of_dvd_left hpb)

theorem pair_factors_coprime {a b N H : ℕ}
    (h : (a, b) ∈ coupledSquarefreePairs N H) : Nat.Coprime a b := by
  obtain ⟨_, _, haN, hbN, _⟩ := mem_coupledSquarefreePairs.mp h
  exact (hbN.of_dvd_right haN).symm

def dividingSquarefreePrefix (N H : ℕ) : Finset ℕ :=
  (fullSquarefreePrefix H).filter (fun a => a ∣ N)

/-- Exact fiber membership, not merely an inclusion. Each inner bound is H/a. -/
theorem coupled_pair_iff_existing_fiber {a b N R H : ℕ} (hHR : H ≤ R) :
    (a, b) ∈ coupledSquarefreePairs N H ↔
      a ∈ dividingSquarefreePrefix N H ∧
        b ∈ boundedArithmeticDivisors N R (H / a) := by
  constructor
  · intro h
    obtain ⟨ha, hb, haN, _, hab⟩ := mem_coupledSquarefreePairs.mp h
    refine ⟨?_, complement_mem_existing_carrier h hHR⟩
    exact Finset.mem_filter.mpr
      ⟨mem_fullSquarefreePrefix.mpr
        ⟨(Nat.le_mul_of_pos_right a hb.ne_zero.bot_lt).trans hab, ha⟩, haN⟩
  · rintro ⟨haMem, hbMem⟩
    obtain ⟨haFull, haN⟩ := Finset.mem_filter.mp haMem
    have ha := (mem_fullSquarefreePrefix.mp haFull).2
    obtain ⟨hbBound, hb, hbN, _⟩ := Finset.mem_filter.mp hbMem
    exact mem_coupledSquarefreePairs.mpr
      ⟨ha, hb, haN, hbN, (coupled_cutoff_iff ha.ne_zero.bot_lt).mpr
        (Nat.le_of_lt_succ (Finset.mem_range.mp hbBound))⟩

end GoldbachCircleMethodFullSquarefreeCarrierV1846
