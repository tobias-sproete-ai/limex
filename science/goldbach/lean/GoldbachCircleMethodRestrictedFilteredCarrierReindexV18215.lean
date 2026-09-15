import GoldbachCircleMethodFullSquarefreePrefixFloorV1848

/-!
# V1.8.215: restricted filtered carrier reindexing

This module proves only the exact finite carrier bijection and the coefficient-preserving
reindexing for squarefree levels coprime to a fixed conductor.  The inner V1.8.39 carrier
uses `N * r` solely for its coprimality and prime-factor filter; every Fourier coefficient
continues to be evaluated at the original target `N`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace GoldbachCircleMethodRestrictedFilteredCarrierReindexV18215

open GoldbachCircleMethodSquarefreeCoefficientBindingV1839
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodFullSquarefreePrefixFloorV1848

/-- Squarefree levels up to `H` that are coprime to the fixed conductor `r`. -/
def restrictedSquarefreePrefix (r H : ℕ) : Finset ℕ :=
  (fullSquarefreePrefix H).filter fun l => Nat.Coprime l r

/-- The outer squarefree divisor carrier, additionally coprime to `r`. -/
def restrictedDividingSquarefreePrefix (N r H : ℕ) : Finset ℕ :=
  (dividingSquarefreePrefix N H).filter fun a => Nat.Coprime a r

theorem mem_restrictedSquarefreePrefix {l r H : ℕ} :
    l ∈ restrictedSquarefreePrefix r H ↔
      l ≤ H ∧ Squarefree l ∧ Nat.Coprime l r := by
  rw [restrictedSquarefreePrefix, Finset.mem_filter, mem_fullSquarefreePrefix]
  tauto

theorem mem_restrictedDividingSquarefreePrefix {a N r H : ℕ} :
    a ∈ restrictedDividingSquarefreePrefix N r H ↔
      a ≤ H ∧ Squarefree a ∧ a ∣ N ∧ Nat.Coprime a r := by
  simp [restrictedDividingSquarefreePrefix, dividingSquarefreePrefix,
    mem_fullSquarefreePrefix, and_assoc]

private theorem restricted_complement_mem_existing_carrier
    {a b N r R H : ℕ}
    (hpair : (a, b) ∈ coupledSquarefreePairs N H)
    (hbr : Nat.Coprime b r) (hHR : H ≤ R) :
    b ∈ boundedArithmeticDivisors (N * r) R (H / a) := by
  obtain ⟨ha, hb, _, hbN, hab⟩ := mem_coupledSquarefreePairs.mp hpair
  have hbNr : Nat.Coprime b (N * r) :=
    Nat.coprime_mul_iff_right.mpr ⟨hbN, hbr⟩
  have hb_le : b ≤ H :=
    (Nat.le_mul_of_pos_left b ha.ne_zero.bot_lt).trans hab
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
    ((coupled_cutoff_iff ha.ne_zero.bot_lt).mp hab)), hb, hbNr, ?_⟩
  intro p hp
  obtain ⟨hpp, hpb, _⟩ := Nat.mem_primeFactors.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr
    ((Nat.le_of_dvd hb.ne_zero.bot_lt hpb).trans (hb_le.trans hHR))), hpp, ?_⟩
  exact hpp.coprime_iff_not_dvd.mp (hbNr.of_dvd_left hpb)

private theorem restricted_fiber_pair
    {a b N r R H : ℕ} (_hHR : H ≤ R)
    (ha : a ∈ restrictedDividingSquarefreePrefix N r H)
    (hb : b ∈ boundedArithmeticDivisors (N * r) R (H / a)) :
    (a, b) ∈ coupledSquarefreePairs N H := by
  obtain ⟨haBase, _⟩ := Finset.mem_filter.mp ha
  obtain ⟨haFull, haN⟩ := Finset.mem_filter.mp haBase
  have haSq := (mem_fullSquarefreePrefix.mp haFull).2
  obtain ⟨hbBound, hbSq, hbNr, _⟩ := Finset.mem_filter.mp hb
  have hbN : Nat.Coprime b N :=
    hbNr.of_dvd_right (dvd_mul_right N r)
  exact mem_coupledSquarefreePairs.mpr
    ⟨haSq, hbSq, haN, hbN, (coupled_cutoff_iff haSq.ne_zero.bot_lt).mpr
      (Nat.le_of_lt_succ (Finset.mem_range.mp hbBound))⟩

private theorem restricted_fiber_product_mem
    {a b N r R H : ℕ} (hHR : H ≤ R)
    (ha : a ∈ restrictedDividingSquarefreePrefix N r H)
    (hb : b ∈ boundedArithmeticDivisors (N * r) R (H / a)) :
    a * b ∈ restrictedSquarefreePrefix r H := by
  have hpair := restricted_fiber_pair hHR ha hb
  have hbase := pair_product_mem hpair
  have har := (Finset.mem_filter.mp ha).2
  have hbNr := (Finset.mem_filter.mp hb).2.2.1
  have hbr : Nat.Coprime b r :=
    hbNr.of_dvd_right (dvd_mul_left r N)
  exact Finset.mem_filter.mpr
    ⟨hbase, Nat.coprime_mul_iff_left.mpr ⟨har, hbr⟩⟩

/-- Exact canonical membership equivalence for `a = gcd(l,N)`, `b = l/a`.

The inner carrier is evaluated at `N*r`; no Fourier coefficient occurs in this statement. -/
theorem restricted_mem_iff_canonical_fiber
    {l N r R H : ℕ} (hHR : H ≤ R) :
    l ∈ restrictedSquarefreePrefix r H ↔
      Nat.gcd l N ∈ restrictedDividingSquarefreePrefix N r H ∧
        l / Nat.gcd l N ∈
          boundedArithmeticDivisors (N * r) R (H / Nat.gcd l N) := by
  constructor
  · intro hl
    obtain ⟨hlBase, hlr⟩ := Finset.mem_filter.mp hl
    have hpair := canonical_pair_mem (N := N) hlBase
    have hprodCoprime :
        Nat.Coprime (Nat.gcd l N * (l / Nat.gcd l N)) r := by
      simpa only [canonical_product] using hlr
    have hparts := Nat.coprime_mul_iff_left.mp hprodCoprime
    refine ⟨?_, restricted_complement_mem_existing_carrier hpair hparts.2 hHR⟩
    have haBase : Nat.gcd l N ∈ dividingSquarefreePrefix N H := by
      exact (coupled_pair_iff_existing_fiber hHR).mp hpair |>.1
    exact Finset.mem_filter.mpr ⟨haBase, hparts.1⟩
  · rintro ⟨ha, hb⟩
    have hprod := restricted_fiber_product_mem hHR ha hb
    simpa only [canonical_product] using hprod

/-- The canonical split is a genuine equivalence with the dependent filtered fibers. -/
noncomputable def restrictedFilteredSplitEquiv
    (N r R H : ℕ) (hHR : H ≤ R) :
    {l // l ∈ restrictedSquarefreePrefix r H} ≃
      {t // t ∈ (restrictedDividingSquarefreePrefix N r H).sigma
        (fun a => boundedArithmeticDivisors (N * r) R (H / a))} where
  toFun l :=
    ⟨⟨Nat.gcd l.1 N, l.1 / Nat.gcd l.1 N⟩,
      Finset.mem_sigma.mpr ((restricted_mem_iff_canonical_fiber hHR).mp l.2)⟩
  invFun t :=
    ⟨t.1.1 * t.1.2,
      restricted_fiber_product_mem hHR (Finset.mem_sigma.mp t.2).1
        (Finset.mem_sigma.mp t.2).2⟩
  left_inv l := by
    apply Subtype.ext
    exact canonical_product l.1 N
  right_inv t := by
    apply Subtype.ext
    have hmem := Finset.mem_sigma.mp t.2
    have hpair := restricted_fiber_pair hHR hmem.1 hmem.2
    apply Sigma.ext
    · exact pair_gcd_recovery hpair
    · simp only [pair_gcd_recovery hpair]
      exact heq_of_eq (Nat.mul_div_cancel_left t.1.2
        (mem_coupledSquarefreePairs.mp hpair).1.ne_zero.bot_lt)

/-- Exact finite sum reindexing over the restricted carrier and its dependent fibers. -/
theorem restrictedSquarefreePrefix_sum_reindex
    {α : Type*} [AddCommMonoid α]
    (N r R H : ℕ) (hHR : H ≤ R) (f : ℕ → α) :
    ∑ l ∈ restrictedSquarefreePrefix r H, f l =
      ∑ a ∈ restrictedDividingSquarefreePrefix N r H,
        ∑ b ∈ boundedArithmeticDivisors (N * r) R (H / a), f (a * b) := by
  rw [Finset.sum_sigma']
  exact Finset.sum_nbij'
    (fun l => (⟨Nat.gcd l N, l / Nat.gcd l N⟩ : Sigma fun _ : ℕ => ℕ))
    (fun t => t.1 * t.2)
    (fun _ hl => Finset.mem_sigma.mpr ((restricted_mem_iff_canonical_fiber hHR).mp hl))
    (fun _ ht => restricted_fiber_product_mem hHR (Finset.mem_sigma.mp ht).1
      (Finset.mem_sigma.mp ht).2)
    (fun l _ => canonical_product l N)
    (fun t ht => by
      have hmem := Finset.mem_sigma.mp ht
      have hpair := restricted_fiber_pair hHR hmem.1 hmem.2
      apply Sigma.ext
      · exact pair_gcd_recovery hpair
      · simp only [pair_gcd_recovery hpair]
        exact heq_of_eq (Nat.mul_div_cancel_left t.2
          (mem_coupledSquarefreePairs.mp hpair).1.ne_zero.bot_lt))
    (fun l _ => by rw [canonical_product])

/-- Restricted real Fourier prefix at the original target `N`. -/
noncomputable def restrictedSquarefreeFourierPrefix (N r H : ℕ) : ℝ :=
  ∑ l ∈ restrictedSquarefreePrefix r H, realFourierCoefficient N l

/-- Coefficient-preserving reindexing: `N*r` occurs only in the inner carrier. -/
theorem restrictedSquarefreeFourierPrefix_eq_nested_original_target
    {N r R H : ℕ} (_hEven : Even N) (_hr : 0 < r) (_hH : 0 < H)
    (hHR : H ≤ R) :
    restrictedSquarefreeFourierPrefix N r H =
      ∑ a ∈ restrictedDividingSquarefreePrefix N r H,
        ∑ b ∈ boundedArithmeticDivisors (N * r) R (H / a),
          realFourierCoefficient N (a * b) := by
  unfold restrictedSquarefreeFourierPrefix
  exact restrictedSquarefreePrefix_sum_reindex N r R H hHR
    (realFourierCoefficient N)

/-- The same exact reindexing with V1.8.48's pointwise coefficient split. -/
theorem restrictedSquarefreeFourierPrefix_eq_factorized
    {N r R H : ℕ} (hEven : Even N) (hr : 0 < r) (hH : 0 < H)
    (hHR : H ≤ R) :
    restrictedSquarefreeFourierPrefix N r H =
      ∑ a ∈ restrictedDividingSquarefreePrefix N r H,
        (1 / (Nat.totient a : ℝ)) *
          ∑ b ∈ boundedArithmeticDivisors (N * r) R (H / a),
            (((ArithmeticFunction.moebius b : ℤ) : ℝ) /
              (Nat.totient b : ℝ) ^ 2) := by
  rw [restrictedSquarefreeFourierPrefix_eq_nested_original_target hEven hr hH hHR]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact realFourierCoefficient_pair (restricted_fiber_pair hHR ha hb) hHR

end GoldbachCircleMethodRestrictedFilteredCarrierReindexV18215
