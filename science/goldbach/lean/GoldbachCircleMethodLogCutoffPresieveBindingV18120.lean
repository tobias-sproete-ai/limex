import GoldbachCircleMethodFiniteWindowConvolutionV18119
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119

namespace GoldbachCircleMethodLogCutoffPresieveBindingV18120

noncomputable def logWeight (R : ℝ) (G : ℝ → ℝ) (q : ℕ) : ℂ :=
  (G (Real.log (q : ℝ) / Real.log R) : ℂ)

/-- Exact support cutoff for positive indices; q=0 is deliberately excluded. -/
theorem log_cutoff_iff (R : ℝ) (hR : 1 < R) (q : ℕ) (hq : 0 < q) :
    Real.log (q : ℝ) / Real.log R ≤ 2 ↔ q ≤ ⌊R^2⌋₊ := by
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  rw [div_le_iff₀ hlog, Nat.le_floor_iff (sq_nonneg R)]
  have hp : Real.log (R^2) = 2 * Real.log R := by
    rw [Real.log_pow]
    norm_num
  rw [← hp]
  exact Real.log_le_log_iff (Nat.cast_pos.mpr hq) (pow_pos hRpos 2)

/-- Compact support beyond 2 gives exact zero, not merely small tail mass. -/
theorem logWeight_zero_above_cutoff (R : ℝ) (hR : 1 < R)
    (G : ℝ → ℝ) (hG : ∀ x : ℝ, 2 < x → G x = 0)
    (q : ℕ) (hq : 0 < q) (hcut : ⌊R^2⌋₊ < q) :
    logWeight R G q = 0 := by
  have hx : 2 < Real.log (q : ℝ) / Real.log R :=
    lt_of_not_ge (fun h => (Nat.not_le_of_gt hcut) ((log_cutoff_iff R hR q hq).mp h))
  simp only [logWeight, hG _ hx, Complex.ofReal_zero]

/-- Enlarging the positive finite ambient index does not alter the weighted sum. -/
theorem logWeight_sum_stable (R : ℝ) (hR : 1 < R)
    (G : ℝ → ℝ) (hG : ∀ x : ℝ, 2 < x → G x = 0)
    (T : ℕ) (hT : ⌊R^2⌋₊ ≤ T) (F : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 T, logWeight R G q * F q) =
      ∑ q ∈ Finset.Icc 1 ⌊R^2⌋₊, logWeight R G q * F q := by
  symm
  apply Finset.sum_subset
  · intro q hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1,
      le_trans (Finset.mem_Icc.mp hq).2 hT⟩
  · intro q hq hnot
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hcut : ⌊R^2⌋₊ < q := by
      by_contra hc
      exact hnot (Finset.mem_Icc.mpr ⟨hqpos, Nat.le_of_not_gt hc⟩)
    rw [logWeight_zero_above_cutoff R hR G hG q hqpos hcut, zero_mul]

def blockCarrier (B : ℕ) : Finset ℕ := Finset.Ioc (B/2) B

/-- Integer carrier exactly matches the half-open block (B/2,B]. -/
theorem mem_blockCarrier (B n : ℕ) :
    n ∈ blockCarrier B ↔ B < 2*n ∧ n ≤ B := by
  simp only [blockCarrier, Finset.mem_Ioc]
  omega

def Rough (Q n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ Q → ¬p ∣ n

/-- No small prime divisor implies the required unit condition for every q<=Q. -/
theorem rough_coprime (Q n q : ℕ) (hn : Rough Q n) (hq : 0 < q) (hQ : q ≤ Q) :
    Nat.Coprime n q := by
  by_contra h
  obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact hn p hp (le_trans (Nat.le_of_dvd hq hpq) hQ) hpn

noncomputable def blockInput (B n : ℕ) : ℂ :=
  if n ∈ blockCarrier B then (ArithmeticFunction.vonMangoldt n : ℂ) else 0

noncomputable def presievedInput (Q B n : ℕ) : ℂ :=
  if Rough Q n then blockInput B n else 0

noncomputable def removedInput (Q B n : ℕ) : ℂ :=
  if Rough Q n then 0 else blockInput B n

theorem block_input_decomposition (Q B n : ℕ) :
    blockInput B n = presievedInput Q B n + removedInput Q B n := by
  simp only [presievedInput, removedInput]
  split_ifs <;> ring

theorem presieved_input_unit_support (Q B n : ℕ) (hf : presievedInput Q B n ≠ 0)
    (q : PositiveLevel Q) : IsUnit (n : ZMod q.val) := by
  have hr : Rough Q n := by
    by_contra h
    exact hf (by simp only [presievedInput, h, if_false])
  exact (ZMod.isUnit_iff_coprime n q.val).mpr
    (rough_coprime Q n q.val hr (Finset.mem_Icc.mp q.property).1
      (Finset.mem_Icc.mp q.property).2)

/-- The removed nonzero mass really consists of powers of primes <=Q. -/
theorem removed_input_prime_power_support (Q B n : ℕ)
    (hg : removedInput Q B n ≠ 0) :
    n ∈ blockCarrier B ∧
      ∃ p k : ℕ, p.Prime ∧ p ≤ Q ∧ 0 < k ∧ p^k = n := by
  have hr : ¬Rough Q n := by
    intro h
    exact hg (by simp only [removedInput, h, if_true])
  have ha : blockInput B n ≠ 0 := by
    simpa only [removedInput, hr, if_false] using hg
  have hn : n ∈ blockCarrier B := by
    by_contra h
    exact ha (by simp only [blockInput, h, if_false])
  have hlambda : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro h
    exact ha (by simp only [blockInput, hn, if_true, h, Complex.ofReal_zero])
  obtain ⟨p,k,hp,hk,hpow⟩ := (isPrimePow_nat_iff n).mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hlambda)
  have hbad : ∃ s : ℕ, s.Prime ∧ s ≤ Q ∧ s ∣ n := by
    simpa only [Rough, not_forall, exists_prop, not_not] using hr
  obtain ⟨s, hs, hsQ, hsn⟩ := hbad
  have hsp : s ∣ p := hs.dvd_of_dvd_pow (hpow ▸ hsn)
  have hspeq : s = p := (Nat.prime_dvd_prime_iff_eq hs hp).mp hsp
  exact ⟨hn, p, k, hp, hspeq ▸ hsQ, hk, hpow⟩

theorem actual_window_width_positive (B : ℕ) (hB : 0 < B)
    (R : ℝ) (hR : 1 < R) : 0 < (B : ℝ) / R^4 :=
  div_pos (Nat.cast_pos.mpr hB) (pow_pos (lt_trans zero_lt_one hR) 4)

/-- Actual Lambda block, actual rough cutoff, real H=B/R^4, and log weight.
All character-expansion support premises are discharged, not freely assumed. -/
theorem presieved_log_window_expansion (B N : ℕ) (R : ℝ) (G : ℝ → ℝ) :
    normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (presievedInput ⌊R^2⌋₊ B) (logWeight R G) =
      ∑ r : PositiveLevel ⌊R^2⌋₊,
        ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
          ((r.val : ℂ)/(r.val.totient : ℂ)) * χ.val (N : ZMod r.val) *
            finiteCompanion r N (logWeight R G) *
            ((2 * (((B : ℝ)/R^4 : ℝ) : ℂ))⁻¹ *
              ∑ U ∈ centeredWindow (blockCarrier B) N ((B : ℝ)/R^4),
                presievedInput ⌊R^2⌋₊ B U * star (χ.val (U : ZMod r.val))) := by
  exact normalized_window_character_expansion ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (presievedInput ⌊R^2⌋₊ B) (logWeight R G)
      (fun U _ hf q => presieved_input_unit_support ⌊R^2⌋₊ B U hf q)

end GoldbachCircleMethodLogCutoffPresieveBindingV18120
