import GoldbachCircleMethodConductorFilteredFinitePrefixFloorV18216
import Mathlib.Algebra.BigOperators.Module

/-!
# V1.8.217: conditional weighted binding preflight

This module performs only a finite Abel transfer for the conductor-filtered
Fourier coefficients established in V1.8.216. The weight is an explicit
hypothesis: nonnegative at the final admitted level and nonincreasing on the
whole finite interval. The final theorem instantiates the level with the
literal conductor threshold `Q / r`.

No property of the historical smooth mask is inferred here, and no equality
with `coupledDiagonal`, reserve, exceptional-set bound, or Goldbach conclusion
is claimed.
-/

set_option autoImplicit false

open scoped BigOperators

namespace GoldbachCircleMethodConditionalWeightedBindingPreflightV18217

open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodFullSquarefreePrefixFloorV1848
open GoldbachCircleMethodRestrictedFilteredCarrierReindexV18215
open GoldbachCircleMethodConductorFilteredFinitePrefixFloorV18216

/-- The all-modulus coefficient with the conductor coprimality filter retained.
Nonsquarefree and conductor-noncoprime levels are zero by definition. -/
noncomputable def restrictedRealFourierCoefficient (N r q : ℕ) : ℝ :=
  if Squarefree q ∧ Nat.Coprime q r then realFourierCoefficient N q else 0

/-- Exact finite carrier readback for the conductor-filtered prefix. -/
theorem restricted_Icc_eq_fourier_prefix (N r H : ℕ) :
    (∑ q ∈ Finset.Icc 1 H, restrictedRealFourierCoefficient N r q) =
      restrictedSquarefreeFourierPrefix N r H := by
  unfold restrictedSquarefreeFourierPrefix restrictedSquarefreePrefix
  have hset :
      (fullSquarefreePrefix H).filter (fun q => Nat.Coprime q r) =
        (Finset.Icc 1 H).filter (fun q => Squarefree q ∧ Nat.Coprime q r) := by
    ext q
    simp only [Finset.mem_filter, mem_fullSquarefreePrefix, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hqH, hsq⟩, hcop⟩
      exact ⟨⟨hsq.ne_zero.bot_lt, hqH⟩, hsq, hcop⟩
    · rintro ⟨⟨_, hqH⟩, hsq, hcop⟩
      exact ⟨⟨hqH, hsq⟩, hcop⟩
  rw [hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : Squarefree q ∧ Nat.Coprime q r
  · simp [restrictedRealFourierCoefficient, hp]
  · simp [restrictedRealFourierCoefficient, hp]

/-- Index translation from `0,...,H-1` to the exact positive interval `1,...,H`. -/
theorem shifted_sum (f : ℕ → ℝ) (H : ℕ) :
    (∑ i ∈ Finset.range H, f (i + 1)) = ∑ q ∈ Finset.Icc 1 H, f q := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- Shifted range form used by the finite Abel adapter. -/
theorem shifted_restricted_coefficient_sum (N r H : ℕ) :
    (∑ i ∈ Finset.range H, restrictedRealFourierCoefficient N r (i + 1)) =
      restrictedSquarefreeFourierPrefix N r H := by
  rw [shifted_sum]
  exact restricted_Icc_eq_fourier_prefix N r H

theorem sum_weight_drops (w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (w i - w (i + 1))) = w 0 - w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Local finite Abel inequality, restated to keep this append-only module on
the V1.8.216 dependency branch. -/
theorem weighted_prefix_lower_bound (a w : ℕ → ℝ) (κ : ℝ) (n : ℕ)
    (hn : 1 ≤ n)
    (hprefix : ∀ k, 1 ≤ k → k ≤ n → κ ≤ ∑ i ∈ Finset.range k, a i)
    (hlast : 0 ≤ w (n - 1))
    (hmono : ∀ i, i + 1 < n → w (i + 1) ≤ w i) :
    κ * w 0 ≤ ∑ i ∈ Finset.range n, w i * a i := by
  have habel := Finset.sum_range_by_parts w a n
  simp only [smul_eq_mul] at habel
  have htop := mul_le_mul_of_nonneg_left (hprefix n hn le_rfl) hlast
  have hdiff :
      (∑ i ∈ Finset.range (n - 1),
        (w (i + 1) - w i) * (∑ j ∈ Finset.range (i + 1), a j)) ≤
        (w (n - 1) - w 0) * κ := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * κ := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact mul_le_mul_of_nonpos_left (hprefix (i + 1) (by omega) (by omega))
          (sub_nonpos.mpr (hmono i (by omega)))
      _ = (w (n - 1) - w 0) * κ := by
        rw [← Finset.sum_mul]
        congr 1
        have hd := sum_weight_drops w (n - 1)
        have hneg : (∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i)) =
            -(∑ i ∈ Finset.range (n - 1), (w i - w (i + 1))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hneg, hd]
        ring
  nlinarith

/-- Conditional Abel transfer. Monotonicity is supplied, not inferred. -/
theorem conditional_weighted_restricted_prefix_floor
    {N r H : ℕ} (hEven : Even N) (hr : 0 < r) (hH : 1 ≤ H)
    (w : ℕ → ℝ) (hlast : 0 ≤ w H)
    (hmono : ∀ q, 1 ≤ q → q < H → w (q + 1) ≤ w q) :
    (2 - Real.exp (Real.pi ^ 2 / 24)) * w 1 ≤
      ∑ i ∈ Finset.range H,
        w (i + 1) * restrictedRealFourierCoefficient N r (i + 1) := by
  have h := weighted_prefix_lower_bound
    (fun i => restrictedRealFourierCoefficient N r (i + 1))
    (fun i => w (i + 1))
    (2 - Real.exp (Real.pi ^ 2 / 24)) H hH
    (by
      intro k hk hkH
      rw [shifted_restricted_coefficient_sum]
      exact restrictedSquarefreeFourierPrefix_ge_kappa hEven hr hk)
    (by simpa [Nat.sub_add_cancel hH] using hlast)
    (by
      intro i hi
      exact hmono (i + 1) (by omega) hi)
  simpa using h

/-- A positive admitted conductor has a nonempty exact quotient threshold. -/
theorem conductor_threshold_at_least_one {Q r : ℕ}
    (hr : 0 < r) (hrQ : r ≤ Q) : 1 ≤ Q / r := by
  exact (Nat.le_div_iff_mul_le hr).mpr (by simpa using hrQ)

/-- The same conditional floor at the literal coupled cutoff `l ≤ Q / r`.
The supplied weight is evaluated at the original product level `r*l`. -/
theorem conditional_weighted_conductor_threshold_floor
    {N Q r : ℕ} (hEven : Even N) (hr : 0 < r) (hrQ : r ≤ Q)
    (w : ℕ → ℝ) (hlast : 0 ≤ w (r * (Q / r)))
    (hmono : ∀ l, 1 ≤ l → l < Q / r →
      w (r * (l + 1)) ≤ w (r * l)) :
    (2 - Real.exp (Real.pi ^ 2 / 24)) * w r ≤
      ∑ i ∈ Finset.range (Q / r),
        w (r * (i + 1)) * restrictedRealFourierCoefficient N r (i + 1) := by
  have hH : 1 ≤ Q / r := conductor_threshold_at_least_one hr hrQ
  have h := conditional_weighted_restricted_prefix_floor hEven hr hH
    (fun l => w (r * l)) hlast hmono
  simpa using h

end GoldbachCircleMethodConditionalWeightedBindingPreflightV18217
