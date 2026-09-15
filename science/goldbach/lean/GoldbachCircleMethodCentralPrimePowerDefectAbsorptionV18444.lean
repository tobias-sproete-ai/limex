import GoldbachCircleMethodCentralQuantitativeSourceReserveV18443
import GoldbachPrimePowerDefectBoundV161
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Goldbach V1.8.444: central prime-power defect absorption

The exact prime-power defect is summed over the finite central target sweep.
Mathlib's explicit Chebyshev bound gives an `O(m^(3/2) log(m)^2)` envelope,
which is eventually strictly smaller than the retained quadratic source
reserve `((8*m)^2)/14336` from V1.8.443.

This closes the prime-power semantic obstruction for the central aggregate.
It supplies no analytic source estimate; therefore the full Goldbach status
remains `NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical Topology
open Filter

namespace GoldbachCircleMethodCentralPrimePowerDefectAbsorptionV18444

open GoldbachPrimePowerDefectBoundV161
open GoldbachVonMangoldtDecompositionV16
open GoldbachCircleMethodCanonicalCentralAdjustedPositiveV18403

/-- Sum of the exact prime-power defects on the central even-target sweep. -/
noncomputable def centralPrimePowerDefectSum (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 * m + 1), primePowerDefect (centralTargetNat m i)

/-- Uniform Chebyshev envelope for the central defect sum. -/
noncomputable def centralPrimePowerDefectEnvelope (m : ℕ) : ℝ :=
  (2 * m + 1 : ℝ) *
    (4 * Real.sqrt ((14 * m : ℕ) : ℝ) *
      (Real.log ((14 * m : ℕ) : ℝ)) ^ 2)

/-- Every target in the central sweep is at most `14*m`, so the sum of exact
defects is bounded by one common Chebyshev envelope. -/
theorem centralPrimePowerDefectSum_le_envelope
    (m : ℕ) (hm : 1 ≤ m) :
    centralPrimePowerDefectSum m ≤ centralPrimePowerDefectEnvelope m := by
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (2 * m + 1)) :
      primePowerDefect (centralTargetNat m i) ≤
        4 * Real.sqrt ((14 * m : ℕ) : ℝ) *
          (Real.log ((14 * m : ℕ) : ℝ)) ^ 2 := by
    have hi' : i < 2 * m + 1 := Finset.mem_range.mp hi
    have hNpos : 1 ≤ centralTargetNat m i := by
      simp only [centralTargetNat]
      omega
    have hNle : centralTargetNat m i ≤ 14 * m := by
      simp only [centralTargetNat]
      omega
    have hNRpos : (0 : ℝ) < centralTargetNat m i := by exact_mod_cast hNpos
    have hMRpos : (0 : ℝ) < 14 * m := by
      exact_mod_cast (show 0 < 14 * m by omega)
    have hcast : ((centralTargetNat m i : ℕ) : ℝ) ≤ ((14 * m : ℕ) : ℝ) := by
      exact_mod_cast hNle
    have hsqrt : Real.sqrt ((centralTargetNat m i : ℕ) : ℝ) ≤
        Real.sqrt ((14 * m : ℕ) : ℝ) := Real.sqrt_le_sqrt hcast
    have hlog : Real.log ((centralTargetNat m i : ℕ) : ℝ) ≤
        Real.log ((14 * m : ℕ) : ℝ) :=
      Real.log_le_log hNRpos hcast
    have hlogN : 0 ≤ Real.log ((centralTargetNat m i : ℕ) : ℝ) :=
      Real.log_natCast_nonneg _
    have hlogM : 0 ≤ Real.log ((14 * m : ℕ) : ℝ) :=
      Real.log_natCast_nonneg _
    calc
      primePowerDefect (centralTargetNat m i) ≤
          4 * Real.sqrt ((centralTargetNat m i : ℕ) : ℝ) *
            (Real.log ((centralTargetNat m i : ℕ) : ℝ)) ^ 2 :=
        primePowerDefect_le_four_sqrt_mul_log_sq hNpos
      _ ≤ 4 * Real.sqrt ((14 * m : ℕ) : ℝ) *
            (Real.log ((14 * m : ℕ) : ℝ)) ^ 2 := by
        gcongr
  unfold centralPrimePowerDefectSum centralPrimePowerDefectEnvelope
  calc
    (∑ i ∈ Finset.range (2 * m + 1),
        primePowerDefect (centralTargetNat m i)) ≤
      ∑ _i ∈ Finset.range (2 * m + 1),
        (4 * Real.sqrt ((14 * m : ℕ) : ℝ) *
          (Real.log ((14 * m : ℕ) : ℝ)) ^ 2) := Finset.sum_le_sum hpoint
    _ = (2 * m + 1 : ℝ) *
        (4 * Real.sqrt ((14 * m : ℕ) : ℝ) *
          (Real.log ((14 * m : ℕ) : ℝ)) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

/-- The Chebyshev defect envelope is eventually absorbed by the exact central
quadratic reserve. -/
theorem eventual_centralPrimePowerDefectEnvelope_lt_reserve :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      centralPrimePowerDefectEnvelope m <
        ((8 * m : ℕ) : ℝ) ^ 2 / 14336 := by
  have hbase :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num)).tendsto_div_nhds_zero
  have harg : Tendsto (fun m : ℕ => ((14 * m : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 14 by norm_num)
  have hratio : Tendsto (fun m : ℕ =>
      (Real.log ((14 * m : ℕ) : ℝ)) ^ 2 /
        Real.sqrt ((14 * m : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_two, Real.sqrt_eq_rpow] using
      hbase.comp harg
  have hsmall : ∀ᶠ m : ℕ in atTop,
      (Real.log ((14 * m : ℕ) : ℝ)) ^ 2 /
          Real.sqrt ((14 * m : ℕ) : ℝ) <
        (1 : ℝ) / 37632 :=
    (tendsto_order.1 hratio).2 ((1 : ℝ) / 37632) (by norm_num)
  apply eventually_atTop.mp
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with m hsmall hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hMR : (0 : ℝ) < ((14 * m : ℕ) : ℝ) := by positivity
  have hsqrt : (0 : ℝ) < Real.sqrt ((14 * m : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr hMR
  have hsqrtSq :
      Real.sqrt ((14 * m : ℕ) : ℝ) *
          Real.sqrt ((14 * m : ℕ) : ℝ) = ((14 * m : ℕ) : ℝ) :=
    Real.mul_self_sqrt hMR.le
  have hrootLog :
      Real.sqrt ((14 * m : ℕ) : ℝ) *
          (Real.log ((14 * m : ℕ) : ℝ)) ^ 2 <
        ((14 * m : ℕ) : ℝ) / 37632 := by
    have hdiv := (div_lt_iff₀ hsqrt).mp hsmall
    have hmul := mul_lt_mul_of_pos_left hdiv hsqrt
    calc
      Real.sqrt ((14 * m : ℕ) : ℝ) *
          (Real.log ((14 * m : ℕ) : ℝ)) ^ 2 <
        Real.sqrt ((14 * m : ℕ) : ℝ) *
          ((1 : ℝ) / 37632 * Real.sqrt ((14 * m : ℕ) : ℝ)) := hmul
      _ = ((1 : ℝ) / 37632) *
          (Real.sqrt ((14 * m : ℕ) : ℝ) *
            Real.sqrt ((14 * m : ℕ) : ℝ)) := by ring
      _ = ((14 * m : ℕ) : ℝ) / 37632 := by rw [hsqrtSq]; ring
  have hcount : (2 * m + 1 : ℝ) ≤ 3 * (m : ℝ) := by
    exact_mod_cast (show 2 * m + 1 ≤ 3 * m by omega)
  have hfactor : 0 ≤ 4 * Real.sqrt ((14 * m : ℕ) : ℝ) *
      (Real.log ((14 * m : ℕ) : ℝ)) ^ 2 := by positivity
  have henv : centralPrimePowerDefectEnvelope m ≤
      12 * (m : ℝ) *
        (Real.sqrt ((14 * m : ℕ) : ℝ) *
          (Real.log ((14 * m : ℕ) : ℝ)) ^ 2) := by
    unfold centralPrimePowerDefectEnvelope
    have := mul_le_mul_of_nonneg_right hcount hfactor
    nlinarith
  have hscaled := mul_lt_mul_of_pos_left hrootLog
    (show (0 : ℝ) < 12 * m by positivity)
  calc
    centralPrimePowerDefectEnvelope m ≤
        12 * (m : ℝ) *
          (Real.sqrt ((14 * m : ℕ) : ℝ) *
            (Real.log ((14 * m : ℕ) : ℝ)) ^ 2) := henv
    _ < 12 * (m : ℝ) * (((14 * m : ℕ) : ℝ) / 37632) := by
      nlinarith
    _ = ((8 * m : ℕ) : ℝ) ^ 2 / 14336 := by
      push_cast
      ring

/-- The exact sum of all prime-power defects on the central sweep is
eventually strictly smaller than the retained source reserve. -/
theorem eventual_centralPrimePowerDefectSum_lt_reserve :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      centralPrimePowerDefectSum m <
        ((8 * m : ℕ) : ℝ) ^ 2 / 14336 := by
  obtain ⟨m₀, henv⟩ := eventual_centralPrimePowerDefectEnvelope_lt_reserve
  refine ⟨max m₀ 1, ?_⟩
  intro m hm
  have hm₀ : m₀ ≤ m := (le_max_left m₀ 1).trans hm
  have hmOne : 1 ≤ m := (le_max_right m₀ 1).trans hm
  exact (centralPrimePowerDefectSum_le_envelope m hmOne).trans_lt (henv m hm₀)

end GoldbachCircleMethodCentralPrimePowerDefectAbsorptionV18444
