import GoldbachCircleMethodRadicalProductLogSplitV18166

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodRadicalProductLogSplitV18166
open GoldbachCircleMethodBadPrimeProductComparisonV18165
namespace GoldbachCircleMethodRadicalMertensPrefixBindingV18167

noncomputable def saturationThreshold (R ξ : ℝ) : ℝ :=
  Real.exp (Real.log R/frequencyAmplitude ξ)

theorem frequencyAmplitude_one_le (ξ : ℝ) : 1 ≤ frequencyAmplitude ξ := by
  unfold frequencyAmplitude
  have h := abs_nonneg ξ
  linarith

theorem threshold_log (R ξ : ℝ) :
    Real.log (saturationThreshold R ξ) = Real.log R/frequencyAmplitude ξ := by
  exact Real.log_exp _

theorem threshold_one_lt {R : ℝ} (hR : 1 < R) (ξ : ℝ) :
    1 < saturationThreshold R ξ := by
  exact Real.one_lt_exp_iff.mpr (div_pos (Real.log_pos hR) (frequencyAmplitude_pos ξ))

theorem cutoff_iff_le_threshold {R : ℝ} (ξ : ℝ)
    {p : ℕ} (hp : p.Prime) :
    frequencyAmplitude ξ*Real.log (p : ℝ) ≤ Real.log R ↔
      (p : ℝ) ≤ saturationThreshold R ξ := by
  have hA := frequencyAmplitude_pos ξ
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [saturationThreshold, ← Real.log_le_iff_le_exp hpr, le_div_iff₀ hA]
  constructor <;> intro h <;> nlinarith

theorem lowCarrier_eq_filter {R : ℝ} (ξ : ℝ) (X : ℕ) :
    lowCarrier R ξ (primePrefix X) =
      (primePrefix X).filter (fun (p : ℕ) => (p : ℝ) ≤ saturationThreshold R ξ) := by
  ext p
  simp only [lowCarrier, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨hp, (cutoff_iff_le_threshold ξ (Finset.mem_filter.mp hp).2).mp hc⟩
  · rintro ⟨hp, hc⟩
    exact ⟨hp, (cutoff_iff_le_threshold ξ (Finset.mem_filter.mp hp).2).mpr hc⟩

theorem highCarrier_eq_filter {R : ℝ} (ξ : ℝ) (X : ℕ) :
    highCarrier R ξ (primePrefix X) =
      (primePrefix X).filter (fun (p : ℕ) => saturationThreshold R ξ < (p : ℝ)) := by
  ext p
  simp only [highCarrier, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨hp, lt_of_not_ge (fun h => hc
      ((cutoff_iff_le_threshold ξ (Finset.mem_filter.mp hp).2).mpr h))⟩
  · rintro ⟨hp, hc⟩
    exact ⟨hp, fun h => (not_le_of_gt hc)
      ((cutoff_iff_le_threshold ξ (Finset.mem_filter.mp hp).2).mp h)⟩

theorem threshold_le_upper {R X : ℝ} (hR : 1 < R) (hRX : R ≤ X) (ξ : ℝ) :
    saturationThreshold R ξ ≤ X := by
  have hX : 0 < X := (zero_lt_one.trans hR).trans_le hRX
  apply (Real.log_le_log_iff (Real.exp_pos _) hX).mp
  rw [Real.log_exp]
  calc
    _ ≤ Real.log R := div_le_self (le_of_lt (Real.log_pos hR)) (frequencyAmplitude_one_le ξ)
    _ ≤ Real.log X := Real.log_le_log (zero_lt_one.trans hR) hRX

theorem low_empty_below_two {R : ℝ} (ξ : ℝ) (X : ℕ)
    (hT : saturationThreshold R ξ < 2) :
    lowCarrier R ξ (primePrefix X) = ∅ := by
  rw [lowCarrier_eq_filter ξ X]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp, hc⟩
  have hprime := (Finset.mem_filter.mp hp).2
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  linarith

theorem high_full_below_two {R : ℝ} (ξ : ℝ) (X : ℕ)
    (hT : saturationThreshold R ξ < 2) :
    highCarrier R ξ (primePrefix X) = primePrefix X := by
  have he := (carriers_partition R ξ (primePrefix X)).2
  simpa only [low_empty_below_two ξ X hT, Finset.empty_union] using he

/-- Explicit external-source interface, with uniform constants passed once.
All sums retain the same finite prime prefix and both cutoff regimes. -/
theorem prefix_bound_from_mertens {X : ℕ} (hX : 2 ≤ X)
    {C0 C1 : ℝ} (hC0 : 0 ≤ C0)
    (hsmall : ∀ T : ℝ, 2 ≤ T → T ≤ (X : ℝ) →
      (∑ p ∈ (primePrefix X).filter (fun (p : ℕ) => (p : ℝ) ≤ T),
        Real.log (p : ℝ)/(p : ℝ)) ≤ C0*Real.log T)
    (htail : ∀ T : ℝ, 2 ≤ T → T ≤ (X : ℝ) →
      (∑ p ∈ (primePrefix X).filter (fun (p : ℕ) => T < (p : ℝ)), 1/(p : ℝ)) ≤
        C1+Real.log (Real.log (X : ℝ)/Real.log T))
    (hfull : (∑ p ∈ primePrefix X, 1/(p : ℝ)) ≤
      C1+Real.log (Real.log (X : ℝ)/Real.log 2))
    {R : ℝ} (hR : 1 < R) (hRX : R ≤ (X : ℝ)) (ξ : ℝ) :
    comparisonProduct R ξ (primePrefix X) ≤
      100*Real.exp (2*C0+2*C1)*(1+|ξ|)^2*(Real.log (X : ℝ)/Real.log R)^2 := by
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (by omega : 1<X)
  have hL := Real.log_pos hR
  have hA := frequencyAmplitude_pos ξ
  have hTX := threshold_le_upper hR hRX ξ
  have hT1 := threshold_one_lt hR ξ
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : Real.log (X : ℝ)/Real.log (saturationThreshold R ξ) =
      frequencyAmplitude ξ*Real.log (X : ℝ)/Real.log R := by
    rw [threshold_log]
    field_simp
  apply product_bound_of_log_moments hR ξ (primePrefix X)
    (fun p hp => (Finset.mem_filter.mp hp).2) hX1
  · by_cases hT : 2 ≤ saturationThreshold R ξ
    · unfold lowLogMoment
      rw [lowCarrier_eq_filter ξ X]
      have h := hsmall _ hT hTX
      rw [threshold_log] at h
      convert h using 1
      ring
    · rw [lowLogMoment, low_empty_below_two ξ X (lt_of_not_ge hT), Finset.sum_empty]
      positivity
  · by_cases hT : 2 ≤ saturationThreshold R ξ
    · unfold highHarmonicMoment
      rw [highCarrier_eq_filter ξ X]
      have h := htail _ hT hTX
      rwa [hratio] at h
    · rw [highHarmonicMoment, high_full_below_two ξ X (lt_of_not_ge hT)]
      apply hfull.trans
      refine add_le_add le_rfl ?_
      apply Real.log_le_log (div_pos (Real.log_pos hX1) hlog2)
      rw [← hratio]
      apply div_le_div_of_nonneg_left (Real.log_pos hX1).le (Real.log_pos hT1)
      exact Real.log_le_log (zero_lt_one.trans hT1) (le_of_lt (lt_of_not_ge hT))

end GoldbachCircleMethodRadicalMertensPrefixBindingV18167
