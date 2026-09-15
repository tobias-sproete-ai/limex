import GoldbachCircleMethodBadPrimeProductComparisonV18165

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodBadPrimeProductComparisonV18165
namespace GoldbachCircleMethodRadicalProductLogSplitV18166

noncomputable def frequencyAmplitude (ξ : ℝ) : ℝ := 10*(1+|ξ|)

theorem frequencyAmplitude_pos (ξ : ℝ) : 0 < frequencyAmplitude ξ := by
  unfold frequencyAmplitude
  positivity

noncomputable def lowCarrier (R ξ : ℝ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun p => frequencyAmplitude ξ*Real.log (p : ℝ) ≤ Real.log R)

noncomputable def highCarrier (R ξ : ℝ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun p => ¬frequencyAmplitude ξ*Real.log (p : ℝ) ≤ Real.log R)

noncomputable def lowLogMoment (R ξ : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ lowCarrier R ξ S, Real.log (p : ℝ)/(p : ℝ)

noncomputable def highHarmonicMoment (R ξ : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ highCarrier R ξ S, 1/(p : ℝ)

theorem carriers_partition (R ξ : ℝ) (S : Finset ℕ) :
    Disjoint (lowCarrier R ξ S) (highCarrier R ξ S) ∧
    lowCarrier R ξ S ∪ highCarrier R ξ S = S := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hp).2
  · ext p
    simp only [lowCarrier, highCarrier, Finset.mem_union, Finset.mem_filter]
    tauto

theorem radicalLocal_low {R ξ : ℝ} (hR : 1 < R) {p : ℕ}
    (hp : frequencyAmplitude ξ*Real.log (p : ℝ) ≤ Real.log R) :
    radicalLocal R ξ p = frequencyAmplitude ξ*Real.log (p : ℝ)/Real.log R := by
  exact min_eq_right ((div_le_one (Real.log_pos hR)).mpr hp)

theorem radicalLocal_high {R ξ : ℝ} (hR : 1 < R) {p : ℕ}
    (hp : ¬frequencyAmplitude ξ*Real.log (p : ℝ) ≤ Real.log R) :
    radicalLocal R ξ p = 1 := by
  apply min_eq_left
  exact (one_le_div (Real.log_pos hR)).mpr (le_of_lt (lt_of_not_ge hp))

theorem weighted_sum_split {R : ℝ} (hR : 1 < R) (ξ : ℝ) (S : Finset ℕ) :
    (∑ p ∈ S, 2*radicalLocal R ξ p/(p : ℝ)) =
      (2*frequencyAmplitude ξ/Real.log R)*lowLogMoment R ξ S +
        2*highHarmonicMoment R ξ S := by
  have he := (carriers_partition R ξ S).2
  calc
    _ = (∑ p ∈ lowCarrier R ξ S, 2*radicalLocal R ξ p/(p : ℝ)) +
        ∑ p ∈ highCarrier R ξ S, 2*radicalLocal R ξ p/(p : ℝ) := by
      rw [← Finset.sum_union (carriers_partition R ξ S).1, he]
    _ = _ := by
      congr 1
      · unfold lowLogMoment
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [radicalLocal_low hR (Finset.mem_filter.mp hp).2]
        ring
      · unfold highHarmonicMoment
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [radicalLocal_high hR (Finset.mem_filter.mp hp).2]
        ring

/-- Conditional transfer of the two stated finite Mertens-type bounds.
The hypotheses are not declared proved by this interface. -/
theorem product_bound_of_log_moments {R : ℝ} (hR : 1 < R) (ξ : ℝ)
    (S : Finset ℕ) (hs : ∀ p ∈ S, p.Prime) {X C0 C1 : ℝ}
    (hX : 1 < X)
    (hlo : lowLogMoment R ξ S ≤ C0*Real.log R/frequencyAmplitude ξ)
    (hhi : highHarmonicMoment R ξ S ≤
      C1+Real.log (frequencyAmplitude ξ*Real.log X/Real.log R)) :
    comparisonProduct R ξ S ≤
      100*Real.exp (2*C0+2*C1)*(1+|ξ|)^2*(Real.log X/Real.log R)^2 := by
  have hL := Real.log_pos hR
  have hA := frequencyAmplitude_pos ξ
  have hB : 0 < frequencyAmplitude ξ*Real.log X/Real.log R :=
    div_pos (mul_pos hA (Real.log_pos hX)) hL
  have hl : (2*frequencyAmplitude ξ/Real.log R)*lowLogMoment R ξ S ≤ 2*C0 := by
    calc
      _ ≤ (2*frequencyAmplitude ξ/Real.log R)*(C0*Real.log R/frequencyAmplitude ξ) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = _ := by field_simp
  have hu : (∑ p ∈ S, 2*radicalLocal R ξ p/(p : ℝ)) ≤
      2*C0+2*C1+2*Real.log (frequencyAmplitude ξ*Real.log X/Real.log R) := by
    rw [weighted_sum_split hR ξ S]
    linarith
  calc
    _ ≤ Real.exp (∑ p ∈ S, 2*radicalLocal R ξ p/(p : ℝ)) :=
      comparisonProduct_le_exp_sum hR ξ hs
    _ ≤ Real.exp (2*C0+2*C1+2*Real.log (frequencyAmplitude ξ*Real.log X/Real.log R)) :=
      Real.exp_le_exp.mpr hu
    _ = _ := by
      rw [show 2*C0+2*C1+2*Real.log (frequencyAmplitude ξ*Real.log X/Real.log R) =
        (2*C0+2*C1)+(Real.log (frequencyAmplitude ξ*Real.log X/Real.log R)+
          Real.log (frequencyAmplitude ξ*Real.log X/Real.log R)) by ring]
      simp only [Real.exp_add, Real.exp_log hB]
      unfold frequencyAmplitude
      ring

end GoldbachCircleMethodRadicalProductLogSplitV18166
