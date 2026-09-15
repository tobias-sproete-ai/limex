import GoldbachCircleMethodCompanionDivisorReindexV18140
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false
open scoped BigOperators Classical
namespace GoldbachCircleMethodCompanionAbsoluteConvergenceV18141

/-- Elementary global majorant, including non-squarefree input. -/
theorem nat_le_divisor_count_mul_totient (n : ℕ) :
    n ≤ n.divisors.card*n.totient := by
  by_cases hn : n=0
  · simp [hn]
  · calc
      n = ∑ d ∈ n.divisors, d.totient := (Nat.sum_totient n).symm
      _ ≤ ∑ _d ∈ n.divisors, n.totient := by
        apply Finset.sum_le_sum
        intro d hd
        exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))
          (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
      _ = _ := by simp

theorem reciprocal_totient_le_divisor_ratio {n : ℕ} (hn : 0<n) :
    1/(n.totient : ℝ) ≤ (n.divisors.card : ℝ)/(n : ℝ) := by
  have hp : 0<(n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hnR : 0<(n : ℝ) := by exact_mod_cast hn
  rw [div_le_div_iff₀ hp hnR]
  simpa using (show (n : ℝ)≤(n.divisors.card : ℝ)*(n.totient : ℝ) by
    exact_mod_cast nat_le_divisor_count_mul_totient n)

/-- A summable, deliberately non-sharp majorant for absolute convergence. -/
noncomputable def divisorMajorant (σ : ℝ) (n : ℕ) : ℝ :=
  if n=0 then 0 else (n.divisors.card : ℝ)/(n : ℝ)^(1+σ)

theorem divisorMajorant_nonneg (σ : ℝ) (n : ℕ) : 0≤divisorMajorant σ n := by
  unfold divisorMajorant
  split_ifs
  · rfl
  · positivity

theorem zeta_convolution_eq_divisor_count (n : ℕ) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n) =
      (n.divisors.card : ℂ) := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  calc
    _ = ∑ _d ∈ n.divisors, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := by
        intro hz
        have hzN : n=0 := Nat.zero_dvd.mp (hz ▸ Nat.dvd_of_mem_divisors hd)
        exact Nat.ne_zero_of_mem_divisors hd hzN
      rw [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne hd0,Nat.cast_one]
    _ = _ := by simp

theorem summable_divisorMajorant {σ : ℝ} (hσ : 0<σ) :
    Summable (divisorMajorant σ) := by
  have hz : LSeriesSummable (fun n => (ArithmeticFunction.zeta n : ℂ))
      ((1+σ : ℝ) : ℂ) :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr (by simpa using hσ)
  have hzz := ArithmeticFunction.LSeriesSummable_mul
    (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
    (g := (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) hz hz
  apply hzz.norm.congr
  intro n
  rw [LSeries.norm_term_eq,zeta_convolution_eq_divisor_count]
  simp only [Complex.norm_natCast,Complex.ofReal_re]
  rfl

/-- Actual complementary Dirichlet coefficient after the finite reindex.
At n=0 the squarefree guard forces zero. -/
noncomputable def complementaryDirichletTerm (k : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  if Squarefree n ∧ Nat.Coprime k n then
    1/((n.totient : ℂ)*(n : ℂ)^s)
  else 0

theorem complementaryDirichletTerm_norm_le (k : ℕ) (s : ℂ) (n : ℕ) :
    ‖complementaryDirichletTerm k s n‖ ≤ divisorMajorant s.re n := by
  unfold complementaryDirichletTerm
  split_ifs with hn
  · have hnpos : 0<n := hn.1.ne_zero.bot_lt
    have hp : 0<(n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hnpos
    have hnR : 0<(n : ℝ) := by exact_mod_cast hnpos
    rw [norm_div,norm_one,norm_mul,Complex.norm_natCast,
      Complex.norm_natCast_cpow_of_pos hnpos]
    rw [divisorMajorant,if_neg hn.1.ne_zero]
    have hb := div_le_div_of_nonneg_right
      (reciprocal_totient_le_divisor_ratio hnpos)
      (Real.rpow_nonneg hnR.le s.re)
    rw [div_div,div_div] at hb
    simpa only [Real.rpow_add hnR,Real.rpow_one] using hb
  · simpa only [norm_zero] using divisorMajorant_nonneg s.re n

/-- Unconditional absolute convergence in the precise half-plane re(s)>0.
No Fourier interchange or uniform logarithmic bound is claimed. -/
theorem summable_complementaryDirichletTerm_norm (k : ℕ) {s : ℂ}
    (hs : 0<s.re) :
    Summable (fun n => ‖complementaryDirichletTerm k s n‖) :=
  (summable_divisorMajorant hs).of_nonneg_of_le
    (fun _ => norm_nonneg _) (complementaryDirichletTerm_norm_le k s)

theorem summable_complementaryDirichletTerm (k : ℕ) {s : ℂ}
    (hs : 0<s.re) :
    Summable (complementaryDirichletTerm k s) :=
  (summable_complementaryDirichletTerm_norm k hs).of_norm


/-- A uniform-in-conductor and imaginary-part bound used ONLY for
absolute domination. Its dependence on re(s) is not estimated here. -/
theorem complementaryDirichletSeries_norm_le (k : ℕ) {s : ℂ} (hs : 0<s.re) :
    ‖∑' n, complementaryDirichletTerm k s n‖ ≤ ∑' n, divisorMajorant s.re n := by
  calc
    _ ≤ ∑' n, ‖complementaryDirichletTerm k s n‖ :=
      norm_tsum_le_tsum_norm (summable_complementaryDirichletTerm_norm k hs)
    _ ≤ _ := (summable_complementaryDirichletTerm_norm k hs).tsum_le_tsum
      (complementaryDirichletTerm_norm_le k s) (summable_divisorMajorant hs)

/-- Sign convention of the V98 inverse Fourier representation. -/
noncomputable def radicalExponent (R ξ : ℝ) : ℂ :=
  ((1 : ℂ)+Complex.I*(ξ : ℂ))/(Real.log R : ℂ)

theorem radicalExponent_re (R ξ : ℝ) :
    (radicalExponent R ξ).re=1/Real.log R := by
  simp [radicalExponent]

theorem radicalExponent_re_pos {R : ℝ} (hR : 1<R) (ξ : ℝ) :
    0<(radicalExponent R ξ).re := by
  rw [radicalExponent_re]
  exact one_div_pos.mpr (Real.log_pos hR)

/-- The actual V98 vertical line has one fixed summable majorant for
every real Fourier frequency and every conductor k. -/
theorem radical_line_absolute_domination {R : ℝ} (hR : 1<R)
    (k : ℕ) (ξ : ℝ) :
    Summable (fun n => ‖complementaryDirichletTerm k (radicalExponent R ξ) n‖) ∧
    (∀ n, ‖complementaryDirichletTerm k (radicalExponent R ξ) n‖ ≤
      divisorMajorant (1/Real.log R) n) ∧
    Summable (divisorMajorant (1/Real.log R)) := by
  have hs := radicalExponent_re_pos hR ξ
  refine ⟨summable_complementaryDirichletTerm_norm k hs,?_,?_⟩
  · intro n
    simpa only [radicalExponent_re] using
      complementaryDirichletTerm_norm_le k (radicalExponent R ξ) n
  · exact summable_divisorMajorant (one_div_pos.mpr (Real.log_pos hR))

end GoldbachCircleMethodCompanionAbsoluteConvergenceV18141
