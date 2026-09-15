import GoldbachCircleMethodFiniteDyadicExceptionCarrierV1876

/-! # V1.8.77: finite logarithmic sum transfer on dyadic cutoffs.
Small values are retained, not declared nonexceptional.
-/
set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodFiniteDyadicExceptionCarrierV1876
open GoldbachCircleMethodLogarithmicBlockDecayV1875
open GoldbachCircleMethodArithmeticProgressionInputMatchV1871
open GoldbachCircleMethodRealApproximationMinorAdapterV1873

namespace GoldbachCircleMethodDyadicLogarithmicSumTransferV1877

theorem globalExceptions_mono {X Y : ℕ} (hXY : X ≤ Y) :
    globalExceptions X ⊆ globalExceptions Y := by
  intro N hn
  obtain ⟨h4, hx, he, hg⟩ := (mem_globalExceptions_iff _ _).mp hn
  exact (mem_globalExceptions_iff _ _).mpr ⟨h4, hx.trans hXY, he, hg⟩

theorem dyadic_log_lower_half (m j : ℕ) (hm : 0 < m) (hj : m/2+1 ≤ j) :
    0 < Real.log ((2 : ℝ)^m) ∧
      0 < Real.log ((2 : ℝ)^j) ∧
      Real.log ((2 : ℝ)^m) ≤ 2*Real.log ((2 : ℝ)^j) := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hle : (m : ℝ) ≤ 2*(j : ℝ) := by exact_mod_cast (show m ≤ 2*j by omega)
  rw [Real.log_pow, Real.log_pow]
  refine ⟨mul_pos hmR h2, mul_pos hjR h2, ?_⟩
  nlinarith

theorem dyadic_weight_sum_le (A m : ℕ) (hm : 0 < m) :
    (∑ j ∈ Finset.Icc (m/2+1) m, (2 : ℝ)^j/(Real.log ((2 : ℝ)^j))^A) ≤
      (2 : ℝ)^(A+1)*(2 : ℝ)^m/(Real.log ((2 : ℝ)^m))^A := by
  have hlog := (dyadic_log_lower_half m (m/2+1) hm le_rfl).1
  have hp : 0 < (Real.log ((2 : ℝ)^m))^A := pow_pos hlog _
  have hterm : ∀ j ∈ Finset.Icc (m/2+1) m,
      (2 : ℝ)^j/(Real.log ((2 : ℝ)^j))^A ≤
        ((2 : ℝ)^A/(Real.log ((2 : ℝ)^m))^A)*(2 : ℝ)^j := by
    intro j hj
    have hl := dyadic_log_lower_half m j hm (Finset.mem_Icc.mp hj).1
    have hjp : 0 < (Real.log ((2 : ℝ)^j))^A := pow_pos hl.2.1 _
    have hpow := pow_le_pow_left₀ hl.1.le hl.2.2 A
    rw [mul_pow] at hpow
    have hfrac : 1/(Real.log ((2 : ℝ)^j))^A ≤
        (2 : ℝ)^A/(Real.log ((2 : ℝ)^m))^A := by
      rw [div_le_div_iff₀ hjp hp]
      simpa only [one_mul] using hpow
    calc
      _ = (1/(Real.log ((2 : ℝ)^j))^A)*(2 : ℝ)^j := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfrac (by positivity)
  have hgeo : (∑ j ∈ Finset.Icc (m/2+1) m, (2 : ℝ)^j) ≤ (2 : ℝ)^(m+1) := by
    have hsub : Finset.Icc (m/2+1) m ⊆ Finset.range (m+1) := by
      intro j hj
      exact Finset.mem_range.mpr (by have h := (Finset.mem_Icc.mp hj).2; omega)
    calc
      _ ≤ ∑ j ∈ Finset.range (m+1), (2 : ℝ)^j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ = (2 : ℝ)^(m+1)-1 := dyadic_geometric_sum m
      _ ≤ _ := by linarith
  calc
    _ ≤ ∑ j ∈ Finset.Icc (m/2+1) m,
        ((2 : ℝ)^A/(Real.log ((2 : ℝ)^m))^A)*(2 : ℝ)^j :=
      Finset.sum_le_sum hterm
    _ = ((2 : ℝ)^A/(Real.log ((2 : ℝ)^m))^A)*
        (∑ j ∈ Finset.Icc (m/2+1) m, (2 : ℝ)^j) := by rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ)^A/(Real.log ((2 : ℝ)^m))^A)*(2 : ℝ)^(m+1) :=
      mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = _ := by rw [pow_succ, pow_succ]; ring

theorem global_dyadic_bound_of_block_bound (A m M₀ : ℕ) (hm : 0 < m)
    (hM₀ : M₀ ≤ 2^(m/2+1))
    (hblock : ∀ M ≥ M₀,
      (((evenTargetBlock M).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
        (M : ℝ)/(Real.log (M : ℝ))^A) :
    ((globalExceptions (2^m)).card : ℝ) ≤
      (2 : ℝ)^(m/2)+(2 : ℝ)^(A+1)*(2 : ℝ)^m/(Real.log ((2 : ℝ)^m))^A := by
  have hb : ∀ j ∈ Finset.Icc (m/2+1) m,
      (((evenTargetBlock (2^j)).filter (fun N => ¬ GoldbachAt N)).card : ℝ) ≤
        (2 : ℝ)^j/(Real.log ((2 : ℝ)^j))^A := by
    intro j hj
    have hMj : M₀ ≤ 2^j := hM₀.trans
      (Nat.pow_le_pow_right (by norm_num) (Finset.mem_Icc.mp hj).1)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hblock (2^j) hMj
  exact (globalExceptions_pow_card_le_real m (m/2) _ hb).trans
    (add_le_add le_rfl (dyadic_weight_sum_le A m hm))

theorem conditional_global_dyadic_bound (A k₀ : ℕ) (Csw csw Cv : ℝ)
    (hCsw : 0 ≤ Csw) (hcsw : 0 < csw) (hCv : 0 ≤ Cv)
    (hAP : ScaleAPEstimate (A+12) k₀ Csw csw) (hV : RealVaughanEstimate Cv) :
    ∃ M₀ : ℕ, ∀ m : ℕ, 0 < m → M₀ ≤ 2^(m/2+1) →
      ((globalExceptions (2^m)).card : ℝ) ≤
        (2 : ℝ)^(m/2)+(2 : ℝ)^(A+1)*(2 : ℝ)^m/(Real.log ((2 : ℝ)^m))^A := by
  obtain ⟨M₀, hb⟩ := eventual_evenBlock_log_decay_of_two_analytic_inputs
    A k₀ Csw csw Cv hCsw hcsw hCv hAP hV
  exact ⟨M₀, fun m hm hM₀ => global_dyadic_bound_of_block_bound A m M₀ hm hM₀ hb⟩

end GoldbachCircleMethodDyadicLogarithmicSumTransferV1877
