import GoldbachCircleMethodActualMultiplierScaleV18135
import GoldbachCircleMethodRealApproximationMinorAdapterV1873

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodActualOutputTailBoundV18132
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodSeparatedFrequencyMultiplierV18134
open GoldbachCircleMethodActualMultiplierScaleV18135
open GoldbachCircleMethodTwoScaleDirichletBindingV1830
open GoldbachCircleMethodRealApproximationMinorAdapterV1873

namespace GoldbachCircleMethodActualBlockAuxiliaryMinorV18136

/-- Exactly the V120 Lambda input on the half-open integer block. -/
noncomputable def blockFourier (B : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ n ∈ blockCarrier B, blockInput B n * fourier (n : ℤ) x

/-- Explicit auxiliary-major region; not the original V87 mask. -/
def auxiliaryMajor (B R : ℝ) : Set UnitAddCircle :=
  {x | ∃ i : ReducedRationalIndex ⌊R^2⌋₊,
    (i.val.1 : ℝ)≤R ∧ dist x (majorArcCenter i)≤R/B}

theorem block_carrier_as_range_difference (B : ℕ) :
    blockCarrier B = Finset.range (B+1) \ Finset.range (B/2+1) := by
  ext n
  simp only [blockCarrier,Finset.mem_Ioc,Finset.mem_sdiff,Finset.mem_range]
  omega

theorem block_fourier_prefix_difference (B : ℕ) (x : UnitAddCircle) :
    blockFourier B x =
      exponentialSum B.succ x - exponentialSum (B/2).succ x := by
  have he : blockFourier B x = ∑ n ∈ blockCarrier B,
      (ArithmeticFunction.vonMangoldt n : ℂ)*fourier (n : ℤ) x := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [blockInput,hn,if_true]
  rw [he,block_carrier_as_range_difference]
  rw [Finset.sum_sdiff_eq_sub (Finset.range_mono (by omega : B/2+1≤B+1))]
  simp only [exponentialSum,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    Nat.succ_eq_add_one]

theorem block_fourier_norm_le (B : ℕ) (hB : 1≤B) (x : UnitAddCircle) :
    ‖blockFourier B x‖≤(B : ℝ)*Real.log (B : ℝ) := by
  have hlog : 0≤Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  unfold blockFourier
  calc
    _ ≤ ∑ n ∈ blockCarrier B, ‖blockInput B n*fourier (n : ℤ) x‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ blockCarrier B, Real.log (B : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [norm_mul,fourier_apply,Circle.norm_coe,mul_one] using
        block_input_norm_le_log B n hn
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hlog
      have hc : (blockCarrier B).card≤B := by simp [blockCarrier,Nat.card_Ioc]
      exact_mod_cast hc

/-- Move only an already reduced rational index to another sufficient cutoff. -/
def reindexCenter {T Q : ℕ} (i : ReducedRationalIndex T) (hq : i.val.1≤Q) :
    ReducedRationalIndex Q :=
  ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨index_denominator_pos i,hq⟩,
     Finset.mem_range.mpr ((Finset.mem_filter.mp i.property).2.1.trans_le hq)⟩,
    (Finset.mem_filter.mp i.property).2⟩⟩

theorem reindex_center_value {T Q : ℕ} (i : ReducedRationalIndex T) (hq : i.val.1≤Q) :
    majorArcCenter (reindexCenter i hq)=majorArcCenter i := rfl

theorem auxiliary_dirichlet_denominator_bounds (B R : ℝ) (hR : 0<R) (hBR : R≤B) :
    0<⌈B/R⌉₊ ∧ B/R≤(⌈B/R⌉₊ : ℝ) ∧ (⌈B/R⌉₊ : ℝ)≤2*B/R := by
  have hratio : 1≤B/R := (le_div_iff₀ hR).mpr (by simpa using hBR)
  have hceil := Nat.ceil_lt_add_one (show 0≤B/R by linarith)
  refine ⟨Nat.ceil_pos.mpr (by linarith),Nat.le_ceil _,?_⟩
  rw [show 2*B/R=2*(B/R) by ring]
  linarith

/-- The outside hypothesis proves q>R for a genuine Dirichlet approximant.
Q_D=ceil(B/R) is kept distinct from the kernel cutoff floor(R^2). -/
theorem auxiliary_minor_has_approximant (B R : ℝ) (hR : 1<R) (hBR : R≤B)
    (x : UnitAddCircle) (hx : x ∉ auxiliaryMajor B R) :
    ∃ i : ReducedRationalIndex ⌈B/R⌉₊,
      R<(i.val.1 : ℝ) ∧ (i.val.1 : ℝ)≤2*B/R ∧
      dist x (majorArcCenter i)≤1/(i.val.1 : ℝ)^2 := by
  have hr : 0<R := lt_trans zero_lt_one hR
  have hb : 0<B := hr.trans_le hBR
  have hd := auxiliary_dirichlet_denominator_bounds B R hr hBR
  obtain ⟨i,hi⟩ := exists_reduced_approximant_reciprocal_radius ⌈B/R⌉₊ hd.1 x
  have hq : (0 : ℝ) < i.val.1 := by exact_mod_cast index_denominator_pos i
  have hq1 : (1 : ℝ) ≤ i.val.1 := by exact_mod_cast index_denominator_pos i
  have hqQ : (i.val.1 : ℝ)≤⌈B/R⌉₊ := by
    exact_mod_cast center_denominator_le ⌈B/R⌉₊ i
  have hlow : R<(i.val.1 : ℝ) := by
    by_contra hn
    have hqr : (i.val.1 : ℝ)≤R := le_of_not_gt hn
    have hk : i.val.1≤⌊R^2⌋₊ := by
      apply (Nat.le_floor_iff (sq_nonneg R)).mpr
      nlinarith
    have hdist : dist x (majorArcCenter i)≤R/B := by
      apply hi.trans
      calc
        _ ≤ 1/(B/R) := by
          apply one_div_le_one_div_of_le (by positivity)
          have hqd : 0≤(⌈B/R⌉₊ : ℝ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hq1 hqd]
        _ = R/B := by field_simp
    apply hx
    exact ⟨reindexCenter i hk,hqr,by simpa only [reindex_center_value] using hdist⟩
  refine ⟨i,hlow,hqQ.trans hd.2.2,?_⟩
  apply hi.trans
  exact one_div_le_one_div_of_le (sq_pos_of_pos hq) (by nlinarith)

theorem vaughan_prefix_to_block_envelope (M B q : ℕ) (hM : 3≤M) (hMB : M≤B)
    (R C : ℝ) (hR : 0<R) (hC : 0≤C)
    (hlow : R≤(q : ℝ)) (hhigh : (q : ℝ)≤2*(B : ℝ)/R) :
    vaughanEnvelope M q C ≤ C*(Real.log (B : ℝ))^4 *
      ((B : ℝ)/Real.sqrt R+(B : ℝ)^((4 : ℝ)/5)+Real.sqrt (2*(B : ℝ)^2/R)) := by
  have hm : (0 : ℝ)<M := by exact_mod_cast (by omega : 0<M)
  have hb : (0 : ℝ)<B := by exact_mod_cast (by omega : 0<B)
  have hmb : (M : ℝ)≤B := by exact_mod_cast hMB
  have hq : (0 : ℝ)<q := hR.trans_le hlow
  have hlog : 0≤Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤M))
  have hlogmono := Real.log_le_log hm hmb
  have ht1 : (M : ℝ)/Real.sqrt (q : ℝ)≤(B : ℝ)/Real.sqrt R := by gcongr
  have ht2 : (M : ℝ)^((4 : ℝ)/5)≤(B : ℝ)^((4 : ℝ)/5) := by gcongr
  have ht3 : Real.sqrt ((M : ℝ)*(q : ℝ))≤Real.sqrt (2*(B : ℝ)^2/R) := by
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ (B : ℝ)*(2*(B : ℝ)/R) := mul_le_mul hmb hhigh hq.le hb.le
      _ = _ := by ring
  unfold vaughanEnvelope
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hlogmono 4) hC)
    (add_le_add (add_le_add ht1 ht2) ht3) (by positivity) (by positivity)

/-- Conditional only: hV is the existing source-shaped analytic premise,
not a fabricated instance or additional global postulate. -/
theorem actual_block_auxiliary_minor_bound (B : ℕ) (hB : 6≤B)
    (R C : ℝ) (hR : 1<R) (hBR : R≤(B : ℝ)) (hC : 0≤C)
    (hV : RealVaughanEstimate C) (x : UnitAddCircle)
    (hx : x ∉ auxiliaryMajor (B : ℝ) R) :
    ‖blockFourier B x‖≤2*C*(Real.log (B : ℝ))^4 *
      ((B : ℝ)/Real.sqrt R+(B : ℝ)^((4 : ℝ)/5)+Real.sqrt (2*(B : ℝ)^2/R)) := by
  obtain ⟨i,hl,hh,hd⟩ := auxiliary_minor_has_approximant (B : ℝ) R hR hBR x hx
  have h1 := circle_estimate_of_real C hV B ⌈(B : ℝ)/R⌉₊ (by omega) i x hd
  have h2 := circle_estimate_of_real C hV (B/2) ⌈(B : ℝ)/R⌉₊ (by omega) i x hd
  have hb1 := h1.trans (vaughan_prefix_to_block_envelope B B i.val.1 (by omega)
    le_rfl R C (by linarith) hC hl.le hh)
  have hb2 := h2.trans (vaughan_prefix_to_block_envelope (B/2) B i.val.1 (by omega)
    (Nat.div_le_self B 2) R C (by linarith) hC hl.le hh)
  rw [block_fourier_prefix_difference]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Actual restricted convolution, with the same input, output block and
signed kernel as V119/V130. This is a name for that expression, not a new model. -/
noncomputable def windowFourier (B : ℕ) (R : ℝ) (G : ℝ → ℝ)
    (x : UnitAddCircle) : ℂ :=
  ∑ n ∈ blockCarrier B,
    GoldbachCircleMethodFiniteWindowConvolutionV18119.normalizedWindowConvolution
      ⌊R^2⌋₊ n ((B : ℝ)/R^4) (blockCarrier B) (blockInput B) (logWeight R G) *
        fourier (n : ℤ) x

/-- On the auxiliary-major region, even the elementary B log B input
bound suffices. No external Chebyshev premise is imported. -/
theorem actual_major_input_product_bound (B : ℕ) (hB : 2≤B)
    (R : ℝ) (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ)))≤R)
    (hupper : R≤(B : ℝ)^((1 : ℝ)/10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (hplateau : ∀ u : ℝ, 0≤u → u≤1 → G u=1)
    (x : UnitAddCircle) (hx : x ∈ auxiliaryMajor (B : ℝ) R) :
    ‖blockFourier B x‖ * ‖1-logWindowMultiplier (B : ℝ) R G x‖ ≤
      9*((1+M)/2+3*Real.pi)*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  have hb : (2 : ℝ)≤B := by exact_mod_cast hB
  have hr2 := lower_range_two_le (B : ℝ) R hb hlower
  have hr : 1<R := by linarith
  have hlog : 0≤Real.log (B : ℝ) := Real.log_nonneg (by linarith)
  obtain ⟨i,hiq,hix⟩ := hx
  have hmult := actual_log_multiplier_major_existing_range (B : ℝ) R hb hr2
    hupper G M hM hG hplateau x i hiq hix
  have hprod := mul_le_mul (block_fourier_norm_le B (by omega) x)
    hmult (norm_nonneg _) (show 0≤(B : ℝ)*Real.log (B : ℝ) by positivity)
  rw [norm_sub_rev] at hprod
  apply hprod.trans
  have hpower : R≤R^3 := by
    simpa using pow_le_pow_right₀ hr.le (by norm_num : 1≤3)
  have hratio : Real.log (B : ℝ)/R^3≤9*R^(-(1 : ℝ)/3) :=
    (div_le_div_of_nonneg_left hlog (by linarith : 0<R) hpower).trans
      (log_absorption_from_lower_scale (B : ℝ) R (by linarith) hr hlower)
  calc
    _ = (((1+M)/2+3*Real.pi)*(B : ℝ))*(Real.log (B : ℝ)/R^3) := by ring
    _ ≤ (((1+M)/2+3*Real.pi)*(B : ℝ))*(9*R^(-(1 : ℝ)/3)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

/-- Actual output restriction is retained and paid for; no tail is dropped. -/
theorem actual_window_major_error_bound (B : ℕ) (hB : 2≤B)
    (R : ℝ) (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ)))≤R)
    (hupper : R≤(B : ℝ)^((1 : ℝ)/10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (hplateau : ∀ u : ℝ, 0≤u → u≤1 → G u=1)
    (x : UnitAddCircle) (hx : x ∈ auxiliaryMajor (B : ℝ) R) :
    ‖blockFourier B x-windowFourier B R G x‖ ≤
      (9*((1+M)/2+3*Real.pi)+36*M)*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  have hb : (2 : ℝ)≤B := by exact_mod_cast hB
  have hr : 1<R := by linarith [lower_range_two_le (B : ℝ) R hb hlower]
  have he := actual_window_fourier_error_le B hB R hr G M hM hG hupper hlower x
  change ‖blockFourier B x-windowFourier B R G x‖≤
    ‖blockFourier B x‖ * ‖1-logWindowMultiplier (B : ℝ) R G x‖+
      36*M*(B : ℝ)*R^(-(1 : ℝ)/3) at he
  have hp := actual_major_input_product_bound B hB R hlower hupper
    G M hM hG hplateau x hx
  exact he.trans (by nlinarith)

/-- Minor-region composition remains explicitly conditional on the source
Vaughan estimate; the unabsorbed bound is recorded without an invented o(B). -/
theorem actual_window_auxiliary_minor_error_bound (B : ℕ) (hB : 6≤B)
    (R C : ℝ) (hBR : R≤(B : ℝ))
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ)))≤R)
    (hupper : R≤(B : ℝ)^((1 : ℝ)/10000))
    (hC : 0≤C) (hV : RealVaughanEstimate C)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (x : UnitAddCircle) (hx : x ∉ auxiliaryMajor (B : ℝ) R) :
    ‖blockFourier B x-windowFourier B R G x‖ ≤
      (2*C*(Real.log (B : ℝ))^4 *
        ((B : ℝ)/Real.sqrt R+(B : ℝ)^((4 : ℝ)/5)+Real.sqrt (2*(B : ℝ)^2/R))) *
        (1+2*M) + 36*M*(B : ℝ)*R^(-(1 : ℝ)/3) := by
  have hb : (2 : ℝ)≤B := by exact_mod_cast (by omega : 2≤B)
  have hr : 1<R := by linarith [lower_range_two_le (B : ℝ) R hb hlower]
  have ha := actual_block_auxiliary_minor_bound B hB R C hr hBR hC hV x hx
  have hm := actual_log_multiplier_full_range (B : ℝ) R hb hlower hupper G M hM hG x
  have hm1 : ‖1-logWindowMultiplier (B : ℝ) R G x‖≤1+2*M :=
    (norm_sub_le _ _).trans (by simpa using add_le_add_left hm 1)
  have hp := mul_le_mul ha hm1 (norm_nonneg _) (by positivity)
  have he := actual_window_fourier_error_le B (by omega) R hr G M hM hG hupper hlower x
  change ‖blockFourier B x-windowFourier B R G x‖≤
    ‖blockFourier B x‖ * ‖1-logWindowMultiplier (B : ℝ) R G x‖+
      36*M*(B : ℝ)*R^(-(1 : ℝ)/3) at he
  exact he.trans (add_le_add hp le_rfl)

end GoldbachCircleMethodActualBlockAuxiliaryMinorV18136
