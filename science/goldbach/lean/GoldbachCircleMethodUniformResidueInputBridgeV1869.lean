import GoldbachCircleMethodGeneralCoprimeCharacterV1868

/-! # V1.8.69: uniform reduced-class inputs on the original prefix carrier.
The distribution input remains explicit. Small prefixes have a proved trivial bound.
-/
open scoped BigOperators
open Filter Topology
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformMajorPrefixReductionV1865
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodFiniteAbelAdapterV1863
open GoldbachCircleMethodActualOperatorErrorTransferV1861
open GoldbachPrimePowerDefectBoundV161

namespace GoldbachCircleMethodUniformResidueInputBridgeV1869

def UniformReducedClassBound (K M : ℕ) (B : ℝ) : Prop :=
  ∀ q : ℕ, ∀ hq : 0 < q, q ≤ logRadius K M →
    ∀ r : ZMod q, IsUnit r → ∀ k ≤ M,
      |@psiResidue k q ⟨Nat.ne_of_gt hq⟩ r-(k : ℝ)/(Nat.totient q : ℝ)| ≤ B

theorem fullPrefixBound_of_uniform_classes_and_budget (K M : ℕ) (B C c : ℝ)
    (hB : 0 ≤ B) (hclasses : UniformReducedClassBound K M B)
    (hbudget : (logRadius K M : ℝ)*B+
      ((logRadius K M : ℝ)+1+2*Real.sqrt (M : ℝ))*Real.log (M : ℝ) ≤ prefixEnvelope M C c) :
    FullPrefixBound K M C c := by
  intro i k hkM
  have hq := index_denominator_pos i
  have hd := (Finset.mem_filter.mp i.property)
  have hqr : i.val.1 ≤ logRadius K M :=
    (Finset.mem_Icc.mp (Finset.mem_product.mp hd.1).1).2
  let _ : NeZero i.val.1 := ⟨Nat.ne_of_gt hq⟩
  have ha : IsUnit (i.val.2 : ZMod i.val.1) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hd.2.2
  have h := rational_prefix_error_moebius M k i.val.1 (i.val.2 : ZMod i.val.1)
    ha hkM B hB (fun r hr => hclasses i.val.1 hq hqr r hr k hkM)
  have hv : (i.val.2 : ZMod i.val.1).val=i.val.2 := ZMod.val_natCast_of_lt hd.2.1
  simp only [hv] at h
  change ‖exponentialSum k.succ
    (((i.val.2 : ℝ)/(i.val.1 : ℝ) : ℝ) : UnitAddCircle)-
      ((((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ))*(k : ℂ))‖ ≤ _
  apply h.trans (le_trans _ hbudget)
  have hqr' : (i.val.1 : ℝ) ≤ logRadius K M := by exact_mod_cast hqr
  exact add_le_add (mul_le_mul_of_nonneg_right hqr' hB)
    (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg M))

theorem exponentialSum_norm_le_prefix_log (M k : ℕ) (hkM : k ≤ M) (x : UnitAddCircle) :
    ‖exponentialSum k.succ x‖ ≤ (k : ℝ)*Real.log (M : ℝ) := by
  rw [exponentialSum_eq_shifted_sum]
  calc
    _ ≤ ∑ n ∈ Finset.range k,
        ‖(ArithmeticFunction.vonMangoldt (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range k, Real.log (M : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact vonMangoldt_le_log_nat_of_le (by have := Finset.mem_range.mp hn; omega)
    _ = _ := by simp

theorem rational_prefix_trivial_bound (M k q : ℕ) (hq : 0 < q) (hkM : k ≤ M)
    (x : UnitAddCircle) :
    ‖exponentialSum k.succ x-
      ((((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ))*(k : ℂ))‖ ≤
        (k : ℝ)*(Real.log (M : ℝ)+1) := by
  have hm : ‖(((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ))*(k : ℂ)‖ ≤ k := by
    rw [norm_mul, Complex.norm_natCast]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (rational_amplitude_norm_le_one q hq) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  calc
    _ ≤ (k : ℝ)*Real.log (M : ℝ)+(k : ℝ) :=
      (norm_sub_le _ _).trans (add_le_add (exponentialSum_norm_le_prefix_log M k hkM x) hm)
    _ = _ := by ring

theorem small_prefix_error_bound (M k q : ℕ) (hq : 0 < q) (hkM : k ≤ M)
    (hsmall : (k : ℝ) ≤ Real.sqrt (M : ℝ)) (x : UnitAddCircle) :
    ‖exponentialSum k.succ x-
      ((((ArithmeticFunction.moebius q : ℤ) : ℂ)/(Nat.totient q : ℂ))*(k : ℂ))‖ ≤
        Real.sqrt (M : ℝ)*(Real.log (M : ℝ)+1) :=
  (rational_prefix_trivial_bound M k q hq hkM x).trans
    (mul_le_mul_of_nonneg_right hsmall (by positivity))

theorem large_prefix_log_lower_bound (M k : ℕ) (hM : 0 < M)
    (hlarge : Real.sqrt (M : ℝ) ≤ k) :
    Real.log (M : ℝ)/2 ≤ Real.log (k : ℝ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have h := Real.log_le_log (Real.sqrt_pos.mpr hm) hlarge
  simpa only [Real.log_sqrt hm.le] using h

theorem doubled_power_le_half_power (K : ℕ) (x : ℝ)
    (hx : (2 : ℝ)^(K+2) ≤ x) :
    2*x^K ≤ (x/2)^(K+1) := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  rw [div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < 2^(K+1))]
  have h := mul_le_mul_of_nonneg_left hx (pow_nonneg hx0 K)
  calc
    2*x^K*2^(K+1) = x^K*2^(K+2) := by rw [pow_succ (2 : ℝ) (K+1)]; ring
    _ ≤ x^K*x := h
    _ = x^(K+1) := (pow_succ x K).symm

theorem large_prefix_modulus_bound (K M k : ℕ) (hM : 0 < M)
    (hlog : (2 : ℝ)^(K+2) ≤ Real.log (M : ℝ))
    (hlarge : Real.sqrt (M : ℝ) ≤ k) :
    (logRadius K M : ℝ) ≤ (Real.log (k : ℝ))^(K+1) := by
  have hlog1 : 1 ≤ Real.log (M : ℝ) :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hlog
  have h := (ceil_power_bounds _ hlog1 K).2
  change (logRadius K M : ℝ) ≤ 2*(Real.log (M : ℝ))^K at h
  refine (h.trans (doubled_power_le_half_power K _ hlog)).trans ?_
  exact pow_le_pow_left₀ (by positivity) (large_prefix_log_lower_bound M k hM hlarge) _

theorem large_prefix_sqrt_log_lower_bound (M k : ℕ) (hM : 0 < M)
    (hlarge : Real.sqrt (M : ℝ) ≤ k) :
    Real.sqrt (Real.log (M : ℝ))/2 ≤ Real.sqrt (Real.log (k : ℝ)) := by
  have hlog := large_prefix_log_lower_bound M k hM hlarge
  have hMlog := Real.log_natCast_nonneg M
  have hklog := Real.log_natCast_nonneg k
  have hsM := Real.sq_sqrt hMlog
  have hsk := Real.sq_sqrt hklog
  nlinarith [Real.sqrt_nonneg (Real.log (M : ℝ)), Real.sqrt_nonneg (Real.log (k : ℝ))]

theorem large_prefix_rate_transfer (M k : ℕ) (hM : 0 < M) (hkM : k ≤ M)
    (hlarge : Real.sqrt (M : ℝ) ≤ k) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c) :
    C*(k : ℝ)*Real.exp (-c*Real.sqrt (Real.log (k : ℝ))) ≤
      C*(M : ℝ)*Real.exp (-(c/2)*Real.sqrt (Real.log (M : ℝ))) := by
  have hs := large_prefix_sqrt_log_lower_bound M k hM hlarge
  have he : -c*Real.sqrt (Real.log (k : ℝ)) ≤
      -(c/2)*Real.sqrt (Real.log (M : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hs hc]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (by exact_mod_cast hkM) hC)
    (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)

def LargePrefixClassBound (K M : ℕ) (B : ℝ) : Prop :=
  ∀ q : ℕ, ∀ hq : 0 < q, q ≤ logRadius K M →
    ∀ r : ZMod q, IsUnit r → ∀ k ≤ M, Real.sqrt (M : ℝ) ≤ k →
      |@psiResidue k q ⟨Nat.ne_of_gt hq⟩ r-(k : ℝ)/(Nat.totient q : ℝ)| ≤ B

/-- An unproved external distribution input, with its own evaluation-scale domain. -/
def ScaleReducedClassEstimate (D k₀ : ℕ) (C c : ℝ) : Prop :=
  ∀ k ≥ k₀, ∀ q : ℕ, ∀ hq : 0 < q, (q : ℝ) ≤ (Real.log (k : ℝ))^D →
    ∀ r : ZMod q, IsUnit r →
      |@psiResidue k q ⟨Nat.ne_of_gt hq⟩ r-(k : ℝ)/(Nat.totient q : ℝ)| ≤
        prefixEnvelope k C c

theorem large_classes_from_scale_estimate (K M k₀ : ℕ) (C c : ℝ)
    (hM : 0 < M) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hlog : (2 : ℝ)^(K+2) ≤ Real.log (M : ℝ))
    (hstart : (k₀ : ℝ) ≤ Real.sqrt (M : ℝ))
    (hscale : ScaleReducedClassEstimate (K+1) k₀ C c) :
    LargePrefixClassBound K M (prefixEnvelope M C (c/2)) := by
  intro q hq hqr r hr k hkM hlarge
  have hstart' : k₀ ≤ k := by exact_mod_cast hstart.trans hlarge
  have hqlog : (q : ℝ) ≤ (Real.log (k : ℝ))^(K+1) :=
    (by exact_mod_cast hqr : (q : ℝ) ≤ logRadius K M).trans
      (large_prefix_modulus_bound K M k hM hlog hlarge)
  exact (hscale k hstart' q hq hqlog r hr).trans
    (large_prefix_rate_transfer M k hM hkM hlarge C c hC hc)

theorem fullPrefixBound_of_large_classes_and_budgets (K M : ℕ) (B C c : ℝ)
    (hB : 0 ≤ B) (hclasses : LargePrefixClassBound K M B)
    (hsmall : Real.sqrt (M : ℝ)*(Real.log (M : ℝ)+1) ≤ prefixEnvelope M C c)
    (hbudget : (logRadius K M : ℝ)*B+
      ((logRadius K M : ℝ)+1+2*Real.sqrt (M : ℝ))*Real.log (M : ℝ) ≤ prefixEnvelope M C c) :
    FullPrefixBound K M C c := by
  intro i k hkM
  have hq := index_denominator_pos i
  by_cases hlarge : Real.sqrt (M : ℝ) ≤ k
  · have hd := Finset.mem_filter.mp i.property
    have hqr : i.val.1 ≤ logRadius K M :=
      (Finset.mem_Icc.mp (Finset.mem_product.mp hd.1).1).2
    let _ : NeZero i.val.1 := ⟨Nat.ne_of_gt hq⟩
    have ha : IsUnit (i.val.2 : ZMod i.val.1) :=
      (ZMod.isUnit_iff_coprime _ _).mpr hd.2.2
    have h := rational_prefix_error_moebius M k i.val.1 (i.val.2 : ZMod i.val.1)
      ha hkM B hB (fun r hr => hclasses i.val.1 hq hqr r hr k hkM hlarge)
    have hv : (i.val.2 : ZMod i.val.1).val=i.val.2 := ZMod.val_natCast_of_lt hd.2.1
    simp only [hv] at h
    change ‖exponentialSum k.succ
      (((i.val.2 : ℝ)/(i.val.1 : ℝ) : ℝ) : UnitAddCircle)-
        ((((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ))*(k : ℂ))‖ ≤ _
    apply h.trans (le_trans _ hbudget)
    have hqr' : (i.val.1 : ℝ) ≤ logRadius K M := by exact_mod_cast hqr
    exact add_le_add (mul_le_mul_of_nonneg_right hqr' hB)
      (mul_le_mul_of_nonneg_right (by linarith) (Real.log_natCast_nonneg M))
  · exact (small_prefix_error_bound M k i.val.1 hq hkM (le_of_not_ge hlarge)
      (majorArcCenter i)).trans hsmall

theorem fullPrefixBound_of_scale_estimate_and_budgets (K M k₀ : ℕ)
    (C c C' c' : ℝ) (hM : 0 < M) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hlog : (2 : ℝ)^(K+2) ≤ Real.log (M : ℝ))
    (hstart : (k₀ : ℝ) ≤ Real.sqrt (M : ℝ))
    (hscale : ScaleReducedClassEstimate (K+1) k₀ C c)
    (hsmall : Real.sqrt (M : ℝ)*(Real.log (M : ℝ)+1) ≤ prefixEnvelope M C' c')
    (hbudget : (logRadius K M : ℝ)*prefixEnvelope M C (c/2)+
      ((logRadius K M : ℝ)+1+2*Real.sqrt (M : ℝ))*Real.log (M : ℝ) ≤ prefixEnvelope M C' c') :
    FullPrefixBound K M C' c' :=
  fullPrefixBound_of_large_classes_and_budgets K M _ C' c' (by unfold prefixEnvelope; positivity)
    (large_classes_from_scale_estimate K M k₀ C c hM hC hc hlog hstart hscale) hsmall hbudget

end GoldbachCircleMethodUniformResidueInputBridgeV1869
